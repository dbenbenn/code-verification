/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import LibsignalBinary.Heap.MuslMemOpsRunsTo
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import ProofLib.SepLogic.HeapIntro

/-!
# Coupled `memcpy` / `compress256` Block-Segment `VmPreserved` & `AllocCallPreserved` Lifting

Provides `coupledMemcpy` and `coupledCompress256` together with `hmacCompressOnlyExcHooksSat` and
`hmacNoMemsetExcHooksSat`, lifting multi-instruction `RunsTo` segments on placed blocks that call
`lsMemcpySym` (`HookSatExactMemcpy`) and/or `lsCompress256Sym` (`HookSatCompress256`) to
`Steps` + `VmPreserved` + `AllocCallPreserved` without concrete hook equalities or splitting
segments at `compress256` call sites.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.CoupledCompress256Sat

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HMAC (ShaState chunks64)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement libsignalSessionLib lsmpl
)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  RunsTo lsCompress256Sym lsMemcpySym
)
open CryptoVerification.LibsignalTripleRatchet (
  readBytes_4_eq shaStateBytes_eq_append shaStateBytes_length
)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open VerifiedLibraries.RustStd (blockProgram_rebase_allInstrs_not_isSvc0)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat (
  blockProgram_allInstrs_not_isMsrTpidrEl0 checkBlockNoMsrTpidrEl0
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookExactMemcpy HookSatExactMemcpy applyMemcpyClobber_ofState_eq
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (
  HookOkCompress256 HookSatCompress256 KeepsExec
  compress256Hook_keepsExec compress256Hook_roBudget_ok
  hookOk_withLsRet624 hookOk_withLsRet624_sessionCompress256ROBudget_elim
  vmPreserved_applyMemcpyClobber_writeBytes withLsRet624
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  compress256Blocks sessionCompress256ROBudgetSpec sessionCompress256ROSpec
)

/-! ## 1. `execInst` Oracle & `AllocCallPreserved` Helpers -/

theorem allocCallPreserved_refl (s : State) : AllocCallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem allocCallPreserved_trans {s1 s2 s3 : State}
    (h1 : AllocCallPreserved s1 s2) (h2 : AllocCallPreserved s2 s3) :
    AllocCallPreserved s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

private def projOracle (s : State) := s.oracle
private theorem projOracle_adv (s : State) : projOracle s.advancePC = projOracle s := by
  cases s; rfl
private theorem projOracle_pc (s : State) (p : BitVec 64) :
    projOracle (s.setPC p) = projOracle s := by cases s; rfl
private theorem projOracle_w64 (s : State) (r : Reg) (v : BitVec 64) :
    projOracle (s.writeReg64 r v) = projOracle s := by cases s; cases r <;> rfl
private theorem projOracle_w32 (s : State) (r : Reg) (v : BitVec 32) :
    projOracle (s.writeReg32 r v) = projOracle s := projOracle_w64 s r _
private theorem projOracle_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    projOracle (s.writeReg w r v) = projOracle s := projOracle_w64 s r _
private theorem projOracle_v128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    projOracle (s.writeVReg128 r v) = projOracle s := by cases s; rfl
private theorem projOracle_v64 (s : State) (r : BitVec 5) (v : BitVec 64) :
    projOracle (s.writeVReg64 r v) = projOracle s := projOracle_v128 s r _
private theorem projOracle_v32 (s : State) (r : BitVec 5) (v : BitVec 32) :
    projOracle (s.writeVReg32 r v) = projOracle s := projOracle_v128 s r _
private theorem projOracle_ps (s : State) (p : PState) :
    projOracle (s.setPState p) = projOracle s := by cases s; rfl
private theorem projOracle_fp (s : State) (f : BitVec 32) :
    projOracle (s.setFpsr f) = projOracle s := by cases s; rfl
private theorem projOracle_ofp (s : State) (f : BitVec 32) :
    projOracle (s.orFpsr f) = projOracle s := by cases s; rfl
private theorem projOracle_st (s : State) (st : ExecStatus) :
    projOracle (s.setStatus st) = projOracle s := by cases s; rfl
private theorem projOracle_wst (s : State) (st : ExecStatus) :
    projOracle { s with status := st } = projOracle s := by cases s; rfl
private theorem projOracle_mem (s : State) (m : Memory) :
    projOracle (s.setMem m) = projOracle s := by cases s; rfl
private theorem projOracle_tp (s : State) (v : BitVec 64) :
    projOracle (setTpidrEl0 s v) = projOracle s := by cases s; rfl
private theorem projOracle_ex (s : State) :
    projOracle s.stepExclOracle = projOracle s := by cases s; rfl
private theorem projOracle_as (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    projOracle (applySimdResult s rd r) = projOracle s := by cases s; cases r <;> rfl
private theorem projOracle_ass (s : State) (rd : BitVec 5) (r : Except String (BitVec 128))
    (sat : Option (BitVec 32)) :
    projOracle (applySimdSatResult s rd r sat) = projOracle s := by
  cases s; cases r <;> cases sat <;> rfl
private theorem projOracle_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      projOracle (simdLoadRegs sz m n vt ea s) = projOracle s
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => (projOracle_slr sz m n _ _ _).trans (projOracle_v128 s _ _)

private theorem execInst_projOracle_of_not_isSvc0 {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).oracle = s.oracle := by
  change projOracle (execInst inst s) = projOracle s
  cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc]; simp [himm, projOracle_st]
    · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, projOracle_st]
  case simdThreeSame q u size rm opcode rn rd =>
    dsimp only [execInst, execInstWithSvc]
    by_cases hop : opcode == 0b00011#5
    · simp only [hop, ↓reduceIte]
      rcases size with ⟨_ | _ | _ | _ | _, _⟩ <;> try omega
      all_goals (cases u <;> first
        | exact (projOracle_adv _).trans (projOracle_v128 _ _ _)
        | exact projOracle_ass _ _ _ _)
    · simp only [hop, Bool.false_eq_true, ↓reduceIte, projOracle_adv, projOracle_v128,
        projOracle_ass, apply_ite projOracle, ite_self]
  case ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp [projOracle_adv, projOracle_mem, projOracle_v128, projOracle_w64, projOracle_st,
        apply_ite projOracle]
  case ldr | ldrLit | str | ldp | stp | ldnp | stnp | addSubImm | logicalImm | moveWide | bitfield
     | logicalShift | addSubShift | addSubExt | addSubCarry | condCompareReg | condCompareImm
     | condSelect | dataProc1 | dataProc2 | dataProc3 =>
    cases s; dsimp only [execInst, execInstWithSvc, execLdr, execLdrLit, execStr, execLdp, execStp,
      execAddSubImm, execLogicalImm, execMoveWide, execBitfield, execLogicalShift, execAddSubShift,
      execAddSubExt, execAddSubCarry, execCondCompare, execCondSelect, execDataProc1, execDataProc2,
      execDataProc3]; (repeat' split) <;> rfl
  all_goals
    dsimp only [execInst, execInstWithSvc]
    simp only [projOracle_adv, projOracle_pc, projOracle_w64, projOracle_w32, projOracle_w,
      projOracle_v128, projOracle_v64, projOracle_v32, projOracle_ps, projOracle_fp,
      projOracle_ofp, projOracle_st, projOracle_wst, projOracle_mem,
      projOracle_ex, projOracle_as, projOracle_ass, projOracle_slr,
      apply_ite projOracle, ite_self]
    try (cases s; (repeat' split) <;> rfl)

/-! ## 2. `restorePerm` & `stripExecOutside` Commutation -/

@[expose] def restorePerm (m₀ m : Memory) : Memory :=
  ⟨fun a => match m.cells a, m₀.perm a with
    | some (some p, b), some p₀ =>
        some (some { p with r := p₀.r, w := p₀.w, x := p₀.x }, b)
    | other, _ => other⟩

private theorem restorePerm_isLazyFree (m₀ m : Memory) (a : BitVec 64) :
    (restorePerm m₀ m).isLazyFree a = m.isLazyFree a := by
  dsimp only [restorePerm, Memory.isLazyFree]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · cases m₀.perm a <;> rfl

private theorem restorePerm_read8 (m₀ m : Memory) (a : BitVec 64) :
    (restorePerm m₀ m).read8 a = m.read8 a := by
  dsimp only [restorePerm, Memory.read8]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · cases m₀.perm a <;> rfl

private theorem restorePerm_readBytes (m₀ m : Memory) (a : BitVec 64) (n : Nat) :
    (restorePerm m₀ m).readBytes a n = m.readBytes a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact congrArg₂ List.cons (restorePerm_read8 m₀ m a) (ih (a + 1#64))

private theorem stripExecOutside_readBytes (kp : BitVec 64 → Bool) (m : Memory)
    (a : BitVec 64) (n : Nat) :
    (ProofLib.stripExecOutside kp m).readBytes a n = m.readBytes a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact congrArg₂ List.cons (ProofLib.strip_read8 kp m a) (ih (a + 1#64))

private theorem stripExecOutside_writeBytes_vm (p : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (bs : List (BitVec 8)),
      (ProofLib.stripExecOutside p m).writeBytes a bs =
        ProofLib.stripExecOutside p (m.writeBytes a bs)
  | _, [] => rfl
  | a, b :: bs => by
    simp only [Memory.writeBytes, ProofLib.strip_write8,
      stripExecOutside_writeBytes_vm p (m.write8 a b) (a + 1#64) bs]

private theorem restorePerm_perm {m₀ m : Memory} {kp : BitVec 64 → Bool}
    (hperm : ∀ a, m.perm a = (ProofLib.stripExecOutside kp m₀).perm a) (a : BitVec 64) :
    (restorePerm m₀ m).perm a = m₀.perm a := by
  have ha := (hperm a).trans (ProofLib.strip_perm kp m₀ a)
  show (match (restorePerm m₀ m).cells a with
    | some (some p, _) => some p.rwx | _ => none) = m₀.perm a
  dsimp only [restorePerm]
  rcases hc : m.cells a with _ | ⟨_ | p, b⟩
  · have hm : m.perm a = none := by simp [Memory.perm, hc]
    rw [hm] at ha; cases hm₀ : m₀.perm a <;> simp [hm₀] at ha ⊢
  · have hm : m.perm a = none := by simp [Memory.perm, hc]
    rw [hm] at ha; cases hm₀ : m₀.perm a <;> simp [hm₀] at ha ⊢
  · have hm : m.perm a = some p.rwx := by simp [Memory.perm, hc]
    rw [hm] at ha
    cases hm₀ : m₀.perm a with
    | none => simp [hm₀] at ha
    | some p₀ =>
      unfold Memory.perm at hm₀
      rcases hc₀ : m₀.cells a with _ | ⟨_ | q₀, _⟩ <;> simp [hc₀] at hm₀
      subst hm₀; rfl

private theorem restorePerm_readable {m₀ m : Memory} {kp : BitVec 64 → Bool}
    (hperm : ∀ a, m.perm a = (ProofLib.stripExecOutside kp m₀).perm a)
    {a : BitVec 64} {n : Nat} (h : m.Readable a n) :
    (restorePerm m₀ m).Readable a n := by
  intro x hx
  obtain ⟨hr, hnl⟩ := h x hx
  rw [restorePerm_perm hperm x, restorePerm_isLazyFree]
  rw [hperm x, (ProofLib.strip_perm_props kp m₀ x).1] at hr
  exact ⟨hr, hnl⟩

private theorem restorePerm_rw {m₀ m : Memory} {kp : BitVec 64 → Bool}
    (hperm : ∀ a, m.perm a = (ProofLib.stripExecOutside kp m₀).perm a)
    {a : BitVec 64} {n : Nat} (h : Memory.RW m a n) :
    Memory.RW (restorePerm m₀ m) a n := fun x hx => by
  rw [Memory.permNoLazy_eq_some_rw_iff]
  have ⟨hrw, hnl⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx)
  rw [restorePerm_perm hperm x, restorePerm_isLazyFree]
  rw [hperm x, (ProofLib.strip_perm_props kp m₀ x).2.2.2] at hrw
  exact ⟨hrw, hnl⟩

private theorem stripExecOutside_restorePerm {m₀ m : Memory} {kp : BitVec 64 → Bool}
    (hperm : ∀ a, m.perm a = (ProofLib.stripExecOutside kp m₀).perm a) :
    ProofLib.stripExecOutside kp (restorePerm m₀ m) = m := by
  ext a
  have ha := (hperm a).trans (ProofLib.strip_perm kp m₀ a)
  dsimp only [ProofLib.stripExecOutside, restorePerm]
  rcases hc : m.cells a with _ | ⟨_ | p, b⟩
  · rfl
  · rfl
  · have hm : m.perm a = some p.rwx := by simp [Memory.perm, hc]
    rw [hm] at ha
    cases hm₀ : m₀.perm a with
    | none => simp [hm₀] at ha
    | some p₀ =>
      simp only [hm₀, Option.map_some, Option.some.injEq] at ha
      rcases p with ⟨r, w, x, lf, an⟩
      rcases p₀ with ⟨r₀, w₀, x₀, lf₀, an₀⟩
      cases hkp : kp a <;> cases x₀ <;>
        simp_all [ProofLib.stripPerm, Perm.rwx]

private theorem restorePerm_stripExecOutside_self {m₀ m₁ : Memory} (kp : BitVec 64 → Bool)
    (hperm : ∀ a, m₁.perm a = m₀.perm a) :
    restorePerm m₀ (ProofLib.stripExecOutside kp m₁) = m₁ := by
  ext a
  have ha := (hperm a).symm
  dsimp only [restorePerm, ProofLib.stripExecOutside]
  rcases hc₁ : m₁.cells a with _ | ⟨_ | p, b⟩
  · rfl
  · rfl
  · have hp₁ : m₁.perm a = some p.rwx := by simp [Memory.perm, hc₁]
    rw [ha, hp₁]
    rcases p with ⟨r, w, x, lf, an⟩
    cases kp a <;> cases x <;> rfl

/-! ## 3. Coupled `memcpy` (`coupledMemcpy`) -/

@[expose] def MemcpyPre (u : State) : Prop :=
  u.status = .Running ∧
  u.spAligned = true ∧
  u.mem.RW (u.readReg64 .x0) (u.readReg64 .x2).toNat ∧
  u.mem.Readable (u.readReg64 .x1) (u.readReg64 .x2).toNat ∧
  ((u.readReg64 .x2).toNat = 0 ∨
    DisjointRegions (u.readReg64 .x0) (u.readReg64 .x2).toNat
      (u.readReg64 .x1) (u.readReg64 .x2).toNat)

/-- Constructively decides `∀ a : BitVec 64, P a` over the finite `2 ^ 64` address space.
Note: enumerates up to `2 ^ 64` addresses, so it is intended for specification decidability rather
than practical `#eval` execution when no early counterexample exists. -/
@[expose] def decForallBV64 (P : BitVec 64 → Prop) [DecidablePred P] :
    Decidable (∀ a : BitVec 64, P a) :=
  decidable_of_iff (∀ i < 2 ^ 64, P (BitVec.ofNat 64 i))
    ⟨fun h a => by simpa [BitVec.ofNat_toNat] using h a.toNat a.isLt,
     fun h i _ => h (BitVec.ofNat 64 i)⟩

local instance instDecidableRW (m : Memory) (base : BitVec 64) (len : Nat) :
    Decidable (m.RW base len) :=
  decForallBV64 fun a => InRegion base len a → m.permNoLazy a = some Perm.rw

local instance instDecidableReadable (m : Memory) (base : BitVec 64) (len : Nat) :
    Decidable (m.Readable base len) :=
  decForallBV64 fun a => InRegion base len a → (m.perm a).r = true ∧ m.isLazyFree a = false

local instance instDecidableDisjointRegions (b₁ : BitVec 64) (n₁ : Nat) (b₂ : BitVec 64) (n₂ : Nat) :
    Decidable (DisjointRegions b₁ n₁ b₂ n₂) :=
  inferInstanceAs (Decidable (n₁ ≤ (b₂ - b₁).toNat ∧ n₂ ≤ (b₁ - b₂).toNat))

local instance instDecidableMemcpyPre (u : State) : Decidable (MemcpyPre u) :=
  inferInstanceAs (Decidable (
    u.status = .Running ∧
    u.spAligned = true ∧
    u.mem.RW (u.readReg64 .x0) (u.readReg64 .x2).toNat ∧
    u.mem.Readable (u.readReg64 .x1) (u.readReg64 .x2).toNat ∧
    ((u.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (u.readReg64 .x0) (u.readReg64 .x2).toNat
        (u.readReg64 .x1) (u.readReg64 .x2).toNat)))

@[expose] def coupledMemcpy (f_mc : State → State) (m₀ : Memory)
    (kp : BitVec 64 → Bool) (u : State) : State :=
  letI : Decidable (∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a) :=
    decForallBV64 fun a => u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a
  if MemcpyPre u then
    if ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a then
      ProofLib.stripS kp (f_mc (u.setMem (restorePerm m₀ u.mem)))
    else
      (u.setMem (u.mem.writeBytes (u.readReg64 .x0)
        (u.mem.readBytes (u.readReg64 .x1) (u.readReg64 .x2).toNat))).setPC (u.readReg64 .lr)
  else
    u.setStatus (.Exception "ext")

private theorem stripS_applyMemcpyClobber_vm (kp : BitVec 64 → Bool) (s : State) (m' : Memory)
    (pc' : BitVec 64) (c : MemcpyClobber) :
    ProofLib.stripS kp (applyMemcpyClobber s m' pc' c) =
      applyMemcpyClobber (ProofLib.stripS kp s) (ProofLib.stripExecOutside kp m') pc' c := by
  cases s; rfl

private theorem allocCallPreserved_applyMemcpyClobber_vm (s : State) (m' : Memory)
    (pc' : BitVec 64) (c : MemcpyClobber) :
    AllocCallPreserved s (applyMemcpyClobber s m' pc' c) := by
  cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem coupledMemcpy_exact {f_mc : State → State} (hf : HookExactMemcpy f_mc)
    (m₀ : Memory) (kp : BitVec 64 → Bool) :
    HookExactMemcpy (coupledMemcpy f_mc m₀ kp) := by
  intro u dst src lr len bs hrun hsp hx0 hx1 hx2 hlr hbs hrw hread hdisj
  have hpre : MemcpyPre u := ⟨hrun, hsp, by rwa [hx0, hx2], by rwa [hx1, hx2], by rwa [hx0, hx1, hx2]⟩
  unfold coupledMemcpy
  simp only [hpre, ↓reduceIte]
  by_cases hperm : ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a
  · simp only [eq_true hperm, ↓reduceIte]
    let s1 := u.setMem (restorePerm m₀ u.mem)
    have hs1_run : s1.status = .Running := by cases u; exact hrun
    have hs1_sp : s1.spAligned = true := by cases u; exact hsp
    have hs1_x0 : s1.readReg64 .x0 = dst := by cases u; exact hx0
    have hs1_x1 : s1.readReg64 .x1 = src := by cases u; exact hx1
    have hs1_x2 : (s1.readReg64 .x2).toNat = len := by cases u; exact hx2
    have hs1_lr : s1.readReg64 .lr = lr := by cases u; exact hlr
    have hs1_bs : s1.mem.readBytes src len = bs := by
      change (restorePerm m₀ u.mem).readBytes src len = bs
      rwa [restorePerm_readBytes]
    have hs1_rw : s1.mem.RW dst len := restorePerm_rw hperm hrw
    have hs1_read : s1.mem.Readable src len := restorePerm_readable hperm hread
    obtain ⟨c, hfc⟩ :=
      hf hs1_run hs1_sp hs1_x0 hs1_x1 hs1_x2 hs1_lr hs1_bs hs1_rw hs1_read hdisj
    refine ⟨c, ?_⟩
    rw [hfc, stripS_applyMemcpyClobber_vm]
    have hu_eq : ProofLib.stripS kp s1 = u := by
      dsimp only [s1, ProofLib.stripS, State.setMem]
      rw [stripExecOutside_restorePerm hperm]
    have hm_eq : ProofLib.stripExecOutside kp (s1.mem.writeBytes dst bs) =
        u.mem.writeBytes dst bs := by
      change ProofLib.stripExecOutside kp ((restorePerm m₀ u.mem).writeBytes dst bs) = _
      rw [← stripExecOutside_writeBytes_vm, stripExecOutside_restorePerm hperm]
    rw [hu_eq, hm_eq]
  · simp only [hperm, ↓reduceIte]
    refine ⟨MemcpyClobber.ofState u, ?_⟩
    rw [hx0, hx1, hx2, hbs, hlr, applyMemcpyClobber_ofState_eq]

theorem coupledMemcpy_running_step {f_mc : State → State} (hf : HookExactMemcpy f_mc)
    {m₀ : Memory} {kp : BitVec 64 → Bool} {s1 : State}
    (hperm1 : ∀ a, s1.mem.perm a = m₀.perm a)
    (hrb' : (coupledMemcpy f_mc m₀ kp (ProofLib.stripS kp s1)).status = .Running) :
    coupledMemcpy f_mc m₀ kp (ProofLib.stripS kp s1) = ProofLib.stripS kp (f_mc s1) ∧
    VmPreserved s1 (f_mc s1) ∧
    AllocCallPreserved s1 (f_mc s1) := by
  let u := ProofLib.stripS kp s1
  have hperm_u : ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a := fun a => by
    have hm : u.mem = ProofLib.stripExecOutside kp s1.mem := by cases s1; rfl
    rw [hm, ProofLib.strip_perm, ProofLib.strip_perm, hperm1 a]
  have hs1_eq : u.setMem (restorePerm m₀ u.mem) = s1 := by
    cases s1; dsimp only [u, ProofLib.stripS, State.setMem]
    rw [restorePerm_stripExecOutside_self kp hperm1]
  have hpre : MemcpyPre u := by
    by_contra hnpre
    have hstat : (coupledMemcpy f_mc m₀ kp u).status = .Exception "ext" := by
      unfold coupledMemcpy; simp only [hnpre, ↓reduceIte]; cases u; rfl
    rw [hstat] at hrb'; cases hrb'
  have hc_eq : coupledMemcpy f_mc m₀ kp u = ProofLib.stripS kp (f_mc s1) := by
    unfold coupledMemcpy
    simp only [eq_true hpre, eq_true hperm_u, ↓reduceIte, hs1_eq]
  rcases hpre with ⟨hrun_u, hsp_u, hrw_u, hread_u, hdisj_u⟩
  have hrun1 : s1.status = .Running := by cases s1; exact hrun_u
  have hsp1 : s1.spAligned = true := by cases s1; exact hsp_u
  have hr64 : ∀ r, u.readReg64 r = s1.readReg64 r := fun _ => by cases s1; rfl
  rw [hr64, hr64] at hrw_u hread_u
  rw [hr64, hr64, hr64] at hdisj_u
  have hm_rest : restorePerm m₀ u.mem = s1.mem := by
    have hm : u.mem = ProofLib.stripExecOutside kp s1.mem := by cases s1; rfl
    rw [hm, restorePerm_stripExecOutside_self kp hperm1]
  have hrw1 : s1.mem.RW (s1.readReg64 .x0) (s1.readReg64 .x2).toNat :=
    hm_rest ▸ restorePerm_rw hperm_u hrw_u
  have hread1 : s1.mem.Readable (s1.readReg64 .x1) (s1.readReg64 .x2).toNat :=
    hm_rest ▸ restorePerm_readable hperm_u hread_u
  obtain ⟨c, hfc⟩ := hf hrun1 hsp1 rfl rfl rfl rfl rfl hrw1 hread1 hdisj_u
  refine ⟨hc_eq, ?_, ?_⟩
  · rw [hfc]; exact vmPreserved_applyMemcpyClobber_writeBytes s1 _ _ _ c
  · rw [hfc]; exact allocCallPreserved_applyMemcpyClobber_vm s1 _ _ c

/-! ## 4. Coupled `compress256` (`coupledCompress256`) -/

private theorem toLEBytes_4_read32 (m : Memory) (a : BitVec 64) :
    toLEBytes 4 (m.read32 a) = m.readBytes a 4 := by
  have hle : toLEBytes 4 (m.read32 a) =
      [(m.read32 a).extractLsb' 0 8, (m.read32 a).extractLsb' 8 8,
       (m.read32 a).extractLsb' 16 8, (m.read32 a).extractLsb' 24 8] := rfl
  rw [hle, readBytes_4_eq]
  dsimp only [Memory.read32]
  simp only [BitVec.add_zero, List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem shaStateBytes_readShaState (m : Memory) (a : BitVec 64) :
    m.readBytes a 32 = shaStateBytes (readShaState m a) := by
  rw [shaStateBytes_eq_append]
  simp only [readShaState, List.Vector.get_ofFn, Fin.val_zero, Fin.val_one,
    show (2 : Fin 8).val = 2 from rfl, show (3 : Fin 8).val = 3 from rfl,
    show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
    show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl,
    toLEBytes_4_read32]
  simp [Memory.readBytes, BitVec.add_assoc]

private theorem keepsFrozen_stripExecOutside {m1 m2 : Memory} (kp : BitVec 64 → Bool)
    (hkf : m1.KeepsFrozen m2) (hkx : KeepsExec m1 m2) :
    (ProofLib.stripExecOutside kp m1).KeepsFrozen (ProofLib.stripExecOutside kp m2) := by
  intro a hfr'
  have h_eq : m2.read8 a = m1.read8 a ∧ m2.perm a = m1.perm a ∧
      m2.isLazyFree a = m1.isLazyFree a ∧ m2.isAnon a = m1.isAnon a := by
    by_cases hx : (m1.perm a).x = true
    · exact hkx a hx
    · have hfr1 : m1.Frozen a := by
        unfold Memory.Frozen Option.frozen at hfr' ⊢
        rw [ProofLib.strip_perm] at hfr'
        cases hp1 : m1.perm a with
        | none => simp [hp1] at hfr'
        | some p =>
          rw [hp1] at hx hfr'
          rcases p with ⟨r, w, x, lf, an⟩
          simp only [Option.x, Bool.not_eq_true] at hx
          subst hx
          simpa [Option.map, ProofLib.stripPerm] using hfr'
      exact hkf a hfr1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ProofLib.strip_read8, ProofLib.strip_read8, h_eq.1]
  · rw [ProofLib.strip_perm, ProofLib.strip_perm, h_eq.2.1]
  · rw [ProofLib.strip_isLazyFree, ProofLib.strip_isLazyFree, h_eq.2.2.1]
  · rw [ProofLib.strip_isAnon, ProofLib.strip_isAnon, h_eq.2.2.2]

private theorem keepsExec_stripExecOutside {m1 m2 : Memory} (kp : BitVec 64 → Bool)
    (hkx : KeepsExec m1 m2) :
    KeepsExec (ProofLib.stripExecOutside kp m1) (ProofLib.stripExecOutside kp m2) := by
  intro a hx'
  have hx1 := (ProofLib.strip_perm_x_imp hx').1
  obtain ⟨hr, hp, hlf, han⟩ := hkx a hx1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ProofLib.strip_read8, ProofLib.strip_read8, hr]
  · rw [ProofLib.strip_perm, ProofLib.strip_perm, hp]
  · rw [ProofLib.strip_isLazyFree, ProofLib.strip_isLazyFree, hlf]
  · rw [ProofLib.strip_isAnon, ProofLib.strip_isAnon, han]

private theorem s2Frame_stripExecOutside {m1 m2 : Memory} (kp : BitVec 64 → Bool)
    {regs : List (BitVec 64 × Nat)}
    (hs2 : S2Frame m1 m2 regs) (hperm_eq : ∀ a, m2.perm a = m1.perm a)
    (hkx : KeepsExec m1 m2) :
    S2Frame (ProofLib.stripExecOutside kp m1) (ProofLib.stripExecOutside kp m2) regs := by
  refine ⟨fun a hr' hlf' hout => ?_,
    ⟨⟨fun a hnl' => ?_, fun a hrw' => ?_⟩,
     ⟨fun a ⟨hm', han'⟩ => ?_, fun a hpn' hout => ?_⟩⟩,
    fun a hr' hlf' => ?_⟩
  · rw [ProofLib.strip_read8, ProofLib.strip_read8]
    rw [(ProofLib.strip_perm_props kp m1 a).1] at hr'
    rw [ProofLib.strip_isLazyFree] at hlf'
    exact hs2.1 a hr' hlf' hout
  · obtain ⟨hrw', hlf'⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl'
    rw [(ProofLib.strip_perm_props kp m1 a).2.2.2] at hrw'
    rw [ProofLib.strip_isLazyFree] at hlf'
    obtain ⟨hrw2, hlf2⟩ :=
      Memory.permNoLazy_eq_some_rw_iff.mp
        (hs2.2.1.1.1 a (Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hrw', hlf'⟩))
    exact Memory.permNoLazy_eq_some_rw_iff.mpr
      ⟨(ProofLib.strip_perm_props kp m2 a).2.2.2.mpr hrw2,
       (ProofLib.strip_isLazyFree kp m2 a).trans hlf2⟩
  · rw [(ProofLib.strip_perm_props kp m1 a).2.2.2] at hrw'
    rw [(ProofLib.strip_perm_props kp m2 a).2.2.2]
    exact hs2.2.1.1.2 a hrw'
  · rw [(ProofLib.strip_perm_props kp m1 a).2.2.1] at hm'
    rw [ProofLib.strip_isAnon] at han'
    obtain ⟨hm2, han2⟩ := hs2.2.1.2.1 a ⟨hm', han'⟩
    exact ⟨(ProofLib.strip_perm_props kp m2 a).2.2.1.trans hm2,
      (ProofLib.strip_isAnon kp m2 a).trans han2⟩
  · have hpn2 : (ProofLib.stripExecOutside kp m2).perm a = some Perm.protNone := by
      rw [ProofLib.strip_perm, hperm_eq a, ← ProofLib.strip_perm, hpn']
    refine ⟨hpn2, fun hlf' => ?_⟩
    rw [ProofLib.strip_isLazyFree] at hlf'
    rw [ProofLib.strip_read8, ProofLib.strip_read8, ProofLib.strip_isLazyFree]
    by_cases hx1 : (m1.perm a).x = true
    · obtain ⟨hr, -, hlf_eq, -⟩ := hkx a hx1
      exact ⟨hr, hlf_eq.trans hlf'⟩
    · have hpn1 : m1.perm a = some Perm.protNone := by
        rw [ProofLib.strip_perm] at hpn'
        cases hp1 : m1.perm a with
        | none => simp [hp1] at hpn'
        | some p =>
          rw [hp1] at hx1 hpn'
          rcases p with ⟨r, w, x, lf, an⟩
          simp only [Option.x, Bool.not_eq_true] at hx1
          subst hx1
          simpa [Option.map, ProofLib.stripPerm] using hpn'
      exact (hs2.2.1.2.2 a hpn1 hout).2 hlf'
  · rw [(ProofLib.strip_perm_props kp m1 a).1] at hr'
    rw [ProofLib.strip_isLazyFree] at hlf'
    obtain ⟨hr2, hlf2⟩ := hs2.2.2 a hr' hlf'
    exact ⟨(ProofLib.strip_perm_props kp m2 a).1.trans hr2,
      (ProofLib.strip_isLazyFree kp m2 a).trans hlf2⟩

@[expose] def Compress256Pre [LibsignalPlacement] (u : State) : Prop :=
  let stA := u.readReg64 .x0
  let blkA := u.readReg64 .x1
  let n := (u.readReg64 .x2).toNat
  u.status = .Running ∧
  u.spAligned = true ∧
  u.mem.RW stA 32 ∧
  u.mem.RW (u.sp - 176#64) 176 ∧
  u.mem.Readable blkA (64 * n) ∧
  DisjointRegions stA 32 (u.sp - 176#64) 176 ∧
  (n = 0 ∨ DisjointRegions stA 32 blkA (64 * n)) ∧
  (n = 0 ∨ DisjointRegions (u.sp - 176#64) 176 blkA (64 * n)) ∧
  64 * n ≤ 2 ^ 64 ∧
  LsRetAddr624 (u.readReg64 .lr)

local instance instDecidableLsRetAddr624 [LibsignalPlacement] (lr : BitVec 64) :
    Decidable (LsRetAddr624 lr) :=
  inferInstanceAs
    (Decidable (∃ j < 624, ∃ o < LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen j,
      lr = lsmpl.base j + BitVec.ofNat 64 o))

local instance instDecidableCompress256Pre [LibsignalPlacement] (u : State) :
    Decidable (Compress256Pre u) :=
  inferInstanceAs (Decidable (
    u.status = .Running ∧
    u.spAligned = true ∧
    u.mem.RW (u.readReg64 .x0) 32 ∧
    u.mem.RW (u.sp - 176#64) 176 ∧
    u.mem.Readable (u.readReg64 .x1) (64 * (u.readReg64 .x2).toNat) ∧
    DisjointRegions (u.readReg64 .x0) 32 (u.sp - 176#64) 176 ∧
    ((u.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (u.readReg64 .x0) 32 (u.readReg64 .x1) (64 * (u.readReg64 .x2).toNat)) ∧
    ((u.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (u.sp - 176#64) 176 (u.readReg64 .x1) (64 * (u.readReg64 .x2).toNat)) ∧
    64 * (u.readReg64 .x2).toNat ≤ 2 ^ 64 ∧
    LsRetAddr624 (u.readReg64 .lr)))

@[expose] def coupledCompress256 [LibsignalPlacement] (f_c256 : State → State)
    (F : ShaCompress) (m₀ : Memory) (kp : BitVec 64 → Bool) (u : State) : State :=
  letI : Decidable (∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a) :=
    decForallBV64 fun a => u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a
  if Compress256Pre u then
    if ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a then
      ProofLib.stripS kp (f_c256 (u.setMem (restorePerm m₀ u.mem)))
    else
      compress256Hook F u
  else
    u.setStatus (.Exception "ext")

private theorem compress256Pre_of_roBudgetPre [LibsignalPlacement] {F : ShaCompress} {u : State}
    {ro : Bool} {stA blkA : BitVec 64} {st : ShaState} {bs : List (BitVec 8)} {n : Nat}
    {R : SepProp}
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hpre : u.mem ⊨ (withLsRet624 (sessionCompress256ROBudgetSpec F 176)).pre
      (ro, stA, st, blkA, bs, n) u ∗ R) :
    Compress256Pre u ∧
    u.readReg64 .x0 = stA ∧ u.readReg64 .x1 = blkA ∧ (u.readReg64 .x2).toNat = n ∧
    bs.length = 64 * n ∧ bs.length ≤ 2 ^ 64 ∧
    u.mem.readBytes stA 32 = shaStateBytes st ∧
    u.mem.readBytes blkA (64 * n) = bs ∧
    u.mem ⊨ (stA ↦ₛ shaStateBytes st) ∗ (stackAt u.sp 176 ∗ (compress256Blocks ro blkA bs ∗ R)) := by
  dsimp only [withLsRet624] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hlr_ls, hpre⟩
  dsimp only [sessionCompress256ROBudgetSpec, sessionCompress256ROSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs_len, hbs_le⟩, hmem⟩
  have hst_len : (shaStateBytes st).length = 32 := shaStateBytes_length st
  have hb_st := IsBlock.pointsToBytes_len (a := stA) hst_len
  have hb_stk := IsBlock.memRegion (u.sp - 176#64) 176
  have hmem_st : u.mem ⊨ (stA ↦ₛ shaStateBytes st) ∗
      (stackAt u.sp 176 ∗ (compress256Blocks ro blkA bs ∗ R)) := by
    ac_nf at hmem ⊢
  have hmem_stk : u.mem ⊨ stackAt u.sp 176 ∗
      ((stA ↦ₛ shaStateBytes st) ∗ (compress256Blocks ro blkA bs ∗ R)) := by
    ac_nf at hmem ⊢
  have hrw_st : u.mem.RW stA 32 := hb_st.rw hmem_st
  have hrw_stk : u.mem.RW (u.sp - 176#64) 176 := hb_stk.rw hmem_stk
  have hst_bytes : u.mem.readBytes stA 32 = shaStateBytes st := by
    simpa [hst_len] using (hb_st.read hmem_st).2
  have hdisj_st_stk : DisjointRegions stA 32 (u.sp - 176#64) 176 :=
    hb_st.disjoint hb_stk (by decide) (by decide) hmem_st
  have hblk_props :
      u.mem.readBytes blkA (64 * n) = bs ∧
      u.mem.Readable blkA (64 * n) ∧
      (n = 0 ∨ DisjointRegions stA 32 blkA (64 * n)) ∧
      (n = 0 ∨ DisjointRegions (u.sp - 176#64) 176 blkA (64 * n)) := by
    cases ro
    · dsimp only [compress256Blocks, cond] at hmem
      have hblk_front : u.mem ⊨ (blkA ↦ₛ bs) ∗
          ((stA ↦ₛ shaStateBytes st) ∗ stackAt u.sp 176 ∗ R) := by ac_nf at hmem ⊢
      have hb_blk := IsBlock.pointsToBytes blkA bs
      have hread_b : u.mem.readBytes blkA (64 * n) = bs :=
        hbs_len ▸ (hb_blk.read hblk_front).2
      have hrd_b : u.mem.Readable blkA (64 * n) := hbs_len ▸ fun a ha =>
        ⟨by rw [hb_blk.perm_rw hblk_front ha]; rfl, hb_blk.isLazyFree_false hblk_front ha⟩
      by_cases hn0 : n = 0
      · exact ⟨hread_b, hrd_b, Or.inl hn0, Or.inl hn0⟩
      · have hpos : 0 < bs.length := by omega
        have hm1 : u.mem ⊨ (stA ↦ₛ shaStateBytes st) ∗
            ((blkA ↦ₛ bs) ∗ stackAt u.sp 176 ∗ R) := by ac_nf at hmem ⊢
        have hm2 : u.mem ⊨ stackAt u.sp 176 ∗
            ((blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st) ∗ R) := by ac_nf at hmem ⊢
        exact ⟨hread_b, hrd_b,
          Or.inr (hbs_len ▸ hb_st.disjoint hb_blk (by decide) hpos hm1),
          Or.inr (hbs_len ▸ hb_stk.disjoint hb_blk (by decide) hpos hm2)⟩
    · dsimp only [compress256Blocks, cond] at hmem
      have hblk_front : u.mem ⊨ (blkA ↦ᵣ bs) ∗
          ((stA ↦ₛ shaStateBytes st) ∗ stackAt u.sp 176 ∗ R) := by ac_nf at hmem ⊢
      have hb_blk := IsBlockRO.pointsToBytesRO blkA bs hbs_le
      have hread_b : u.mem.readBytes blkA (64 * n) = bs :=
        hbs_len ▸ hb_blk.read hblk_front
      have hrd_b : u.mem.Readable blkA (64 * n) := hbs_len ▸ fun a ha =>
        ⟨hb_blk.perm_r hblk_front ha, hb_blk.isLazyFree_false hblk_front ha⟩
      by_cases hn0 : n = 0
      · exact ⟨hread_b, hrd_b, Or.inl hn0, Or.inl hn0⟩
      · have hpos : 0 < bs.length := by omega
        have hm1 : u.mem ⊨ (blkA ↦ᵣ bs) ∗
            (memRegion stA 32 ∗ (stackAt u.sp 176 ∗ R)) := by
          have hm1' : u.mem ⊨ (stA ↦ₛ shaStateBytes st) ∗
              ((blkA ↦ᵣ bs) ∗ (stackAt u.sp 176 ∗ R)) := by ac_nf at hmem ⊢
          have hm1'' := Satisfies.mono
            (sepConj_mono_left (hst_len ▸ pointsToBytes_entails_memRegion stA (shaStateBytes st))) hm1'
          ac_nf at hm1'' ⊢
        have hnd1 : ¬ InRegion stA 32 blkA := fun h =>
          not_satisfies_ownsRO_ownsRW
            (ownsRO_pointsToBytesRO_at hbs_le (by simp [InRegion, hpos]))
            (ownsRW_sepConj_left (ownsRW_memRegion stA 32 blkA h)) hm1
        have hns1 : ¬ InRegion blkA bs.length stA := fun h =>
          not_satisfies_ownsRO_ownsRW
            (ownsRO_pointsToBytesRO_at hbs_le h)
            (ownsRW_sepConj_left (ownsRW_memRegion stA 32 stA (by simp [InRegion]))) hm1
        have hm2 : u.mem ⊨ (blkA ↦ᵣ bs) ∗
            (memRegion (u.sp - 176#64) 176 ∗ ((stA ↦ₛ shaStateBytes st) ∗ R)) := by
          dsimp only [stackAt] at hmem
          ac_nf at hmem ⊢
        have hnd2 : ¬ InRegion (u.sp - 176#64) 176 blkA := fun h =>
          not_satisfies_ownsRO_ownsRW
            (ownsRO_pointsToBytesRO_at hbs_le (by simp [InRegion, hpos]))
            (ownsRW_sepConj_left (ownsRW_memRegion (u.sp - 176#64) 176 blkA h)) hm2
        have hns2 : ¬ InRegion blkA bs.length (u.sp - 176#64) := fun h =>
          not_satisfies_ownsRO_ownsRW
            (ownsRO_pointsToBytesRO_at hbs_le h)
            (ownsRW_sepConj_left
              (ownsRW_memRegion (u.sp - 176#64) 176 (u.sp - 176#64) (by simp [InRegion]))) hm2
        dsimp only [InRegion] at hnd1 hns1 hnd2 hns2
        rw [hbs_len] at hns1 hns2
        exact ⟨hread_b, hrd_b,
          Or.inr ⟨Nat.le_of_not_lt hnd1, Nat.le_of_not_lt hns1⟩,
          Or.inr ⟨Nat.le_of_not_lt hnd2, Nat.le_of_not_lt hns2⟩⟩
  have hpre_c : Compress256Pre u := by
    dsimp only [Compress256Pre]
    rw [hx0, hx1, hx2]
    exact ⟨hrun, hsp, hrw_st, hrw_stk, hblk_props.2.1,
      hdisj_st_stk, hblk_props.2.2.1, hblk_props.2.2.2, hbs_len ▸ hbs_le, hlr_ls⟩
  exact ⟨hpre_c, hx0, hx1, hx2, hbs_len, hbs_le, hst_bytes, hblk_props.1, hmem_st⟩

private theorem callingConventionPreserved_setMem_stripS (u s' : State) (m : Memory)
    (kp : BitVec 64 → Bool) (h : CallingConventionPreserved (u.setMem m) s') :
    CallingConventionPreserved u (ProofLib.stripS kp s') := by
  cases u; cases s'; exact h

private theorem vmPreserved_setMem_stripS (u s' : State) (m : Memory)
    (kp : BitVec 64 → Bool) (hvm : VmPreserved (u.setMem m) s')
    (hperm : ∀ a, (ProofLib.stripExecOutside kp s'.mem).perm a = u.mem.perm a) :
    VmPreserved u (ProofLib.stripS kp s') := by
  rcases hvm with ⟨hpool, hpma, -, hfds⟩
  cases u; cases s'
  exact ⟨hpool, hpma, hperm, hfds⟩

theorem coupledCompress256_ok [LibsignalPlacement] {F : ShaCompress} {f_c256 : State → State}
    (hf : HookOkCompress256 f_c256 F) (m₀ : Memory) (kp : BitVec 64 → Bool) :
    HookOkCompress256 (coupledCompress256 f_c256 F m₀ kp) F := by
  rcases hf with ⟨hfOk, hfKx⟩
  refine ⟨?_, ?_⟩
  · intro ⟨ro, stA, st, blkA, bs, n⟩ R u hrun hpre hsp
    obtain ⟨hpre_c, hx0, hx1, hx2, hbs_len, hbs_le, hst_u, hbs_u, hmem_st⟩ :=
      compress256Pre_of_roBudgetPre hrun hsp hpre
    unfold coupledCompress256
    simp only [hpre_c, ↓reduceIte]
    by_cases hperm : ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a
    · simp only [eq_true hperm, ↓reduceIte]
      let s1 := u.setMem (restorePerm m₀ u.mem)
      have hs1_run : s1.status = .Running := by cases u; exact hrun
      have hs1_sp_al : (s1.sp &&& 15#64) = 0#64 := by
        dsimp only [s1, State.setMem]
        simpa [State.spAligned] using hsp
      have hs1_x0 : s1.readReg64 .x0 = stA := by cases u; exact hx0
      have hs1_x1 : s1.readReg64 .x1 = blkA := by cases u; exact hx1
      have hs1_x2 : (s1.readReg64 .x2).toNat = n := by cases u; exact hx2
      have hs1_sp_eq : s1.sp = u.sp := by cases u; rfl
      have hs1_st : s1.mem.readBytes stA 32 = shaStateBytes st := by
        change (restorePerm m₀ u.mem).readBytes stA 32 = shaStateBytes st
        rwa [restorePerm_readBytes]
      have hs1_bs : s1.mem.readBytes blkA (64 * n) = bs := by
        change (restorePerm m₀ u.mem).readBytes blkA (64 * n) = bs
        rwa [restorePerm_readBytes]
      have hrw_st_u : u.mem.RW stA 32 := by have := hpre_c.2.2.1; rwa [hx0] at this
      have hrw_stk_u : u.mem.RW (u.sp - 176#64) 176 := hpre_c.2.2.2.1
      have hrd_blk_u : u.mem.Readable blkA (64 * n) := by
        have := hpre_c.2.2.2.2.1; rwa [hx1, hx2] at this
      have hd1 : DisjointRegions stA 32 (s1.sp - 176#64) 176 := by
        rw [hs1_sp_eq]; have := hpre_c.2.2.2.2.2.1; rwa [hx0] at this
      have hd2 : n = 0 ∨ DisjointRegions stA 32 blkA (64 * n) := by
        have := hpre_c.2.2.2.2.2.2.1; rwa [hx0, hx1, hx2] at this
      have hd3 : n = 0 ∨ DisjointRegions (s1.sp - 176#64) 176 blkA (64 * n) := by
        rw [hs1_sp_eq]; have := hpre_c.2.2.2.2.2.2.2.1; rwa [hx1, hx2] at this
      have hs1_lr : LsRetAddr624 (s1.readReg64 .lr) := by
        have hlr_eq : s1.readReg64 .lr = u.readReg64 .lr := by cases u; rfl
        rw [hlr_eq]; exact hpre_c.2.2.2.2.2.2.2.2.2
      obtain ⟨hkf1, hsym1, hret1, hcc1, hvm1, hacp1, htr1, hread_out1, hs2_1, -⟩ :=
        hookOk_withLsRet624_sessionCompress256ROBudget_elim hfOk hs1_lr hs1_run hs1_x0 hs1_x1
          hs1_x2 hs1_sp_al hs1_st hs1_bs (restorePerm_rw hperm hrw_st_u)
          (hs1_sp_eq ▸ restorePerm_rw hperm hrw_stk_u)
          (restorePerm_readable hperm hrd_blk_u) hd1 hd2 hd3 (hbs_len ▸ hbs_le)
      have hkx1 : KeepsExec s1.mem (f_c256 s1).mem :=
        hfKx s1 (hs1_x0 ▸ restorePerm_rw hperm hrw_st_u)
      have hu_mem : ProofLib.stripExecOutside kp s1.mem = u.mem :=
        stripExecOutside_restorePerm hperm
      have hkf : u.mem.KeepsFrozen (ProofLib.stripS kp (f_c256 s1)).mem := by
        change u.mem.KeepsFrozen (ProofLib.stripExecOutside kp (f_c256 s1).mem)
        rw [← hu_mem]
        exact keepsFrozen_stripExecOutside kp hkf1 hkx1
      have hsym : (ProofLib.stripS kp (f_c256 s1)).symtab = u.symtab := by
        have h1 : (ProofLib.stripS kp (f_c256 s1)).symtab = (f_c256 s1).symtab := by
          cases f_c256 s1; rfl
        have h2 : s1.symtab = u.symtab := by cases u; rfl
        exact h1.trans (hsym1.trans h2)
      have hret : Returned u (ProofLib.stripS kp (f_c256 s1)) := by
        rcases hret1 with ⟨hpc, hsp', hst'⟩
        have hlr_eq : s1.readReg64 .lr = u.readReg64 .lr := by cases u; rfl
        have hpc_strip : (ProofLib.stripS kp (f_c256 s1)).pc = (f_c256 s1).pc := by
          cases f_c256 s1; rfl
        have hsp_strip : (ProofLib.stripS kp (f_c256 s1)).sp = (f_c256 s1).sp := by
          cases f_c256 s1; rfl
        have hst_strip : (ProofLib.stripS kp (f_c256 s1)).status = (f_c256 s1).status := by
          cases f_c256 s1; rfl
        exact ⟨hpc_strip.trans (hpc.trans hlr_eq),
          hsp_strip.trans (hsp'.trans hs1_sp_eq),
          hst_strip.trans hst'⟩
      have hcc : CallingConventionPreserved u (ProofLib.stripS kp (f_c256 s1)) :=
        callingConventionPreserved_setMem_stripS u (f_c256 s1) (restorePerm m₀ u.mem) kp hcc1
      have hvm : VmPreserved u (ProofLib.stripS kp (f_c256 s1)) := by
        refine vmPreserved_setMem_stripS u (f_c256 s1) (restorePerm m₀ u.mem) kp hvm1 fun a => ?_
        rw [ProofLib.strip_perm, hvm1.perm_eq a, ← ProofLib.strip_perm, hu_mem]
      have hacp : AllocCallPreserved u (ProofLib.stripS kp (f_c256 s1)) := by
        have h1 : AllocCallPreserved u s1 := by
          dsimp only [s1, State.setMem]; exact allocCallPreserved_refl u
        have h2 : AllocCallPreserved (f_c256 s1) (ProofLib.stripS kp (f_c256 s1)) := by
          cases f_c256 s1; exact allocCallPreserved_refl _
        exact allocCallPreserved_trans h1 (allocCallPreserved_trans hacp1 h2)
      have htr : (ProofLib.stripS kp (f_c256 s1)).trace = u.trace := by
        have ht1 : (ProofLib.stripS kp (f_c256 s1)).trace = (f_c256 s1).trace := by
          cases f_c256 s1; rfl
        exact ht1.trans htr1
      let outBytes := shaStateBytes ((chunks64 bs).foldl F st)
      have hs2_u : S2Frame u.mem (ProofLib.stripS kp (f_c256 s1)).mem
          [(stA, 32), (u.sp - 176#64, 176)] := by
        change S2Frame u.mem (ProofLib.stripExecOutside kp (f_c256 s1).mem) _
        rw [← hu_mem, ← hs1_sp_eq]
        exact s2Frame_stripExecOutside kp hs2_1 hvm1.perm_eq hkx1
      have hread_out_u : (ProofLib.stripS kp (f_c256 s1)).mem.readBytes stA 32 = outBytes := by
        change (ProofLib.stripExecOutside kp (f_c256 s1).mem).readBytes stA 32 = outBytes
        rw [stripExecOutside_readBytes]
        exact hread_out1
      have hst_len : (shaStateBytes st).length = 32 := shaStateBytes_length st
      have hout_len : outBytes.length = 32 := shaStateBytes_length _
      have hpost_mem : (ProofLib.stripS kp (f_c256 s1)).mem ⊨
          (stA ↦ₛ outBytes) ∗ (stackAt u.sp 176 ∗ (compress256Blocks ro blkA bs ∗ R)) :=
        S2Frame.update_two_blocks
          (IsBlock.pointsToBytes_len (a := stA) hst_len)
          (IsBlock.pointsToBytes_len (a := stA) hout_len)
          (IsBlock.memRegion (u.sp - 176#64) 176)
          (IsBlock.memRegion (u.sp - 176#64) 176)
          hmem_st hs2_u ⟨by rw [hout_len]; decide, by rwa [hout_len]⟩ trivial
      refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
      dsimp only [withLsRet624, sessionCompress256ROBudgetSpec, sessionCompress256ROSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hvm, hacp⟩, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htr, by ac_nf at hpost_mem ⊢⟩
    · simp only [hperm, ↓reduceIte]
      exact hookOk_withLsRet624 (compress256Hook_roBudget_ok F 176)
        (ro, stA, st, blkA, bs, n) R u hrun hpre hsp
  · intro u hrw_u
    unfold coupledCompress256
    by_cases hpre_c : Compress256Pre u
    · simp only [hpre_c, ↓reduceIte]
      by_cases hperm : ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a
      · simp only [eq_true hperm, ↓reduceIte]
        let s1 := u.setMem (restorePerm m₀ u.mem)
        have hs1_rw : s1.mem.RW (s1.readReg64 .x0) 32 := by
          have hx0_eq : s1.readReg64 .x0 = u.readReg64 .x0 := by cases u; rfl
          rw [hx0_eq]
          exact restorePerm_rw hperm hrw_u
        have hkx1 := hfKx s1 hs1_rw
        have hu_mem : ProofLib.stripExecOutside kp s1.mem = u.mem :=
          stripExecOutside_restorePerm hperm
        change KeepsExec u.mem (ProofLib.stripExecOutside kp (f_c256 s1).mem)
        rw [← hu_mem]
        exact keepsExec_stripExecOutside kp hkx1
      · simp only [hperm, ↓reduceIte]
        exact compress256Hook_keepsExec F u hrw_u
    · simp only [hpre_c, ↓reduceIte]
      intro a _
      cases u
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem coupledCompress256_running_step [LibsignalPlacement] {F : ShaCompress}
    {f_c256 : State → State}
    (hf : HookOkCompress256 f_c256 F)
    {m₀ : Memory} {kp : BitVec 64 → Bool} {s1 : State}
    (hperm1 : ∀ a, s1.mem.perm a = m₀.perm a)
    (hrb' : (coupledCompress256 f_c256 F m₀ kp (ProofLib.stripS kp s1)).status = .Running) :
    coupledCompress256 f_c256 F m₀ kp (ProofLib.stripS kp s1) = ProofLib.stripS kp (f_c256 s1) ∧
    VmPreserved s1 (f_c256 s1) ∧
    AllocCallPreserved s1 (f_c256 s1) := by
  let u := ProofLib.stripS kp s1
  have hperm_u : ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a := fun a => by
    have hm : u.mem = ProofLib.stripExecOutside kp s1.mem := by cases s1; rfl
    rw [hm, ProofLib.strip_perm, ProofLib.strip_perm, hperm1 a]
  have hs1_eq : u.setMem (restorePerm m₀ u.mem) = s1 := by
    cases s1; dsimp only [u, ProofLib.stripS, State.setMem]
    rw [restorePerm_stripExecOutside_self kp hperm1]
  have hpre : Compress256Pre u := by
    by_contra hnpre
    have hstat : (coupledCompress256 f_c256 F m₀ kp u).status = .Exception "ext" := by
      unfold coupledCompress256; simp only [hnpre, ↓reduceIte]; cases u; rfl
    rw [hstat] at hrb'; cases hrb'
  have hc_eq : coupledCompress256 f_c256 F m₀ kp u = ProofLib.stripS kp (f_c256 s1) := by
    unfold coupledCompress256
    simp only [eq_true hpre, eq_true hperm_u, ↓reduceIte, hs1_eq]
  rcases hpre with ⟨hrun_u, hsp_u, hrw_st_u, hrw_stk_u, hrd_blk_u, hd1, hd2, hd3, hn_le, hlr_ls⟩
  have hrun1 : s1.status = .Running := by cases s1; exact hrun_u
  have hsp_al1 : (s1.sp &&& 15#64) = 0#64 := by
    have hsp_eq' : u.spAligned = s1.spAligned := by dsimp only [u]; cases s1; rfl
    rw [hsp_eq'] at hsp_u
    simpa [State.spAligned] using hsp_u
  have hr64 : ∀ r, u.readReg64 r = s1.readReg64 r := fun _ => by cases s1; rfl
  have hsp_eq : u.sp = s1.sp := by cases s1; rfl
  rw [hr64] at hrw_st_u
  rw [hsp_eq] at hrw_stk_u
  rw [hr64, hr64] at hrd_blk_u
  rw [hr64, hsp_eq] at hd1
  rw [hr64, hr64, hr64] at hd2
  rw [hr64, hsp_eq, hr64] at hd3
  rw [hr64] at hn_le
  rw [hr64] at hlr_ls
  have hm_rest : restorePerm m₀ u.mem = s1.mem := by
    have hm : u.mem = ProofLib.stripExecOutside kp s1.mem := by cases s1; rfl
    rw [hm, restorePerm_stripExecOutside_self kp hperm1]
  obtain ⟨-, -, -, -, hvm1, hacp1, -⟩ :=
    hookOk_withLsRet624_sessionCompress256ROBudget_elim hf.1 hlr_ls hrun1 rfl rfl rfl hsp_al1
      (shaStateBytes_readShaState s1.mem (s1.readReg64 .x0)) rfl
      (hm_rest ▸ restorePerm_rw hperm_u hrw_st_u)
      (hm_rest ▸ restorePerm_rw hperm_u hrw_stk_u)
      (hm_rest ▸ restorePerm_readable hperm_u hrd_blk_u)
      hd1 hd2 hd3 hn_le
  exact ⟨hc_eq, hvm1, hacp1⟩

/-! ## 5. Hook Tables & Placed Block-Segment `RunsTo` Lifting -/

private theorem option_or_isSome_vm {α : Type} (o₁ o₂ : Option α) :
    (o₁.or o₂).isSome = (o₁.isSome || o₂.isSome) := by cases o₁ <;> rfl

private theorem findSome?_isSome_congr_vm {α β γ : Type} (l : List α)
    (f : α → Option β) (g : α → Option γ) (h : ∀ x, (f x).isSome = (g x).isSome) :
    (l.findSome? f).isSome = (l.findSome? g).isSome := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?]
    cases hf : f x <;> cases hg : g x
    · exact ih
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · rfl

private theorem strip_codeLoaded_of_keep_vm {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem strip_execOnlyIn_of_keep_vm (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_vm {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem step_P_extern_eq_vm {P : Program} {s1 s2 : State} {f : State → State}
    (hstep : Step P s1 s2) (hrun2 : s2.status = .Running)
    (heP : P.externAt? s1.pc = some f) :
    s2 = f s1 ∧ s1.mem.KeepsFrozen (f s1).mem ∧ (f s1).symtab = s1.symtab := by
  cases hstep with
  | @exec _ _ hfe => unfold Program.fetchMem at hfe; rw [heP] at hfe; simp at hfe
  | halt_unmapped _ _ he => rw [heP] at he; cases he
  | extern _ he hkf hsym =>
    rw [heP] at he; injection he with hff; subst hff; exact ⟨rfl, hkf, hsym⟩
  | extern_fault _ _ _ => cases s1; cases hrun2

private theorem step_P_exec_eq_vm {P : Program} {s1 s2 : State} {inst : Instr}
    (hstep : Step P s1 s2)
    (hfeP : P.fetchMem s1.mem s1.pc = some inst)
    (hnsvc0 : inst.isSvc0 = false) :
    s2 = execInst inst s1 := by
  have heP_none : P.externAt? s1.pc = none := by
    unfold Program.fetchMem at hfeP
    cases he : P.externAt? s1.pc with | none => rfl | some _ => simp [he] at hfeP
  cases hstep with
  | @exec _ _ hfe' =>
    rw [hfeP] at hfe'; injection hfe' with hi; subst hi
    exact Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
  | halt_unmapped _ hfe' _ => rw [hfeP] at hfe'; cases hfe'
  | extern _ he _ _ => rw [heP_none] at he; cases he
  | extern_fault _ he _ => rw [heP_none] at he; cases he

/-! ### 5a. `hmacCompressOnlyExcHooksSat` (`compress256`-Only Segments) -/

@[expose] def hmacCompressOnlyExcHooksSat [LibsignalPlacement] (F : ShaCompress)
    (H : LibsignalHooks) (m₀ : Memory) (kp : BitVec 64 → Bool) : LibsignalHooks :=
  fun n =>
    if n = lsCompress256Sym then (H lsCompress256Sym).map (fun f_c256 => coupledCompress256 f_c256 F m₀ kp)
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

theorem hmacCompressOnlyExcHooksSat_compress [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks}
    (h_c256 : HookSatCompress256 H lsCompress256Sym F)
    (m₀ : Memory) (kp : BitVec 64 → Bool) :
    HookSatCompress256 (hmacCompressOnlyExcHooksSat F H m₀ kp) lsCompress256Sym F := by
  rcases h_c256 with ⟨f_c256, hfH, hfOk⟩
  exact ⟨coupledCompress256 f_c256 F m₀ kp,
    by simp [hmacCompressOnlyExcHooksSat, hfH],
    coupledCompress256_ok hfOk m₀ kp⟩

private theorem hmacCompressOnlyExcHooksSat_isSome [LibsignalPlacement] (F : ShaCompress)
    (H : LibsignalHooks) (m₀ : Memory) (kp : BitVec 64 → Bool) (n : String) :
    (hmacCompressOnlyExcHooksSat F H m₀ kp n).isSome = (H n).isSome := by
  unfold hmacCompressOnlyExcHooksSat
  by_cases h : n = lsCompress256Sym <;> simp [h]

private theorem blockProgram_hmacCompressOnlyExcHooksSat_externAt?_isSome [LibsignalPlacement]
    (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    (F : ShaCompress) (H : LibsignalHooks) (m₀ : Memory) (kp : BitVec 64 → Bool)
    (pc : BitVec 64) :
    ((lib.blockProgram pl i (hmacCompressOnlyExcHooksSat F H m₀ kp)).externAt? pc).isSome =
      ((lib.blockProgram pl i H).externAt? pc).isSome := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program
  dsimp only
  rw [option_or_isSome_vm, option_or_isSome_vm]
  rw [findSome?_isSome_congr_vm _
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then
        hmacCompressOnlyExcHooksSat F H m₀ kp x.1
      else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then H x.1 else none)]
  intro x
  cases h : (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) <;>
    simp [hmacCompressOnlyExcHooksSat_isSome]

private theorem findSome?_hmacCompressOnlyExcHooksSat_cases [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} {f_c256 : State → State}
    (h_c256 : H lsCompress256Sym = some f_c256)
    (m₀ : Memory) (kp : BitVec 64 → Bool) :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then hmacCompressOnlyExcHooksSat F H m₀ kp n else none) =
        some f →
      (∀ s, (f s).status = .Exception "ext") ∨
      (f = coupledCompress256 f_c256 F m₀ kp ∧
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f_c256)
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons] at h ⊢
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_hmacCompressOnlyExcHooksSat_cases h_c256 m₀ kp tl h
    · simp only [ho, ↓reduceIte] at h ⊢
      unfold hmacCompressOnlyExcHooksSat at h
      by_cases h2 : n = lsCompress256Sym
      · subst h2; simp only [↓reduceIte, h_c256, Option.map, Option.some.injEq] at h; subst h
        rw [h_c256]; exact Or.inr ⟨rfl, rfl⟩
      · simp only [h2, ↓reduceIte] at h
        cases hHn : H n with
        | none =>
          rw [hHn] at h; dsimp only [Option.map] at h ⊢
          exact findSome?_hmacCompressOnlyExcHooksSat_cases h_c256 m₀ kp tl h
        | some _ =>
          rw [hHn] at h; simp only [Option.map, Option.some.injEq] at h; subst h
          exact Or.inl fun s => by cases s; rfl

private theorem blockProgram_hmacCompressOnlyExcHooksSat_externAt?_cases [LibsignalPlacement]
    {lib : MultiPlacedLib} {pl : MultiPlacement} {i : Nat}
    {F : ShaCompress} {H : LibsignalHooks} {f_c256 : State → State}
    (h_c256 : H lsCompress256Sym = some f_c256)
    {m₀ : Memory} {kp : BitVec 64 → Bool}
    {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram pl i (hmacCompressOnlyExcHooksSat F H m₀ kp)).externAt? pc = some f) :
    (∀ s, (f s).status = .Exception "ext") ∨
    (f = coupledCompress256 f_c256 F m₀ kp ∧ (lib.blockProgram pl i H).externAt? pc = some f_c256) := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program at h ⊢
  dsimp only at h ⊢
  have hnone : ∀ (l : List (String × Nat)),
      (l.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro l; induction l with | nil => rfl | cons _ _ ih => exact ih
  simp only [ite_self, hnone, Option.or_none] at h ⊢
  exact findSome?_hmacCompressOnlyExcHooksSat_cases h_c256 m₀ kp _ h

theorem steps_hmacCompressOnlyExcSat_lift_strip_allocVm [LibsignalPlacement]
    (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    {F : ShaCompress} {H : LibsignalHooks}
    (h_c256 : HookSatCompress256 H lsCompress256Sym F)
    (m₀ : Memory)
    (hall_svc :
      (lib.blockProgram pl i
        (hmacCompressOnlyExcHooksSat F H m₀ (ProofLib.progKeep (lib.blockProgram pl i H)))).allInstrs
      (fun ins => !ins.isSvc0) = true)
    (hall_msr :
      (lib.blockProgram pl i
        (hmacCompressOnlyExcHooksSat F H m₀ (ProofLib.progKeep (lib.blockProgram pl i H)))).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true)
    {s1' sf' : State}
    (hsteps : Steps
      (lib.blockProgram pl i
        (hmacCompressOnlyExcHooksSat F H m₀ (ProofLib.progKeep (lib.blockProgram pl i H)))) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let P := lib.blockProgram pl i H
    let Q := lib.blockProgram pl i (hmacCompressOnlyExcHooksSat F H m₀ (ProofLib.progKeep P))
    ∀ (s1 sfP : State),
      s1' = ProofLib.stripS (ProofLib.progKeep Q) s1 →
      (∀ a, s1.mem.perm a = m₀.perm a) →
      Q.CodeLoaded s1.mem →
      Steps P s1 sfP →
      sfP.status = .Running →
      ∃ sf : State,
        Steps P s1 sf ∧
        VmPreserved s1 sf ∧
        AllocCallPreserved s1 sf ∧
        (sf' = ProofLib.stripS (ProofLib.progKeep Q) sf ∨ sf = sfP) := by
  rcases h_c256 with ⟨f_c256, hfC, hfOkC⟩
  intro P Q
  have hkp : ProofLib.progKeep Q = ProofLib.progKeep P := rfl
  induction hsteps with
  | refl =>
    intro s1 _ hs1 _ _ _ _
    exact ⟨s1, .refl s1, VmPreserved.refl s1, allocCallPreserved_refl s1, Or.inl hs1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 sfP hsa hperm1 hL1 hstepsP hrun_sfP
    cases hstepsP with
    | refl =>
      exact ⟨s1, .refl s1, VmPreserved.refl s1, allocCallPreserved_refl s1, Or.inr rfl⟩
    | @step _ s2P _ h1_P hrest_P =>
      have hr2P : s2P.status = .Running := steps_start_running_vm hrest_P hrun_sfP
      have hrb' : sb'.status = .Running := steps_start_running_vm hrest hrun_f
      subst hsa
      cases h1 with
      | halt_unmapped _ _ _ => cases s1; cases hrb'
      | extern_fault _ _ _ => cases s1; cases hrb'
      | extern hr1' he _ _ =>
        have hr1 : s1.status = .Running := by cases s1; exact hr1'
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := by cases s1; rfl
        rw [hpc_eq] at he
        rcases blockProgram_hmacCompressOnlyExcHooksSat_externAt?_cases hfC he with
          htrap | ⟨rfl, heP⟩
        · rw [htrap] at hrb'; cases hrb'
        · obtain ⟨hs2P, hkf1, hsym1⟩ := step_P_extern_eq_vm h1_P hr2P heP
          rw [hs2P] at hrest_P
          have hstepP := Step.extern hr1 heP hkf1 hsym1
          rw [hkp] at hrb' ⊢
          obtain ⟨hc_eq, hvm1, hacp1⟩ := coupledCompress256_running_step hfOkC hperm1 hrb'
          have hperm2 : ∀ a, (f_c256 s1).mem.perm a = m₀.perm a :=
            fun a => (hvm1.perm_eq a).trans (hperm1 a)
          obtain ⟨sf, hsteps_rest, hvm_rest, hacp_rest, hor⟩ :=
            ih hrun_f (f_c256 s1) sfP (by rw [hkp]; exact hc_eq) hperm2
              (hL1.of_keepsFrozen hkf1) hrest_P hrun_sfP
          rw [hkp] at hor
          exact ⟨sf, .step hstepP hsteps_rest, hvm1.trans hvm_rest,
            allocCallPreserved_trans hacp1 hacp_rest, hor⟩
      | @exec inst hr1' hfe' =>
        have hr1 : s1.status = .Running := by cases s1; exact hr1'
        have hL1' : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
          strip_codeLoaded_of_keep_vm hL1
        have hexec' : Q.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
          strip_execOnlyIn_of_keep_vm Q s1.mem
        have hnsvc0 : inst.isSvc0 = false := by
          simpa using Program.fetchMem_of_allInstrs hall_svc hL1' hexec' _ inst hfe'
        have hnmsr : inst.isMsrTpidrEl0 = false := by
          simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
        have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
          have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := by cases s1; rfl
          have hmem_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).mem =
              ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem := by cases s1; rfl
          rw [hpc_eq, hmem_eq] at hfe'
          unfold Program.fetchMem at hfe' ⊢
          have his : (Q.externAt? s1.pc).isSome = (P.externAt? s1.pc).isSome :=
            blockProgram_hmacCompressOnlyExcHooksSat_externAt?_isSome lib pl i F H
              m₀ (ProofLib.progKeep P) s1.pc
          rw [his] at hfe'
          cases heP : (P.externAt? s1.pc).isSome
          · simp only [heP, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
            by_cases hal_pc : s1.pc.toNat % 4 = 0
            · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
              split at hfe'
              · contradiction
              · rename_i hce'
                have hce : s1.mem.canExec s1.pc 4 = true := by
                  simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
                  unfold Memory.canExec at hce' ⊢
                  rw [Memory.allPerm_iff] at hce' ⊢
                  intro k hk
                  have hxk := hce' k hk
                  rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
                have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem).read32 s1.pc =
                    s1.mem.read32 s1.pc := by simp [Memory.read32, ProofLib.strip_read8]
                rw [hr32] at hfe'
                simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                exact hfe'
            · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
          · simp only [heP, ↓reduceIte] at hfe'; contradiction
        have hev_Q : Q.evalInst inst (ProofLib.stripS (ProofLib.progKeep Q) s1) =
            ProofLib.stripS (ProofLib.progKeep Q) (execInst inst s1) := by
          rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
        have hs2P := step_P_exec_eq_vm h1_P hfe_P hnsvc0
        rw [hs2P] at hrest_P
        have hstep_P : Step P s1 (execInst inst s1) := by
          have := Step.exec (prog := P) hr1 hfe_P
          rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
        have hLQ_next : Q.CodeLoaded (execInst inst s1).mem := hstep_P.codeLoaded hL1
        have hbo1 := ProofLib.execInst_brk_oracle_of_not_isSvc0 hnsvc0 s1
        have hnsp1 := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1
        have htp1 := Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1
        have hvm1 := hnsp1.toVmPreserved htp1
        have hperm2 : ∀ a, (execInst inst s1).mem.perm a = m₀.perm a :=
          fun a => (hvm1.perm_eq a).trans (hperm1 a)
        obtain ⟨sf, hsteps_rest, hvm_rest, hacp_rest, hor⟩ :=
          ih hrun_f (execInst inst s1) sfP hev_Q hperm2 hLQ_next hrest_P hrun_sfP
        have hacp1 : AllocCallPreserved s1 (execInst inst s1) :=
          ⟨hbo1.2.2.2.2.2, hnsp1.1, hbo1.1, htp1, hbo1.2.2.1,
            execInst_projOracle_of_not_isSvc0 hnsvc0 s1, hstep_P.symtab_eq⟩
        exact ⟨sf, .step hstep_P hsteps_rest, hvm1.trans hvm_rest,
          allocCallPreserved_trans hacp1 hacp_rest, hor⟩

theorem runsTo_block_lift_vm_compress_only_sat [LibsignalPlacement] {blkLib : PlacedLib}
    {i : Nat} {F : ShaCompress} {H : LibsignalHooks}
    (h_c256 : HookSatCompress256 H lsCompress256Sym F)
    (hlib : blkLib = libsignalSessionLib.blockLib i)
    (hchk_svc : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib.text = true := by rfl)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true := by rfl)
    {s : State} {PostP PostQ : State → Prop}
    (hL : (libsignalSessionLib.blockProgram lsmpl i H).CodeLoaded s.mem)
    (hrunsP : RunsTo (libsignalSessionLib.blockProgram lsmpl i H) s PostP)
    (hrunsQ : RunsTo
      (libsignalSessionLib.blockProgram lsmpl i
        (hmacCompressOnlyExcHooksSat F H s.mem
          (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl i H))))
      (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl i
          (hmacCompressOnlyExcHooksSat F H s.mem
            (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl i H))))) s) PostQ)
    (hPostP_run : ∀ s', PostP s' → s'.status = .Running)
    (hPostQ_run : ∀ s', PostQ s' → s'.status = .Running) :
    let kp := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl i H)
    let Q := libsignalSessionLib.blockProgram lsmpl i (hmacCompressOnlyExcHooksSat F H s.mem kp)
    ∃ sf : State,
      Steps (libsignalSessionLib.blockProgram lsmpl i H) s sf ∧
      VmPreserved s sf ∧
      AllocCallPreserved s sf ∧
      sf.trace = s.trace ∧
      calleeSavedVRegs sf = calleeSavedVRegs s ∧
      (PostQ (ProofLib.stripS (ProofLib.progKeep Q) sf) ∨ PostP sf) := by
  subst hlib
  intro kp Q
  have hall_svc : Q.allInstrs (fun ins => !ins.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 libsignalSessionLib lsmpl i hchk_svc
  have hall_msr : Q.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true :=
    blockProgram_allInstrs_not_isMsrTpidrEl0 libsignalSessionLib lsmpl i
      (hmacCompressOnlyExcHooksSat F H s.mem kp) hchk_msr
  have hLQ : Q.CodeLoaded s.mem := hL.of_base_code rfl rfl
  have hLQ_strip : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s).mem := by
    have hm : (ProofLib.stripS (ProofLib.progKeep Q) s).mem =
        ProofLib.stripExecOutside (ProofLib.progKeep Q) s.mem := by cases s; rfl
    rw [hm]; exact strip_codeLoaded_of_keep_vm hLQ
  obtain ⟨sfP, hstepsP, htrP, hvregsP, hPostP, _⟩ := hrunsP hL
  obtain ⟨sf', hstepsQ, htr', hvregs', hPost', _⟩ := hrunsQ hLQ_strip
  obtain ⟨sf, hsteps_out, hvm, hacp, hsf_eq | rfl⟩ :=
    steps_hmacCompressOnlyExcSat_lift_strip_allocVm libsignalSessionLib lsmpl i h_c256 s.mem
      hall_svc hall_msr hstepsQ (hPostQ_run sf' hPost') s sfP rfl (fun _ => rfl) hLQ hstepsP
      (hPostP_run sfP hPostP)
  · have htr : sf.trace = s.trace := by
      have h1 : sf'.trace = sf.trace := by rw [hsf_eq]; cases sf; rfl
      have h2 : (ProofLib.stripS (ProofLib.progKeep Q) s).trace = s.trace := by cases s; rfl
      exact h1.symm.trans (htr'.trans h2)
    have hvregs : calleeSavedVRegs sf = calleeSavedVRegs s := by
      have h1 : calleeSavedVRegs sf' = calleeSavedVRegs sf := by
        rw [hsf_eq]; cases sf; rfl
      have h2 : calleeSavedVRegs (ProofLib.stripS (ProofLib.progKeep Q) s) = calleeSavedVRegs s := by
        cases s; rfl
      exact h1.symm.trans (hvregs'.trans h2)
    exact ⟨sf, hsteps_out, hvm, hacp, htr, hvregs, Or.inl (hsf_eq ▸ hPost')⟩
  · exact ⟨sf, hsteps_out, hvm, hacp, htrP, hvregsP, Or.inr hPostP⟩

/-! ### 5b. `hmacNoMemsetExcHooksSat` (`memcpy` + `compress256` Segments) -/

@[expose] def hmacNoMemsetExcHooksSat [LibsignalPlacement] (F : ShaCompress)
    (H : LibsignalHooks) (m₀ : Memory) (kp : BitVec 64 → Bool) : LibsignalHooks :=
  fun n =>
    if n = lsMemcpySym then (H lsMemcpySym).map (fun f_mc => coupledMemcpy f_mc m₀ kp)
    else if n = lsCompress256Sym then
      (H lsCompress256Sym).map (fun f_c256 => coupledCompress256 f_c256 F m₀ kp)
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

theorem hmacNoMemsetExcHooksSat_memcpy [LibsignalPlacement] {F : ShaCompress} {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym) (m₀ : Memory) (kp : BitVec 64 → Bool) :
    HookSatExactMemcpy (hmacNoMemsetExcHooksSat F H m₀ kp) lsMemcpySym := by
  rcases h_mc with ⟨f_mc, hfH, hfEx⟩
  exact ⟨coupledMemcpy f_mc m₀ kp, by simp [hmacNoMemsetExcHooksSat, hfH],
    coupledMemcpy_exact hfEx m₀ kp⟩

theorem hmacNoMemsetExcHooksSat_compress [LibsignalPlacement] {F : ShaCompress} {H : LibsignalHooks}
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) (m₀ : Memory) (kp : BitVec 64 → Bool) :
    HookSatCompress256 (hmacNoMemsetExcHooksSat F H m₀ kp) lsCompress256Sym F := by
  rcases h_c256 with ⟨f_c256, hfH, hfOk⟩
  have hne : lsCompress256Sym ≠ lsMemcpySym := by decide
  exact ⟨coupledCompress256 f_c256 F m₀ kp,
    by simp [hmacNoMemsetExcHooksSat, hne, hfH],
    coupledCompress256_ok hfOk m₀ kp⟩

private theorem hmacNoMemsetExcHooksSat_isSome [LibsignalPlacement] (F : ShaCompress)
    (H : LibsignalHooks) (m₀ : Memory) (kp : BitVec 64 → Bool) (n : String) :
    (hmacNoMemsetExcHooksSat F H m₀ kp n).isSome = (H n).isSome := by
  unfold hmacNoMemsetExcHooksSat
  have hne : lsCompress256Sym ≠ lsMemcpySym := by decide
  by_cases h1 : n = lsMemcpySym
  · subst h1; simp
  · by_cases h2 : n = lsCompress256Sym <;> simp [h1, h2, hne]

private theorem blockProgram_hmacNoMemsetExcHooksSat_externAt?_isSome [LibsignalPlacement]
    (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    (F : ShaCompress) (H : LibsignalHooks) (m₀ : Memory) (kp : BitVec 64 → Bool)
    (pc : BitVec 64) :
    ((lib.blockProgram pl i (hmacNoMemsetExcHooksSat F H m₀ kp)).externAt? pc).isSome =
      ((lib.blockProgram pl i H).externAt? pc).isSome := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program
  dsimp only
  rw [option_or_isSome_vm, option_or_isSome_vm]
  rw [findSome?_isSome_congr_vm _
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then
        hmacNoMemsetExcHooksSat F H m₀ kp x.1
      else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then H x.1 else none)]
  intro x
  cases h : (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) <;>
    simp [hmacNoMemsetExcHooksSat_isSome]

private theorem findSome?_hmacNoMemsetExcHooksSat_cases [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} {f_mc f_c256 : State → State}
    (h_mc : H lsMemcpySym = some f_mc)
    (h_c256 : H lsCompress256Sym = some f_c256)
    (m₀ : Memory) (kp : BitVec 64 → Bool) :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then hmacNoMemsetExcHooksSat F H m₀ kp n else none) =
        some f →
      (∀ s, (f s).status = .Exception "ext") ∨
      (f = coupledMemcpy f_mc m₀ kp ∧
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f_mc) ∨
      (f = coupledCompress256 f_c256 F m₀ kp ∧
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f_c256)
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons] at h ⊢
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_hmacNoMemsetExcHooksSat_cases h_mc h_c256 m₀ kp tl h
    · simp only [ho, ↓reduceIte] at h ⊢
      unfold hmacNoMemsetExcHooksSat at h
      by_cases h1 : n = lsMemcpySym
      · subst h1; simp only [↓reduceIte, h_mc, Option.map, Option.some.injEq] at h; subst h
        rw [h_mc]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · by_cases h2 : n = lsCompress256Sym
        · subst h2; simp only [h1, ↓reduceIte, h_c256, Option.map, Option.some.injEq] at h; subst h
          rw [h_c256]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · simp only [h1, h2, ↓reduceIte] at h
          cases hHn : H n with
          | none =>
            rw [hHn] at h; dsimp only [Option.map] at h ⊢
            exact findSome?_hmacNoMemsetExcHooksSat_cases h_mc h_c256 m₀ kp tl h
          | some _ =>
            rw [hHn] at h; simp only [Option.map, Option.some.injEq] at h; subst h
            exact Or.inl fun s => by cases s; rfl

private theorem blockProgram_hmacNoMemsetExcHooksSat_externAt?_cases [LibsignalPlacement]
    {lib : MultiPlacedLib} {pl : MultiPlacement} {i : Nat}
    {F : ShaCompress} {H : LibsignalHooks} {f_mc f_c256 : State → State}
    (h_mc : H lsMemcpySym = some f_mc)
    (h_c256 : H lsCompress256Sym = some f_c256)
    {m₀ : Memory} {kp : BitVec 64 → Bool}
    {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram pl i (hmacNoMemsetExcHooksSat F H m₀ kp)).externAt? pc = some f) :
    (∀ s, (f s).status = .Exception "ext") ∨
    (f = coupledMemcpy f_mc m₀ kp ∧ (lib.blockProgram pl i H).externAt? pc = some f_mc) ∨
    (f = coupledCompress256 f_c256 F m₀ kp ∧ (lib.blockProgram pl i H).externAt? pc = some f_c256) := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program at h ⊢
  dsimp only at h ⊢
  have hnone : ∀ (l : List (String × Nat)),
      (l.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro l; induction l with | nil => rfl | cons _ _ ih => exact ih
  simp only [ite_self, hnone, Option.or_none] at h ⊢
  exact findSome?_hmacNoMemsetExcHooksSat_cases h_mc h_c256 m₀ kp _ h

theorem steps_hmacNoMemsetExcSat_lift_strip_allocVm [LibsignalPlacement]
    (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    {F : ShaCompress} {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F)
    (m₀ : Memory)
    (hall_svc :
      (lib.blockProgram pl i
        (hmacNoMemsetExcHooksSat F H m₀ (ProofLib.progKeep (lib.blockProgram pl i H)))).allInstrs
      (fun ins => !ins.isSvc0) = true)
    (hall_msr :
      (lib.blockProgram pl i
        (hmacNoMemsetExcHooksSat F H m₀ (ProofLib.progKeep (lib.blockProgram pl i H)))).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true)
    {s1' sf' : State}
    (hsteps : Steps
      (lib.blockProgram pl i
        (hmacNoMemsetExcHooksSat F H m₀ (ProofLib.progKeep (lib.blockProgram pl i H)))) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let P := lib.blockProgram pl i H
    let Q := lib.blockProgram pl i (hmacNoMemsetExcHooksSat F H m₀ (ProofLib.progKeep P))
    ∀ (s1 sfP : State),
      s1' = ProofLib.stripS (ProofLib.progKeep Q) s1 →
      (∀ a, s1.mem.perm a = m₀.perm a) →
      Q.CodeLoaded s1.mem →
      Steps P s1 sfP →
      sfP.status = .Running →
      ∃ sf : State,
        Steps P s1 sf ∧
        VmPreserved s1 sf ∧
        AllocCallPreserved s1 sf ∧
        (sf' = ProofLib.stripS (ProofLib.progKeep Q) sf ∨ sf = sfP) := by
  rcases h_mc with ⟨f_mc, hfH, hfEx⟩
  rcases h_c256 with ⟨f_c256, hfC, hfOkC⟩
  intro P Q
  have hkp : ProofLib.progKeep Q = ProofLib.progKeep P := rfl
  induction hsteps with
  | refl =>
    intro s1 _ hs1 _ _ _ _
    exact ⟨s1, .refl s1, VmPreserved.refl s1, allocCallPreserved_refl s1, Or.inl hs1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 sfP hsa hperm1 hL1 hstepsP hrun_sfP
    cases hstepsP with
    | refl =>
      exact ⟨s1, .refl s1, VmPreserved.refl s1, allocCallPreserved_refl s1, Or.inr rfl⟩
    | @step _ s2P _ h1_P hrest_P =>
      have hr2P : s2P.status = .Running := steps_start_running_vm hrest_P hrun_sfP
      have hrb' : sb'.status = .Running := steps_start_running_vm hrest hrun_f
      subst hsa
      cases h1 with
      | halt_unmapped _ _ _ => cases s1; cases hrb'
      | extern_fault _ _ _ => cases s1; cases hrb'
      | extern hr1' he _ _ =>
        have hr1 : s1.status = .Running := by cases s1; exact hr1'
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := by cases s1; rfl
        rw [hpc_eq] at he
        rcases blockProgram_hmacNoMemsetExcHooksSat_externAt?_cases hfH hfC he with
          htrap | ⟨rfl, heP⟩ | ⟨rfl, heP⟩
        · rw [htrap] at hrb'; cases hrb'
        · obtain ⟨hs2P, hkf1, hsym1⟩ := step_P_extern_eq_vm h1_P hr2P heP
          rw [hs2P] at hrest_P
          have hstepP := Step.extern hr1 heP hkf1 hsym1
          rw [hkp] at hrb' ⊢
          obtain ⟨hc_eq, hvm1, hacp1⟩ := coupledMemcpy_running_step hfEx hperm1 hrb'
          have hperm2 : ∀ a, (f_mc s1).mem.perm a = m₀.perm a :=
            fun a => (hvm1.perm_eq a).trans (hperm1 a)
          obtain ⟨sf, hsteps_rest, hvm_rest, hacp_rest, hor⟩ :=
            ih hrun_f (f_mc s1) sfP (by rw [hkp]; exact hc_eq) hperm2
              (hL1.of_keepsFrozen hkf1) hrest_P hrun_sfP
          rw [hkp] at hor
          exact ⟨sf, .step hstepP hsteps_rest, hvm1.trans hvm_rest,
            allocCallPreserved_trans hacp1 hacp_rest, hor⟩
        · obtain ⟨hs2P, hkf1, hsym1⟩ := step_P_extern_eq_vm h1_P hr2P heP
          rw [hs2P] at hrest_P
          have hstepP := Step.extern hr1 heP hkf1 hsym1
          rw [hkp] at hrb' ⊢
          obtain ⟨hc_eq, hvm1, hacp1⟩ := coupledCompress256_running_step hfOkC hperm1 hrb'
          have hperm2 : ∀ a, (f_c256 s1).mem.perm a = m₀.perm a :=
            fun a => (hvm1.perm_eq a).trans (hperm1 a)
          obtain ⟨sf, hsteps_rest, hvm_rest, hacp_rest, hor⟩ :=
            ih hrun_f (f_c256 s1) sfP (by rw [hkp]; exact hc_eq) hperm2
              (hL1.of_keepsFrozen hkf1) hrest_P hrun_sfP
          rw [hkp] at hor
          exact ⟨sf, .step hstepP hsteps_rest, hvm1.trans hvm_rest,
            allocCallPreserved_trans hacp1 hacp_rest, hor⟩
      | @exec inst hr1' hfe' =>
        have hr1 : s1.status = .Running := by cases s1; exact hr1'
        have hL1' : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
          strip_codeLoaded_of_keep_vm hL1
        have hexec' : Q.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
          strip_execOnlyIn_of_keep_vm Q s1.mem
        have hnsvc0 : inst.isSvc0 = false := by
          simpa using Program.fetchMem_of_allInstrs hall_svc hL1' hexec' _ inst hfe'
        have hnmsr : inst.isMsrTpidrEl0 = false := by
          simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
        have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
          have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := by cases s1; rfl
          have hmem_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).mem =
              ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem := by cases s1; rfl
          rw [hpc_eq, hmem_eq] at hfe'
          unfold Program.fetchMem at hfe' ⊢
          have his : (Q.externAt? s1.pc).isSome = (P.externAt? s1.pc).isSome :=
            blockProgram_hmacNoMemsetExcHooksSat_externAt?_isSome lib pl i F H
              m₀ (ProofLib.progKeep P) s1.pc
          rw [his] at hfe'
          cases heP : (P.externAt? s1.pc).isSome
          · simp only [heP, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
            by_cases hal_pc : s1.pc.toNat % 4 = 0
            · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
              split at hfe'
              · contradiction
              · rename_i hce'
                have hce : s1.mem.canExec s1.pc 4 = true := by
                  simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
                  unfold Memory.canExec at hce' ⊢
                  rw [Memory.allPerm_iff] at hce' ⊢
                  intro k hk
                  have hxk := hce' k hk
                  rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
                have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem).read32 s1.pc =
                    s1.mem.read32 s1.pc := by simp [Memory.read32, ProofLib.strip_read8]
                rw [hr32] at hfe'
                simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                exact hfe'
            · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
          · simp only [heP, ↓reduceIte] at hfe'; contradiction
        have hev_Q : Q.evalInst inst (ProofLib.stripS (ProofLib.progKeep Q) s1) =
            ProofLib.stripS (ProofLib.progKeep Q) (execInst inst s1) := by
          rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
        have hs2P := step_P_exec_eq_vm h1_P hfe_P hnsvc0
        rw [hs2P] at hrest_P
        have hstep_P : Step P s1 (execInst inst s1) := by
          have := Step.exec (prog := P) hr1 hfe_P
          rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
        have hLQ_next : Q.CodeLoaded (execInst inst s1).mem := hstep_P.codeLoaded hL1
        have hbo1 := ProofLib.execInst_brk_oracle_of_not_isSvc0 hnsvc0 s1
        have hnsp1 := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1
        have htp1 := Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1
        have hvm1 := hnsp1.toVmPreserved htp1
        have hperm2 : ∀ a, (execInst inst s1).mem.perm a = m₀.perm a :=
          fun a => (hvm1.perm_eq a).trans (hperm1 a)
        obtain ⟨sf, hsteps_rest, hvm_rest, hacp_rest, hor⟩ :=
          ih hrun_f (execInst inst s1) sfP hev_Q hperm2 hLQ_next hrest_P hrun_sfP
        have hacp1 : AllocCallPreserved s1 (execInst inst s1) :=
          ⟨hbo1.2.2.2.2.2, hnsp1.1, hbo1.1, htp1, hbo1.2.2.1,
            execInst_projOracle_of_not_isSvc0 hnsvc0 s1, hstep_P.symtab_eq⟩
        exact ⟨sf, .step hstep_P hsteps_rest, hvm1.trans hvm_rest,
          allocCallPreserved_trans hacp1 hacp_rest, hor⟩

theorem runsTo_block_lift_vm_no_memset_sat [LibsignalPlacement] {blkLib : PlacedLib}
    {i : Nat} {F : ShaCompress} {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F)
    (hlib : blkLib = libsignalSessionLib.blockLib i)
    (hchk_svc : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib.text = true := by rfl)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true := by rfl)
    {s : State} {PostP PostQ : State → Prop}
    (hL : (libsignalSessionLib.blockProgram lsmpl i H).CodeLoaded s.mem)
    (hrunsP : RunsTo (libsignalSessionLib.blockProgram lsmpl i H) s PostP)
    (hrunsQ : RunsTo
      (libsignalSessionLib.blockProgram lsmpl i
        (hmacNoMemsetExcHooksSat F H s.mem
          (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl i H))))
      (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl i
          (hmacNoMemsetExcHooksSat F H s.mem
            (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl i H))))) s) PostQ)
    (hPostP_run : ∀ s', PostP s' → s'.status = .Running)
    (hPostQ_run : ∀ s', PostQ s' → s'.status = .Running) :
    let kp := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl i H)
    let Q := libsignalSessionLib.blockProgram lsmpl i (hmacNoMemsetExcHooksSat F H s.mem kp)
    ∃ sf : State,
      Steps (libsignalSessionLib.blockProgram lsmpl i H) s sf ∧
      VmPreserved s sf ∧
      AllocCallPreserved s sf ∧
      sf.trace = s.trace ∧
      calleeSavedVRegs sf = calleeSavedVRegs s ∧
      (PostQ (ProofLib.stripS (ProofLib.progKeep Q) sf) ∨ PostP sf) := by
  subst hlib
  intro kp Q
  have hall_svc : Q.allInstrs (fun ins => !ins.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 libsignalSessionLib lsmpl i hchk_svc
  have hall_msr : Q.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true :=
    blockProgram_allInstrs_not_isMsrTpidrEl0 libsignalSessionLib lsmpl i
      (hmacNoMemsetExcHooksSat F H s.mem kp) hchk_msr
  have hLQ : Q.CodeLoaded s.mem := hL.of_base_code rfl rfl
  have hLQ_strip : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s).mem := by
    have hm : (ProofLib.stripS (ProofLib.progKeep Q) s).mem =
        ProofLib.stripExecOutside (ProofLib.progKeep Q) s.mem := by cases s; rfl
    rw [hm]; exact strip_codeLoaded_of_keep_vm hLQ
  obtain ⟨sfP, hstepsP, htrP, hvregsP, hPostP, _⟩ := hrunsP hL
  obtain ⟨sf', hstepsQ, htr', hvregs', hPost', _⟩ := hrunsQ hLQ_strip
  obtain ⟨sf, hsteps_out, hvm, hacp, hsf_eq | rfl⟩ :=
    steps_hmacNoMemsetExcSat_lift_strip_allocVm libsignalSessionLib lsmpl i h_mc h_c256 s.mem
      hall_svc hall_msr hstepsQ (hPostQ_run sf' hPost') s sfP rfl (fun _ => rfl) hLQ hstepsP
      (hPostP_run sfP hPostP)
  · have htr : sf.trace = s.trace := by
      have h1 : sf'.trace = sf.trace := by rw [hsf_eq]; cases sf; rfl
      have h2 : (ProofLib.stripS (ProofLib.progKeep Q) s).trace = s.trace := by cases s; rfl
      exact h1.symm.trans (htr'.trans h2)
    have hvregs : calleeSavedVRegs sf = calleeSavedVRegs s := by
      have h1 : calleeSavedVRegs sf' = calleeSavedVRegs sf := by
        rw [hsf_eq]; cases sf; rfl
      have h2 : calleeSavedVRegs (ProofLib.stripS (ProofLib.progKeep Q) s) = calleeSavedVRegs s := by
        cases s; rfl
      exact h1.symm.trans (hvregs'.trans h2)
    exact ⟨sf, hsteps_out, hvm, hacp, htr, hvregs, Or.inl (hsf_eq ▸ hPost')⟩
  · exact ⟨sf, hsteps_out, hvm, hacp, htrP, hvregsP, Or.inr hPostP⟩

end LibsignalBinary.Proofs.ConsumeMessageKey.CoupledCompress256Sat

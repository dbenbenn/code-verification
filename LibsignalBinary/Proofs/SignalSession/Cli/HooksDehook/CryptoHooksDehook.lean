/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn

/-!
# Ghost `<EdwardsPoint as Neg>::neg` Hook, `lr`-Trap Suite, and 2-Step `pk1`/`pk2` Replays

Ghost-hook, `lr`-trap, and block-617 replay proofs for three linked crypto symbols:

1. `<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg`
   (`edwardsPointNegWords`, 57 words = 228 bytes, 0 B stack):
   - `edNegByteLen = 228`, `keepEdNeg`, `edNegRegion`, `edwardsPointNeg_all_safe` (`by decide`),
     `edNeg_regionWordsSafe`, `codeLoaded_pureWordsProg`, and `edNeg_codeLoaded_stripExecOutside`.
   - `edNegGhostHook`, `f3EmptyEdNegGhostHook`, and concrete `narrowEdNegGhostHook entryTarget`
     with unconditional `.fs`, `HookFsTraced IsFsC`, `.trace`, `VmPreserved`,
     `OomPreserved ∧ PoolPreserved`, `ExecFrozen`, `HookOk` lifts, `TrapHook L` instances,
     `edNeg_lr_trap_after_hook_ret`, and `narrowEdNegGhostHook_visitedIn`.
2. `<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk1` (`mlkemPk1Words`, 2 words)
   and `::pk2` (`mlkemPk2Words`, 2 words):
   - `TrapHook L` instances for `mlkemPk1Hook` and `mlkemPk2Hook`.
   - Direct 2-step `Step.exec` replay theorems `steps_mlkemPk1_of_hasWords` and
     `steps_mlkemPk2_of_hasWords` from `P_rx.CodeLoaded u.mem` and `P_rx.hasWords entry mlkemPk{1,2}Words`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CryptoHooksDehook

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (hasInstrs)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.E2E (u8Vec vecU8)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy (edNegHook mlkemPk1Hook mlkemPk2Hook)
open CryptoVerification.E2E.Pqxdh.Shared (cryptoLeafStubSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget FdsHiFrame VmPreserved OomPreserved PoolPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg (dalekEdNegVec)
open LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk (
  mlkemPk1Words mlkemPk1Instrs mlkemPk2Words mlkemPk2Instrs hasInstrs_of_hasWords
)
open LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg (
  edwardsPointNegWords edwardsPointNegUnstackedSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace ActiveRealPre ActiveRealRun
  linkedCallHook linkedCallHook_fs linkedCallHook_fsT linkedCallHook_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  linkedCallHook_activeRealPre_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg emptyStdProg_svc emptyStdProg_externAt_none
  f3LinkedCallHook_const_eq_linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapRegion keepBlock keepOf keepOf_singleton
  RegionWordsSafe RegionHasWords RegionCodeLoaded
  codeLoaded_stripExecOutside_of_keep
  TrapHook trapHook_linkedCallHook TrapEntryGuard
  checkWordsTrapSafe regionWordsSafe_single
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap (
  lr_trap_after_hook_ret
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (
  subroutineOutcome_running_pc_and_noFault
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode (
  EdNegStatePreserved masterEdNegSpec processEdNegSpec masterEdNegBudgetSpec
  pureWordsProg_edNeg_hasWords processEdNeg_pre_of_masterEdNeg_pre
  subroutine_ok_processEdNeg_of_hasWords
  edNegHook_vmPreserved edNegHook_preserves_oom_pool edNegHook_masterEdNeg_ok
  hookOk_edNegUnstackedFalse_of_master hookOk_edNegCryptoLeafStub_of_master
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_real_subroutine_run_visitedIn_of_stripS
)

/-! ## 1. `228` B `edwardsPointNeg` Region, `TrapSafeWords` & `pureWordsProg.CodeLoaded` -/

/-- Byte length (`228 = 4 * 57`) of `<EdwardsPoint as Neg>::neg` (`edwardsPointNegWords`). -/
@[expose] def edNegByteLen : Nat :=
  4 * edwardsPointNegWords.length

theorem edNegByteLen_eq : edNegByteLen = 228 := rfl

theorem four_mul_edwardsPointNegWords_length :
    4 * edwardsPointNegWords.length = edNegByteLen := rfl

/-- Kept-region byte predicate `[entry, entry + 228)` for `<EdwardsPoint as Neg>::neg`. -/
@[expose] def keepEdNeg (entry : BitVec 64) : BitVec 64 → Bool :=
  keepBlock entry edNegByteLen

theorem keepEdNeg_iff (entry pc : BitVec 64) :
    keepEdNeg entry pc = true ↔ (pc - entry).toNat < edNegByteLen := by
  simp [keepEdNeg, keepBlock, decide_eq_true_eq]

/-- Single-block `TrapRegion` for the 57-word `edwardsPointNegWords` block at `entry`. -/
@[expose] def edNegRegion (entry : BitVec 64) : TrapRegion :=
  [(entry, edwardsPointNegWords)]

theorem keepOf_edNegRegion (entry : BitVec 64) :
    keepOf (edNegRegion entry) = keepEdNeg entry := by
  funext pc
  dsimp only [edNegRegion]
  rw [keepOf_singleton, four_mul_edwardsPointNegWords_length]
  rfl

theorem keepOf_edNegRegion_apply (entry pc : BitVec 64) :
    keepOf (edNegRegion entry) pc = keepEdNeg entry pc :=
  congrFun (keepOf_edNegRegion entry) pc

private theorem readWordOff_bounds {P : Program} {off : Nat} {w : BitVec 32}
    (h : P.readWordOff off = some w) : off % 4 = 0 ∧ off + 3 < P.code.length := by
  unfold Program.readWordOff at h
  by_cases hmod : off % 4 = 0
  · simp only [hmod, ne_eq, not_true_eq_false, ↓reduceIte] at h
    rcases hd : P.code.drop off with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;>
      rw [hd] at h <;> try contradiction
    have hdl : (P.code.drop off).length = P.code.length - off := List.length_drop
    rw [hd] at hdl; simp only [List.length_cons] at hdl; exact ⟨hmod, by omega⟩
  · simp only [hmod, ne_eq, not_false_eq_true, ↓reduceIte] at h; contradiction

/-- Extract `(pureWordsProg addr words).CodeLoaded m` from any loaded parent program `P` holding
    non-empty `words` at `addr` (e.g. `f3TrialRxProg`). -/
theorem codeLoaded_pureWordsProg {P : Program} {m : Memory} {addr : BitVec 64}
    {words : List (BitVec 32)}
    (hP : P.CodeLoaded m) (hw : P.hasWords addr words) (hne : words ≠ []) :
    (pureWordsProg addr words).CodeLoaded m := by
  let off := (addr - P.base).toNat
  have hpos : 0 < words.length := List.length_pos_iff.mpr hne
  have hoff_al : off % 4 = 0 := (readWordOff_bounds (hw.2.1 0 hpos)).1
  have hlt_end : off + 4 * (words.length - 1) + 3 < P.code.length :=
    (readWordOff_bounds (hw.2.1 (words.length - 1) (by omega))).2
  have hoff_end : off + 4 * words.length ≤ P.code.length := by omega
  have hbase_al := hP.aligned
  have hno_wrap := hP.no_wrap
  have haddr_nat : addr.toNat = P.base.toNat + off := by
    have : off < P.code.length := by omega
    dsimp [off] at this ⊢; bv_omega
  have hclen : (pureWordsProg addr words).code.length = 4 * words.length :=
    Program.length_flatMap_wordToBytesLE words
  refine Program.CodeLoaded.intro (by change addr.toNat % 4 = 0; omega)
    (by change addr.toNat + (pureWordsProg addr words).code.length ≤ 2 ^ 64; omega) fun k hk => ?_
  rw [hclen] at hk
  have hkP : off + k < P.code.length := by omega
  have haddr_k : (pureWordsProg addr words).base + BitVec.ofNat 64 k =
      P.base + BitVec.ofNat 64 (off + k) := by
    change addr + BitVec.ofNat 64 k = P.base + BitVec.ofNat 64 (off + k)
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hc_eq : P.code[off + k] = (pureWordsProg addr words).code[k]'(hclen ▸ hk) := by
    have hq := Program.code_getElem?_of_hasWordsOff hw k hk
    rw [List.getElem?_eq_getElem hkP] at hq
    change some P.code[off + k] = (pureWordsProg addr words).code[k]? at hq
    rw [List.getElem?_eq_getElem (hclen ▸ hk)] at hq; exact Option.some.inj hq
  rw [haddr_k, ← hc_eq]
  exact ⟨hP.byte_eq (off + k) hkP, hP.perm_eq (off + k) hkP, hP.isLazyFree_eq (off + k) hkP⟩

theorem edNeg_codeLoaded_stripExecOutside {entry : BitVec 64} {mem : Memory}
    (hL : (pureWordsProg entry edwardsPointNegWords).CodeLoaded mem) :
    (pureWordsProg entry edwardsPointNegWords).CodeLoaded
      (ProofLib.stripExecOutside (keepEdNeg entry) mem) := by
  refine codeLoaded_stripExecOutside_of_keep (fun off hoff => ?_) hL
  have hclen : (pureWordsProg entry edwardsPointNegWords).code.length = edNegByteLen := by
    unfold pureWordsProg Program.ofWords; dsimp only; rw [Program.length_flatMap_wordToBytesLE]; rfl
  rw [hclen] at hoff
  change keepEdNeg entry (entry + BitVec.ofNat 64 off) = true
  rw [keepEdNeg_iff]
  have hsub : entry + BitVec.ofNat 64 off - entry = BitVec.ofNat 64 off := by bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [edNegByteLen_eq] at hoff; omega)]
  exact hoff

/-- Entry-state `lr` guard at `s0` for `edwardsPointNeg` stub replay. -/
@[expose] def CryptoEdNegEntryGuard (entry stubPc : BitVec 64) (s0 : State) : Prop :=
  keepEdNeg entry (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

theorem cryptoEdNegEntryGuard_iff_trapEntryGuard (entry stubPc : BitVec 64) (s0 : State) :
    CryptoEdNegEntryGuard entry stubPc s0 ↔ TrapEntryGuard (edNegRegion entry) stubPc s0 := by
  simp only [CryptoEdNegEntryGuard, TrapEntryGuard, keepOf_edNegRegion_apply]

/-! ## 2. Ghost `<EdwardsPoint as Neg>::neg` Hooks & Pointwise Suite -/

/-- Plain ghost `<EdwardsPoint as Neg>::neg` hook wrapping `masterEdNegSpec` with fallback
    `edNegHook dalekEdNegVec`. -/
@[expose] noncomputable def edNegGhostHook (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  linkedCallHook keep P_real P_sub entryTarget masterEdNegSpec (edNegHook dalekEdNegVec)

/-- `W`-independent `f3LinkedCallHook` form (`P_real := emptyStdProg`). -/
@[expose] noncomputable def f3EmptyEdNegGhostHook (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => masterEdNegSpec)
    (edNegHook dalekEdNegVec)

theorem f3EmptyEdNegGhostHook_eq (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) :
    f3EmptyEdNegGhostHook keep P_sub entryTarget =
      edNegGhostHook keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget masterEdNegSpec
    (edNegHook dalekEdNegVec)

/-- Concrete narrow `W`-independent ghost hook at `entryTarget` over `keepEdNeg entryTarget` and
    `pureWordsProg entryTarget edwardsPointNegWords`. -/
@[expose] noncomputable def narrowEdNegGhostHook (entryTarget : BitVec 64) : State → State :=
  f3EmptyEdNegGhostHook (keepEdNeg entryTarget)
    (pureWordsProg entryTarget edwardsPointNegWords) entryTarget

theorem specStripSInvariant_masterEdNeg (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterEdNegSpec where
  pre_eq := fun ⟨_, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specPreservesFsTrace_masterEdNeg : SpecPreservesFsTrace masterEdNegSpec := by
  intro ⟨_, _, _⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterEdNegSpec] at hpost; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.1, FsTraced.of_eq hpost.1.2.1 (congrArg FsState.files hpost.1.1)⟩
  · dsimp only [masterEdNegSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [masterEdNegSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [masterEdNegSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem masterEdNeg_pre_setPC
    (x : BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) (s : State) (pc : BitVec 64) :
    masterEdNegSpec.pre x (s.setPC pc) = masterEdNegSpec.pre x s := by
  rcases x with ⟨_, _, _⟩; cases s; rfl

theorem masterEdNeg_outcome_setPC
    (x : BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterEdNegSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterEdNegSpec x R s0 sf := by
  rcases x with ⟨_, _, _⟩; cases s0; cases sf; exact h

theorem keepFsTrace_edNegHook_eq
    (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160) (s0 : State) :
    keepFsTrace (edNegHook edNeg) s0 = edNegHook edNeg s0 := by
  cases s0; rfl

theorem keepFsTrace_edNegHook_master_ok :
    HookOk (keepFsTrace (edNegHook dalekEdNegVec)) masterEdNegSpec := by
  rw [funext (keepFsTrace_edNegHook_eq dalekEdNegVec)]
  exact edNegHook_masterEdNeg_ok

theorem edNegHook_preserves_execFrozen
    (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160)
    {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (edNegHook edNeg s0).mem := by
  unfold edNegHook returnToLinkRegister
  intro a
  simpa [Memory.perm_writeBytes] using hfr a

theorem subroutine_ok_masterEdNeg_of_process {P_sub : Program} {entryTarget : BitVec 64}
    (hsub_proc : subroutine_ok P_sub entryTarget processEdNegSpec) :
    subroutine_ok P_sub entryTarget masterEdNegSpec := by
  refine subroutine_ok_mono hsub_proc (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [processEdNegSpec, masterEdNegSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨EdNegStatePreserved.of_processFieldsPreserved hq.1, hq.2⟩

private theorem perm_eq_of_stripExecOutside_keepsFrozen {keep : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64, (stripExecOutside keep mf).perm a = (stripExecOutside keep m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  have hst := hstrip a
  rw [strip_perm, strip_perm] at hst
  have hfr0_a := hfr0 a
  have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a with
    | none =>
      cases hpf : mf.perm a with
      | none => rfl
      | some pf => rw [hp0, hpf] at hst; simp [Option.map] at hst
    | some p0 =>
      cases hpf : mf.perm a with
      | none => rw [hp0, hpf] at hst; simp [Option.map] at hst
      | some pf =>
        rw [hp0] at hfr0_a hfrozen0 hst; rw [hpf] at hfrf_a hst
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩; rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hst
        cases hk : keep a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;> simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem subroutineStop_of_processEdNegOutcome
    {x : BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome processEdNegSpec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩; rw [hret.2.2]; decide
  · dsimp only [processEdNegSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [processEdNegSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [processEdNegSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem activeRealRun_processEdNeg {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processEdNegSpec)
    {x : BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ masterEdNegSpec.pre x s0 ∗ R)
    (hReal : ActiveRealRun keep P_real P_sub entryTarget s0) :
    ProcessFieldsPreserved s0 (Classical.choose hReal.2.2.2) := by
  have hpre : s0.mem ⊨ processEdNegSpec.pre x s0 ∗ R := processEdNeg_pre_of_masterEdNeg_pre hpreM
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ processEdNegSpec.pre x s1 ∗ R := by rcases x with ⟨_, _, _⟩; cases s0; exact hpre
  have hs1'_pre : s1'.mem ⊨ processEdNegSpec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    have heq : processEdNegSpec.pre x s1' = processEdNegSpec.pre x s1 := by
      dsimp only [s1']; rcases x with ⟨_, _, _⟩; cases s1; rfl
    rwa [heq]
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hsub_proc x R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_processEdNegOutcome hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0) hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he) hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : Classical.choose hReal.2.2.2 = sf :=
    StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hdet]
  rcases hout' with ⟨_, _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [processEdNegSpec] at hpost'; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hproc' : ProcessFieldsPreserved s1' sf' := hpost'.1
    rw [hsf_eq] at hproc'
    have hperm : ∀ addr, sf.mem.perm addr = s0.mem.perm addr :=
      perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen
        hproc'.2.2.2.2.2.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hperm⟩
    · cases s0; cases sf; exact hproc'.1
    · cases s0; cases sf; exact hproc'.2.1
    · cases s0; cases sf; exact hproc'.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.2.2.2.1
  · dsimp only [processEdNegSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [processEdNegSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [processEdNegSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem vmPreserved_of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, FdsHiFrame.of_fs_eq h.1⟩

private theorem oomPoolPreserved_of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

theorem f3EmptyEdNegGhostHook_fs (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyEdNegGhostHook keep P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keep emptyStdProg P_sub entryTarget (fun _ _ => masterEdNegSpec)
    (edNegHook dalekEdNegVec) s0

theorem narrowEdNegGhostHook_fs (entryTarget : BitVec 64) (s0 : State) :
    (narrowEdNegGhostHook entryTarget s0).fs = s0.fs :=
  f3EmptyEdNegGhostHook_fs _ _ _ s0

theorem f3EmptyEdNegGhostHook_fsT (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyEdNegGhostHook keep P_sub entryTarget) :=
  f3LinkedCallHook_fsT keep emptyStdProg P_sub entryTarget (fun _ _ => masterEdNegSpec)
    (edNegHook dalekEdNegVec)

theorem narrowEdNegGhostHook_fsT (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (narrowEdNegGhostHook entryTarget) :=
  f3EmptyEdNegGhostHook_fsT _ _ _

theorem edNegGhostHook_preserves_execFrozen (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (edNegGhostHook keep P_real P_sub entryTarget s0).mem := by
  classical
  unfold edNegGhostHook linkedCallHook; split
  · split
    · rename_i _ hReal; exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · rw [keepFsTrace_edNegHook_eq]; exact edNegHook_preserves_execFrozen dalekEdNegVec hfr
  · exact hfr

theorem f3EmptyEdNegGhostHook_preserves_execFrozen (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (f3EmptyEdNegGhostHook keep P_sub entryTarget s0).mem := by
  rw [f3EmptyEdNegGhostHook_eq]
  exact edNegGhostHook_preserves_execFrozen keep emptyStdProg P_sub entryTarget hfr

theorem narrowEdNegGhostHook_preserves_execFrozen (entryTarget : BitVec 64) {s0 : State}
    (hfr : ExecFrozen s0.mem) :
    ExecFrozen (narrowEdNegGhostHook entryTarget s0).mem :=
  f3EmptyEdNegGhostHook_preserves_execFrozen _ _ _ hfr

section F3EmptyProcessPointwise

variable {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hsub_proc : subroutine_ok P_sub entryTarget processEdNegSpec)
include hsvc_sub hsub_no hsub_proc

theorem f3EmptyEdNegGhostHook_master_ok_of_process :
    HookOk (f3EmptyEdNegGhostHook keep P_sub entryTarget) masterEdNegSpec := by
  rw [f3EmptyEdNegGhostHook_eq]
  exact linkedCallHook_ok emptyStdProg_svc hsvc_sub
    (fun pc _ => emptyStdProg_externAt_none pc) hsub_no
    (subroutine_ok_masterEdNeg_of_process hsub_proc)
    (specStripSInvariant_masterEdNeg keep) specPreservesFsTrace_masterEdNeg
    masterEdNeg_pre_setPC masterEdNeg_outcome_setPC keepFsTrace_edNegHook_master_ok

theorem f3EmptyEdNegGhostHook_vmPreserved_of_process (s0 : State) :
    VmPreserved s0 (f3EmptyEdNegGhostHook keep P_sub entryTarget s0) := by
  classical
  rw [f3EmptyEdNegGhostHook_eq]
  unfold edNegGhostHook linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact vmPreserved_of_processFieldsPreserved
        (activeRealRun_processEdNeg emptyStdProg_svc hsvc_sub
          (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc hrun hsp hpre hReal)
    · rw [keepFsTrace_edNegHook_eq]; exact edNegHook_vmPreserved dalekEdNegVec s0
  · exact VmPreserved.refl s0

end F3EmptyProcessPointwise

private theorem pureWordsProg_edNeg_svc (entry : BitVec 64) :
    (pureWordsProg entry edwardsPointNegWords).svc = Syscall.standard := rfl

theorem narrowEdNegGhostHook_master_ok (entryTarget : BitVec 64) :
    HookOk (narrowEdNegGhostHook entryTarget) masterEdNegSpec :=
  f3EmptyEdNegGhostHook_master_ok_of_process
    (pureWordsProg_edNeg_svc entryTarget)
    (pureWordsProg_externAt_none entryTarget edwardsPointNegWords)
    (subroutine_ok_processEdNeg_of_hasWords
      (pureWordsProg_externAt_none entryTarget edwardsPointNegWords)
      (pureWordsProg_edNeg_hasWords entryTarget))

theorem narrowEdNegGhostHook_vmPreserved (entryTarget : BitVec 64) (s0 : State) :
    VmPreserved s0 (narrowEdNegGhostHook entryTarget s0) :=
  f3EmptyEdNegGhostHook_vmPreserved_of_process
    (pureWordsProg_edNeg_svc entryTarget)
    (pureWordsProg_externAt_none entryTarget edwardsPointNegWords)
    (subroutine_ok_processEdNeg_of_hasWords
      (pureWordsProg_externAt_none entryTarget edwardsPointNegWords)
      (pureWordsProg_edNeg_hasWords entryTarget)) s0

/-! ## 3. `TrapHook` Instances & Post-Hook `lr` Trap Corollaries -/

private theorem readReg64_lr_writeReg64_x0 (s : State) (v : BitVec 64) :
    (s.writeReg64 .x0 v).readReg64 .lr = s.readReg64 .lr := by
  simp [State.readReg64, State.writeReg64, RegFile.read, RegFile.write]

/-! ## 4. `StepsVisitedIn` Witness for `narrowEdNegGhostHook` & 2-Step `pk1`/`pk2` Replays -/

theorem f3EmptyEdNegGhostHook_visitedIn {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget edwardsPointNegWords) {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyEdNegGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptyEdNegGhostHook keep P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf_g ∧
      ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  classical
  rw [f3EmptyEdNegGhostHook_eq] at hnoex
  have hActPre : ActiveRealPre masterEdNegSpec u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS emptyStdProg_svc hsvc_sub
      (fun pc _ => emptyStdProg_externAt_none pc) hsub_no
      (subroutine_ok_masterEdNeg_of_process (subroutine_ok_processEdNeg_of_hasWords hsub_no hwords))
      (specStripSInvariant_masterEdNeg keep) specPreservesFsTrace_masterEdNeg
      masterEdNeg_pre_setPC masterEdNeg_outcome_setPC hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : f3EmptyEdNegGhostHook keep P_sub entryTarget u = sf := by
    rw [f3EmptyEdNegGhostHook_eq]
    unfold edNegGhostHook linkedCallHook; simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  dsimp only; rw [heq]; exact ⟨hvis, hfr_sf, hfs⟩

/-- Stock-safe `h2fsgen_StepsVisitedIn (keepEdNeg entryTarget) emptyStdProg` witness for
    `narrowEdNegGhostHook entryTarget` from any loaded parent program `P_rx` holding
    `edwardsPointNegWords` at `entryTarget` (e.g. `f3TrialRxProg`). -/
theorem narrowEdNegGhostHook_visitedIn {P_rx : Program} {entryTarget : BitVec 64} {u : State}
    (hCodeRx : P_rx.CodeLoaded u.mem)
    (hwordsRx : P_rx.hasWords entryTarget edwardsPointNegWords)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (narrowEdNegGhostHook entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keepEdNeg entryTarget (u.readReg64 .lr) = false) :
    let sf_g := narrowEdNegGhostHook entryTarget u
    h2fsgen_StepsVisitedIn (keepEdNeg entryTarget) emptyStdProg (u.setPC entryTarget) sf_g ∧
      ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs :=
  f3EmptyEdNegGhostHook_visitedIn
    (pureWordsProg_edNeg_svc entryTarget)
    (pureWordsProg_externAt_none entryTarget edwardsPointNegWords)
    (pureWordsProg_edNeg_hasWords entryTarget)
    hrun hnoex hFr hlr_out
    (edNeg_codeLoaded_stripExecOutside
      (codeLoaded_pureWordsProg hCodeRx hwordsRx (by decide)))

private theorem fetchMem_of_codeLoaded_hasInstrs {P_real P_rx : Program} {m : Memory}
    {base off : BitVec 64} {ls : List Instr} {inst : Instr} (i : Nat)
    (hCodeRx : P_rx.CodeLoaded m)
    (hins : hasInstrs P_rx base ls)
    (hno_rx : P_rx.externAt? (base + off) = none)
    (hno_real : P_real.externAt? (base + off) = none)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P_real.fetchMem m (base + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := hins.fetch_off i off hlt hoff
  rw [List.getElem?_eq_getElem hlt] at hi
  rw [Option.some.inj hi] at hf
  have hfm_rx : P_rx.fetchMem m (base + off) = some inst :=
    Program.fetchMem_of_fetch hCodeRx hf
  unfold Program.fetchMem at hfm_rx ⊢
  rw [hno_real]; rw [hno_rx] at hfm_rx
  exact hfm_rx

/-- Direct 2-step `Step.exec` replay (`add x0, x0, #0x900; ret`) on `P_real` producing
    `mlkemPk1Hook u` identically. -/
theorem steps_mlkemPk1_of_hasWords {P_real P_rx : Program} {entry : BitVec 64} {u : State}
    (hCodeRx : P_rx.CodeLoaded u.mem)
    (hwordsRx : P_rx.hasWords entry mlkemPk1Words)
    (hno_rx0 : P_rx.externAt? entry = none)
    (hno_rx4 : P_rx.externAt? (entry + 4#64) = none)
    (hno_real0 : P_real.externAt? entry = none)
    (hno_real4 : P_real.externAt? (entry + 4#64) = none)
    (hrun : u.status = .Running) :
    Steps P_real (u.setPC entry) (mlkemPk1Hook u) := by
  have hins : hasInstrs P_rx entry mlkemPk1Instrs := hasInstrs_of_hasWords hwordsRx
  have hz : entry + 0#64 = entry := by bv_omega
  have hfm0 : P_real.fetchMem (u.setPC entry).mem (u.setPC entry).pc =
      some (.addSubImm .W64 .ADD .x0 .x0 0x900#12 false) := by
    change P_real.fetchMem u.mem entry = _
    rw [← hz]
    exact fetchMem_of_codeLoaded_hasInstrs 0 hCodeRx hins (hz.symm ▸ hno_rx0) (hz.symm ▸ hno_real0)
  let s1 := P_real.evalInst (.addSubImm .W64 .ADD .x0 .x0 0x900#12 false) (u.setPC entry)
  have hstep1 : Step P_real (u.setPC entry) s1 := Step.exec hrun hfm0
  have hs1_eq : s1 = ((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 2304#64)).advancePC := by
    dsimp only [s1, Program.evalInst, execInstWithSvc, execAddSubImm]
    rw [evalAddSub_w64_add]
    cases u; rfl
  have hrun1 : s1.status = .Running := by rw [hs1_eq]; exact hrun
  have hfm1 : P_real.fetchMem s1.mem s1.pc = some (.ret .lr) := by
    rw [hs1_eq]
    change P_real.fetchMem u.mem (entry + 4#64) = some (.ret .lr)
    exact fetchMem_of_codeLoaded_hasInstrs 1 hCodeRx hins hno_rx4 hno_real4
  let s2 := P_real.evalInst (.ret .lr) s1
  have hstep2 : Step P_real s1 s2 := Step.exec hrun1 hfm1
  have hs2_eq : s2 = mlkemPk1Hook u := by
    dsimp only [s2]
    rw [hs1_eq]
    change (((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 2304#64)).advancePC).setPC
      (((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 2304#64)).advancePC.readReg64 .lr) =
      mlkemPk1Hook u
    have hlr : (((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 2304#64)).advancePC).readReg64 .lr =
        u.readReg64 .lr := by
      have h1 : (((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 2304#64)).advancePC).readReg64 .lr =
          ((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 2304#64)).readReg64 .lr := by
        cases u; rfl
      rw [h1, readReg64_lr_writeReg64_x0]
      cases u; rfl
    rw [hlr]
    unfold mlkemPk1Hook retHook
    cases u; rfl
  rw [hs2_eq] at hstep2
  exact Steps.step hstep1 (Steps.step hstep2 (Steps.refl _))

/-- Direct 2-step `Step.exec` replay (`add x0, x0, #0x480; ret`) on `P_real` producing
    `mlkemPk2Hook u` identically. -/
theorem steps_mlkemPk2_of_hasWords {P_real P_rx : Program} {entry : BitVec 64} {u : State}
    (hCodeRx : P_rx.CodeLoaded u.mem)
    (hwordsRx : P_rx.hasWords entry mlkemPk2Words)
    (hno_rx0 : P_rx.externAt? entry = none)
    (hno_rx4 : P_rx.externAt? (entry + 4#64) = none)
    (hno_real0 : P_real.externAt? entry = none)
    (hno_real4 : P_real.externAt? (entry + 4#64) = none)
    (hrun : u.status = .Running) :
    Steps P_real (u.setPC entry) (mlkemPk2Hook u) := by
  have hins : hasInstrs P_rx entry mlkemPk2Instrs := hasInstrs_of_hasWords hwordsRx
  have hz : entry + 0#64 = entry := by bv_omega
  have hfm0 : P_real.fetchMem (u.setPC entry).mem (u.setPC entry).pc =
      some (.addSubImm .W64 .ADD .x0 .x0 0x480#12 false) := by
    change P_real.fetchMem u.mem entry = _
    rw [← hz]
    exact fetchMem_of_codeLoaded_hasInstrs 0 hCodeRx hins (hz.symm ▸ hno_rx0) (hz.symm ▸ hno_real0)
  let s1 := P_real.evalInst (.addSubImm .W64 .ADD .x0 .x0 0x480#12 false) (u.setPC entry)
  have hstep1 : Step P_real (u.setPC entry) s1 := Step.exec hrun hfm0
  have hs1_eq : s1 = ((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 1152#64)).advancePC := by
    dsimp only [s1, Program.evalInst, execInstWithSvc, execAddSubImm]
    rw [evalAddSub_w64_add]
    cases u; rfl
  have hrun1 : s1.status = .Running := by rw [hs1_eq]; exact hrun
  have hfm1 : P_real.fetchMem s1.mem s1.pc = some (.ret .lr) := by
    rw [hs1_eq]
    change P_real.fetchMem u.mem (entry + 4#64) = some (.ret .lr)
    exact fetchMem_of_codeLoaded_hasInstrs 1 hCodeRx hins hno_rx4 hno_real4
  let s2 := P_real.evalInst (.ret .lr) s1
  have hstep2 : Step P_real s1 s2 := Step.exec hrun1 hfm1
  have hs2_eq : s2 = mlkemPk2Hook u := by
    dsimp only [s2]
    rw [hs1_eq]
    change (((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 1152#64)).advancePC).setPC
      (((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 1152#64)).advancePC.readReg64 .lr) =
      mlkemPk2Hook u
    have hlr : (((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 1152#64)).advancePC).readReg64 .lr =
        u.readReg64 .lr := by
      have h1 : (((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 1152#64)).advancePC).readReg64 .lr =
          ((u.setPC entry).writeReg64 .x0 (u.readReg64 .x0 + 1152#64)).readReg64 .lr := by
        cases u; rfl
      rw [h1, readReg64_lr_writeReg64_x0]
      cases u; rfl
    rw [hlr]
    unfold mlkemPk2Hook retHook
    cases u; rfl
  rw [hs2_eq] at hstep2
  exact Steps.step hstep1 (Steps.step hstep2 (Steps.refl _))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CryptoHooksDehook

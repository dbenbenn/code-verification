/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Spec.GlobalAlloc
public import ProofLib
public import LibsignalBinary.Heap.IfaceBudget
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop -- proof-setup: allow-public-import
import ProofLib.Hoare.Model
import ProofLib.SepLogic.WP.StepsProcess

/-!
# Pure-block `ProcessFieldsPreserved` lifting and `compress256` contract

Lifts standalone block execution to ambient programs while preserving `ProcessFieldsPreserved`
and `AllocCallPreserved`:

- `ProcessFieldsPreserved_toHeapVmPreserved`, `ProcessFieldsPreserved_toRustVmPreserved`.
- `stackAt_split_frame176`: splits and recombines `hookStack ≥ 176` without upper-bound hypotheses.
- `withPlacedCodeLoaded`, `SpecSimulates.withPlacedCodeLoaded`, `SpecSimulates.placedSubroutineOk`.
- `steps_lift_placed_process`: generic pure-block `ProcessFieldsPreserved` trace lift.
- `compress256MasterROSpec`, `compress256_master_ro_ok`, `compress256_master_ro_subroutineOk`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open LibsignalBinary.Heap (AllocCallPreserved FdsHiFrame)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (compress256Sym sha2K32Sym compress256Block compress256Lib compress256_code_eq
   compress256_tree_size compress256_program_noSvc compress256_program_noMsrTpidrEl0)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop
  (compress256RawROSpec compress256_fnAddr compress256_raw_ro_ok)

/-! ## 1. `ProcessFieldsPreserved` → `VmPreserved` & Stack Splitting -/

theorem ProcessFieldsPreserved_toHeapVmPreserved {s0 sf : State}
    (hpf : ProcessFieldsPreserved s0 sf) :
    LibsignalBinary.Heap.VmPreserved s0 sf :=
  ⟨⟨hpf.2.2.2.2.2.1, hpf.2.2.2.2.1, hpf.2.2.1⟩,
   hpf.2.2.2.2.2.2.1, hpf.2.2.2.2.2.2.2, FdsHiFrame.of_fs_eq hpf.1⟩

theorem ProcessFieldsPreserved_toRustVmPreserved {s0 sf : State}
    (hpf : ProcessFieldsPreserved s0 sf) :
    Arm64.Rust.VmPreserved s0 sf :=
  ⟨hpf.2.2.2.2.2.1, hpf.2.2.2.2.1, hpf.2.2.1, funext hpf.2.2.2.2.2.2.2⟩

theorem stackAt_le_two_pow_64 {m : Memory} {a sp : BitVec 64} {st : ShaState}
    {n : Nat} {R : SepProp}
    (h : m ⊨ (a ↦ₛ CryptoVerification.LibsignalHmac.shaStateBytes st) ∗ (stackAt sp n ∗ R)) :
    n ≤ 2 ^ 64 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · omega
  · rw [Sha256Math.pointsToBytes_shaStateBytes, sepConj_assoc] at h
    rw [sepConj_left_comm _ (stackAt sp n)] at h
    have hd := (IsBlock.pointsTo32 a (st.toList.getD 0 0#32)).disjoint
      (IsBlock.memRegion (sp - BitVec.ofNat 64 n) n) (by decide) hn h
    have hlt := (a - (sp - BitVec.ofNat 64 n)).isLt
    have h2 := hd.2
    omega

theorem stackAt_split_frame176 (s0 : State) {hookStack : Nat}
    (hle : 176 ≤ hookStack) (hmax : hookStack ≤ 2 ^ 64) :
    stackAt s0.sp hookStack =
      stackFrame s0 176 ∗ stackAt (s0.sp - 176#64) (hookStack - 176) := by
  have heq : hookStack = 176 + (hookStack - 176) := by omega
  have hmax' : 176 + (hookStack - 176) ≤ 2 ^ 64 := by omega
  conv => lhs; rw [heq]
  rw [stackAt_eq_stackFrameAt s0.sp (176 + (hookStack - 176)) hmax',
      stackFrameAt_split s0.sp 176 (hookStack - 176) hmax',
      ← stackAt_eq_stackFrameAt s0.sp 176 (by omega),
      ← stackAt_eq_stackFrameAt (s0.sp - BitVec.ofNat 64 176) (hookStack - 176) (by omega)]

/-! ## 2. `Obj.PlacedLib` `withPlacedCodeLoaded` & `SpecSimulates` Transport -/

/-- Adjoin `⌜(lib.program pl).CodeLoaded s0.mem⌝` to `spec.pre` (single-block `Obj.PlacedLib`
counterpart of `Obj.MultiPlacedLib.withCodeLoaded`). -/
@[expose] def withPlacedCodeLoaded {α : Type} (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜(lib.program pl).CodeLoaded s0.mem⌝ }

theorem SpecSimulates.withPlacedCodeLoaded {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) (lib : Obj.PlacedLib) (pl : Obj.Placement) :
    SpecSimulates (StepsLift.withPlacedCodeLoaded lib pl spec₁)
      (StepsLift.withPlacedCodeLoaded lib pl spec₂) := by
  intro y R s0 hpre
  dsimp only [StepsLift.withPlacedCodeLoaded] at hpre ⊢
  rw [sepConj_comm (spec₂.pre y s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre₂⟩ := hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre₂
  refine ⟨x, R₁, ?_, hm⟩
  rw [sepConj_comm (spec₁.pre x s0) ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl]
  exact hpre₁

theorem SpecSimulates.placedSubroutineOk {α β : Type} {lib : Obj.PlacedLib}
    {fnName : String} {spec₁ : Obj.Placement → Spec α}
    {spec₂ : Obj.Placement → Spec β}
    {externs : String → Option (State → State)}
    (hsim : ∀ pl, SpecSimulates (spec₁ pl) (spec₂ pl))
    (h : lib.subroutineOk fnName spec₁ externs) :
    lib.subroutineOk fnName spec₂ externs :=
  ⟨h.1, fun pl hpl => (hsim pl).subroutine_ok (h.2 pl hpl)⟩

/-! ## 3. Pure-Block `ProcessFieldsPreserved` Trace Lift -/

private theorem steps_start_running {P : Program} {s1 s2 : State}
    (h : Steps P s1 s2) (hrun2 : s2.status = .Running) : s1.status = .Running := by
  cases h with
  | refl => exact hrun2
  | step h1 _ => exact h1.running_of_step

theorem strip_execOnlyIn_prog (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (stripExecOutside (progKeep prog) m) := by
  intro addr hx
  exact of_decide_eq_true (strip_perm_x_imp hx).2

theorem strip_codeLoaded_prog {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside (progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_lin
  have hin : progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold progKeep
    rw [decide_eq_true_iff, hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hL.no_wrap; omega)]
    exact hi
  rw [strip_read8, strip_perm_of_keep hin, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

theorem steps_lift_placed_process_alloc {P R₀ : Program}
    (hext_blk : ∀ off : Nat, off < R₀.code.length →
      P.externAt? (R₀.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R₀.externAt? pc = none)
    (hsvc : R₀.allInstrs (fun i => !i.isSvc) = true)
    (hmsr : R₀.allInstrs (fun i => !i.isMsrTpidrEl0) = true)
    {s1' sf' : State} (hsteps : Steps R₀ s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = stripS (progKeep R₀) s1 → R₀.CodeLoaded s1.mem →
      ∃ sf : State, Steps P s1 sf ∧ sf' = stripS (progKeep R₀) sf ∧
        ProcessFieldsPreserved s1 sf ∧ AllocCallPreserved s1 sf := by
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, .refl s1, hs1, ProcessFieldsPreserved.refl s1,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R₀.CodeLoaded (stripS (progKeep R₀) s1).mem := strip_codeLoaded_prog hL1
      have hexec' : R₀.ExecOnlyIn (stripS (progKeep R₀) s1).mem := strip_execOnlyIn_prog R₀ s1.mem
      have hn_svc : (!inst.isSvc) = true :=
        Program.fetchMem_of_allInstrs hsvc hL1' hexec' _ inst hfe'
      have hn_msr : (!inst.isMsrTpidrEl0) = true :=
        Program.fetchMem_of_allInstrs hmsr hL1' hexec' _ inst hfe'
      have hsvc_f : inst.isSvc = false := by simpa using hn_svc
      have hmsr_f : inst.isMsrTpidrEl0 = false := by simpa using hn_msr
      have hsvc0_f : inst.isSvc0 = false := inst.isSvc0_eq_false_of_isSvc_eq_false hsvc_f
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (stripS (progKeep R₀) s1).pc = s1.pc := by cases s1; rfl
        have hmem_eq : (stripS (progKeep R₀) s1).mem = stripExecOutside (progKeep R₀) s1.mem := by
          cases s1; rfl
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
          split at hfe'
          · contradiction
          · rename_i hce'
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            have hkeep0 : progKeep R₀ s1.pc = true := by
              have hce0 := hce'
              unfold Memory.canExec at hce0
              rw [Memory.allPerm_iff] at hce0
              simpa only [BitVec.add_zero] using (strip_perm_x_imp (hce0 0 (by omega))).2
            have hoff_lt : (s1.pc - R₀.base).toNat < R₀.code.length :=
              of_decide_eq_true hkeep0
            have hpc_off : R₀.base + BitVec.ofNat 64 (s1.pc - R₀.base).toNat = s1.pc := by
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              bv_lin
            have hext_P_pc : P.externAt? s1.pc = none :=
              hpc_off ▸ hext_blk (s1.pc - R₀.base).toNat hoff_lt
            rw [hext_P_pc]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              hal_pc, ne_eq, not_true_eq_false]
            have hce : s1.mem.canExec s1.pc 4 = true := by
              unfold Memory.canExec at hce' ⊢
              rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk
              have hxk := hce' k hk
              rwa [strip_perm_of_keep (strip_perm_x_imp hxk).2] at hxk
            have hr32 : (stripExecOutside (progKeep R₀) s1.mem).read32 s1.pc =
                s1.mem.read32 s1.pc := by
              simp [Memory.read32, strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
          contradiction
      have hev_R : R₀.evalInst inst (stripS (progKeep R₀) s1) =
          stripS (progKeep R₀) (execInst inst s1) := by
        rw [evalInst_eq_execInst_of_not_isSvc0 hsvc0_f, execInst_stripS hsvc0_f]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [evalInst_eq_execInst_of_not_isSvc0 hsvc0_f] at this
      have hpf12 : ProcessFieldsPreserved s1 (execInst inst s1) :=
        execInst_preserves_processFields hsvc_f hmsr_f s1
      have hora12 : (execInst inst s1).oracle = s1.oracle := by
        let Pstd : Program := { code := [], base := 0, externs := fun _ => none, svc := Syscall.standard }
        rw [← evalInst_eq_execInst_of_not_isSvc0 (prog := Pstd) hsvc0_f]
        exact evalInst_oracle_of_standard (prog := Pstd) rfl inst s1
      have hacp12 : AllocCallPreserved s1 (execInst inst s1) :=
        ⟨hpf12.1, hpf12.2.1, hpf12.2.2.2.1, hpf12.2.2.1, hpf12.2.2.2.2.2.1,
         hora12, hstep_P.symtab_eq⟩
      obtain ⟨sf, hsteps_P, hsf_eq, hpf_rest, hacp_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      rcases hacp12 with ⟨a1, a2, a3, a4, a5, a6, a7⟩
      rcases hacp_rest with ⟨b1, b2, b3, b4, b5, b6, b7⟩
      exact ⟨sf, .step hstep_P hsteps_P, hsf_eq, hpf12.trans hpf_rest,
        ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7⟩⟩

theorem steps_lift_placed_process {P R₀ : Program}
    (hext_blk : ∀ off : Nat, off < R₀.code.length →
      P.externAt? (R₀.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R₀.externAt? pc = none)
    (hsvc : R₀.allInstrs (fun i => !i.isSvc) = true)
    (hmsr : R₀.allInstrs (fun i => !i.isMsrTpidrEl0) = true)
    {s1' sf' : State} (hsteps : Steps R₀ s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = stripS (progKeep R₀) s1 → R₀.CodeLoaded s1.mem →
      ∃ sf : State, Steps P s1 sf ∧ sf' = stripS (progKeep R₀) sf ∧
        ProcessFieldsPreserved s1 sf := by
  intro s1 hs1 hL1
  obtain ⟨sf, hstepsP, hsf_eq, hpf, _⟩ :=
    steps_lift_placed_process_alloc hext_blk hext_R hsvc hmsr hsteps hrun_f s1 hs1 hL1
  exact ⟨sf, hstepsP, hsf_eq, hpf⟩

/-! ## 4. Master `compress256` Contract & Lift Theorems -/

/-- Master RO contract for `sha2::sha256::compress256`, strengthening `compress256RawROSpec` with
full `ProcessFieldsPreserved s0 sf` and `AllocCallPreserved s0 sf`. -/
@[expose] def compress256MasterROSpec (k32 : BitVec 64) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := (compress256RawROSpec k32).pre
  post := fun x s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝ ∗
      (compress256RawROSpec k32).post x s0 sf

set_option maxRecDepth 400000 in
private theorem compress256_patched_length {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) :
    (compress256Lib.program pl).code.length = 7636 := by
  have hc : (compress256Lib.program pl).code = compress256Lib.text.patched pl := rfl
  rw [hc, Obj.CodeBlock.length_patched_of_aligned pl hpl.text.len_aligned,
      compress256_code_eq,
      ProofLib.ProgramReflection.WordTree.length_toBytes_of_checkSize? compress256_tree_size]

private theorem compress256_program_externAt?_none (pl : Obj.Placement)
    (externs : String → Option (State → State) := fun _ => none) (pc : BitVec 64) :
    (compress256Lib.program pl externs).externAt? pc = none := by
  simp [compress256Lib, compress256Block, Obj.PlacedLib.program, Program.externAt?, Program.hookAtOff?]

/-- Lift `compress256_raw_ro_ok` to any `P : Program` that places no hooks inside the `7,636`-byte
body of `compress256Lib` at `pl.base`, strengthening the postcondition to `compress256MasterROSpec`. -/
theorem compress256_master_ro_ok {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl)
    {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl (compress256MasterROSpec (pl.ρ sha2K32Sym))) := by
  let R₀ := compress256Lib.program pl
  let kp₀ := progKeep R₀
  have hsub := compress256_raw_ro_ok pl hpl
  rw [compress256_fnAddr pl] at hsub ⊢
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpc hrun hpre hsp _hLP
  dsimp only [withPlacedCodeLoaded, compress256MasterROSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hL0, hpre_raw⟩ := hpre
  let s0' := stripS kp₀ s0
  have hpre_mem : ∀ x (s : State) (m : Memory),
      (compress256RawROSpec (pl.ρ sha2K32Sym)).pre x (s.setMem m) =
        (compress256RawROSpec (pl.ρ sha2K32Sym)).pre x s := by
    rintro ⟨_, _, _, _, _⟩ s _; cases s; rfl
  have hpost_mem : ∀ x (s1 s2 : State) (m1 m2 : Memory),
      (compress256RawROSpec (pl.ρ sha2K32Sym)).post x (s1.setMem m1) (s2.setMem m2) =
        (compress256RawROSpec (pl.ρ sha2K32Sym)).post x s1 s2 := by
    rintro ⟨_, _, _, _, _⟩ s1 s2 _ _; cases s1; cases s2; rfl
  obtain ⟨R_view, hpre_view, hunstrip⟩ := strip_frame kp₀ hpre_raw
  have hpre' : s0'.mem ⊨ (compress256RawROSpec (pl.ρ sha2K32Sym)).pre (stA, st, blkA, bs, n) s0' ∗
      R_view := by
    dsimp [s0', stripS]
    rw [hpre_mem, State.mem_setMem]
    exact hpre_view
  obtain ⟨sf', hsteps', hout'⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hsub (stA, st, blkA, bs, n) R_view s0'
      (by cases s0; exact hpc) (by cases s0; exact hrun) hpre' (by cases s0; exact hsp))
    (by change R₀.CodeLoaded (stripExecOutside kp₀ s0.mem); exact strip_codeLoaded_prog hL0)
  have hlen_R : R₀.code.length = 7636 := compress256_patched_length hpl
  have hext_R_blk : ∀ off : Nat, off < R₀.code.length →
      P.externAt? (R₀.base + BitVec.ofNat 64 off) = none := by
    rw [hlen_R]; exact hext
  have hext_R : ∀ pc, R₀.externAt? pc = none := compress256_program_externAt?_none pl
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · obtain ⟨sf, hstepsP, hsf_eq, hpf, hacp⟩ :=
      steps_lift_placed_process_alloc hext_R_blk hext_R (compress256_program_noSvc pl)
        (compress256_program_noMsrTpidrEl0 pl) hsteps' hret'.2.2 s0 rfl hL0
    refine ⟨sf, hstepsP, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      have hpc_sf : sf.pc = s0.readReg64 Reg.lr := by
        rw [hsf_eq] at hr_pc; cases sf; cases s0; exact hr_pc
      have hsp_sf : sf.sp = s0.sp := by
        rw [hsf_eq] at hr_sp; cases sf; cases s0; exact hr_sp
      have hrun_sf : sf.status = .Running := by
        rw [hsf_eq] at hr_st; cases sf; exact hr_st
      exact ⟨hpc_sf, hsp_sf, hrun_sf⟩
    · rw [hsf_eq] at hcc'
      rcases hcc' with ⟨hsp_cc, hcs⟩
      exact ⟨by cases sf; cases s0; exact hsp_cc, by cases s0; cases sf; exact hcs⟩
    · rw [hsf_eq] at hpost'
      dsimp [s0', stripS] at hpost'
      rw [hpost_mem, State.mem_setMem] at hpost'
      have hpost'' : sf.mem ⊨ (compress256RawROSpec (pl.ρ sha2K32Sym)).post (stA, st, blkA, bs, n) s0 sf ∗ R :=
        hunstrip hpf.2.2.2.2.2.2.2 hpost'
      dsimp only [withPlacedCodeLoaded, compress256MasterROSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpf, hacp⟩, hpost''⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- Layout-generic `PlacedLib.subroutineOk` for `compress256Sym` against `compress256MasterROSpec`
under any `externs` map (`compress256Lib` has zero external call stubs). -/
theorem compress256_master_ro_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    compress256Lib.subroutineOk compress256Sym
      (fun pl => compress256MasterROSpec (pl.ρ sha2K32Sym)) externs := by
  refine ⟨by simp [compress256Lib], fun pl hpl => ?_⟩
  have hm := compress256_master_ro_ok hpl (P := compress256Lib.program pl externs)
    (fun off _ => compress256_program_externAt?_none pl externs _)
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hL0 : (compress256Lib.program pl).CodeLoaded s0.mem :=
    hLP.of_base_code rfl rfl
  have hpre_cl : s0.mem ⊨
      (withPlacedCodeLoaded compress256Lib pl (compress256MasterROSpec (pl.ρ sha2K32Sym))).pre x s0 ∗ R := by
    dsimp only [withPlacedCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, satisfies_pure_sepConj]
    exact ⟨hL0, hpre⟩
  exact hm.mono_outcome x R s0 hpc hrun hpre_cl hsp (fun _ h => h)

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift

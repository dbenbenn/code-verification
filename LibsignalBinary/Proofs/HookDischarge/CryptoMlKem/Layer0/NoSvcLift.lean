/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap
import ProofLib.Hoare.Model

/-!
# `NonSyscallPreserved` Lifting and Keccak RW Specializations

Re-exports `mlkemBlockOk_withNonSyscallPreserved` and `mlkemBlockConstOk_withNonSyscallPreserved`
from `Layer0.NoSvcLiftBase`, plus `OnlyRW`, `IsROPair`, and `rw_to_ro_preserve` from
`Layer0.FrozenHeap`. Proves `mlkemBlockSafeOk_withNonSyscallPreserved` and the writable-input
Keccak specializations `keccak2_72_6_RW1_ok`, `keccak2_136_6_RW1_ok`, `keccak2_136_31_RW2_ok`,
and `keccak2_136_31_RW1_ok`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockConstOk
  MlKemBlockOk
  MlKemBlockSafeOk
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2FixedArgs
  Keccak2ShakeArgs
  Keccak2SlicesRO
  Keccak2SlicesRW
  keccak2_136_31_RW1Spec
  keccak2_136_31_RW2Spec
  keccak2_136_31_Spec
  keccak2_136_6_RW1Spec
  keccak2_136_6_Spec
  keccak2_72_6_RW1Spec
  keccak2_72_6_Spec
  withNonSyscallPreserved
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  sha3_256List
  sha3_512List
  shake256List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep
  mlkemRoOk_stripExecOutside
  steps_diverge_stripS_mlkem
  steps_lift_stripS_mlkem
  stripExecOutside_eq_iff_of_perm_eq
  stripS_mem
  stripS_pc
  stripS_readReg32
  stripS_readReg64
  stripS_regs
  stripS_sp
  stripS_spAligned
  stripS_status
  stripS_vregs
  strip_codeLoaded_mlkem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap (
  IsROPair
  OnlyRW
  isROPair_keccak2Slices
  isROPair_pointsTo64
  isROPair_pointsToBytes
  isROPair_sepConj
  onlyRW_emp
  onlyRW_of_isBlock
  onlyRW_sepConj
  rw_to_ro_preserve
)

export LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemBlockOk_withNonSyscallPreserved
  mlkemBlockConstOk_withNonSyscallPreserved
)

/-- Lift any partial-correctness `MlKemBlockSafeOk j spec` (`j < 32`) to
    `withNonSyscallPreserved`. -/
theorem mlkemBlockSafeOk_withNonSyscallPreserved {j : Nat} {α : Type}
    {spec : MultiPlacement → Spec α}
    (hok : MlKemBlockSafeOk j spec)
    (hj : j < mlkemMultiLib.blocks.length := by decide)
    (hpan : ∀ mpl, (spec mpl).onPanic = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hex : ∀ mpl, (spec mpl).onExit = fun _ _ _ _ => ⌜False⌝ := by intro _; rfl)
    (hoom : ∀ mpl, (spec mpl).onOom = fun _ _ _ => ⌜False⌝ := by intro _; rfl)
    (h_pre : ∀ (mpl : MultiPlacement) (x : α) (R : SepProp) (s0 : State),
      (s0.mem ⊨ (spec mpl).pre x s0 ∗ R) →
      (s0.mem ⊨ (spec mpl).pre x (stripS (mlkemKeep mpl) s0) ∗ R) := by
        intro mpl x R s0 h; dsimp at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
    (h_post : ∀ (mpl : MultiPlacement) (x : α) (R : SepProp) (s0 sf : State),
      ProofLib.NonSyscallPreserved s0 sf →
      (sf.mem ⊨ (spec mpl).post x (stripS (mlkemKeep mpl) s0) (stripS (mlkemKeep mpl) sf) ∗ R) →
      (sf.mem ⊨ (spec mpl).post x s0 sf ∗ R) := by
        intro mpl x R s0 sf hnsp h; dsimp at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h) :
    MlKemBlockSafeOk j (fun mpl => withNonSyscallPreserved (spec mpl)) := by
  intro _ x R s0 hentry hpre _hLj
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved] at hpre
  rw [sepConj_comm ((spec mlkemMpl).pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_spec⟩ := hpre
  let keep := mlkemKeep mlkemMpl
  have hpre_s0' := h_pre mlkemMpl x R s0 hpre_spec
  obtain ⟨R_view, hpre_strip, hunstrip⟩ := strip_frame keep hpre_s0'
  let s0' := stripS keep s0
  have hcl_strip : mlkemMultiLib.CodeLoaded mlkemMpl s0'.mem :=
    strip_codeLoaded_mlkem hcl0
  have hpre' : s0'.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl (spec mlkemMpl)).pre x s0' ∗ R_view := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl_strip]
    exact hpre_strip
  have hentry' : AapcsEntry s0' (mlkemMpl.base j) :=
    ⟨by simpa [s0', stripS_pc] using hentry.1,
     by simpa [s0', stripS_status] using hentry.2.1,
     by simpa [s0', stripS_spAligned] using hentry.2.2⟩
  rcases hok x R_view s0' hentry' hpre' (hcl_strip j hj) with ⟨sf', hsteps_blk, hout'⟩ | hall'
  · rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · obtain ⟨sf, hsf_eq, hsteps_P, hnsp⟩ :=
        steps_lift_stripS_mlkem MlKemPlacement.placeable hcl0 rfl
          (Memory.KeepsFrozen.refl s0.mem) hsteps_blk
          (by rw [hret'.2.2]; decide)
      refine Or.inl ⟨sf, hsteps_P, Or.inl ⟨?_, ?_, ?_⟩⟩
      · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
        rw [hsf_eq] at hr_pc hr_sp hr_st
        exact ⟨by simpa [s0', stripS_pc, stripS_readReg64] using hr_pc,
          by simpa [s0', stripS_sp] using hr_sp,
          by simpa [stripS_status] using hr_st⟩
      · rw [hsf_eq] at hcc'
        rcases hcc' with ⟨hsp_cc, hcs⟩
        exact ⟨by simpa [s0', stripS_sp] using hsp_cc, by cases s0; cases sf; exact hcs⟩
      · rw [hsf_eq] at hpost'
        dsimp only [MultiPlacedLib.withCodeLoaded] at hpost'
        have hpost_strip : sf.mem ⊨
            (spec mlkemMpl).post x (stripS keep s0) (stripS keep sf) ∗ R :=
          hunstrip (fun a => congrFun hnsp.2.1 a) hpost'
        have hpost_sf := h_post mlkemMpl x R s0 sf hnsp hpost_strip
        dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved]
        rwa [sepConj_assoc, pure_sepConj_of_true hnsp]
    · dsimp only [MultiPlacedLib.withCodeLoaded] at hp
      rw [hpan mlkemMpl] at hp
      exact False.elim (not_satisfies_false_sepConj hp)
    · dsimp only [MultiPlacedLib.withCodeLoaded] at he
      rw [hex mlkemMpl] at he
      exact False.elim (not_satisfies_false_sepConj he)
    · dsimp only [MultiPlacedLib.withCodeLoaded] at ho
      rw [hoom mlkemMpl] at ho
      exact False.elim (not_satisfies_false_sepConj ho)
  · exact Or.inr fun u hu =>
      steps_diverge_stripS_mlkem MlKemPlacement.placeable hcl0 hu
        (Memory.KeepsFrozen.refl s0.mem) hall'

/-- `B00` aliased single-buffer RW specialization (`keccak2_72_6_RW1Spec`). -/
theorem keccak2_72_6_RW1_ok (hok : MlKemBlockOk 0 keccak2_72_6_Spec) :
    MlKemBlockOk 0 keccak2_72_6_RW1Spec := by
  have hok_nsp : MlKemBlockOk 0 (fun mpl => withNonSyscallPreserved (keccak2_72_6_Spec mpl)) :=
    mlkemBlockOk_withNonSyscallPreserved hok (by decide)
      (h_pre := fun mpl a R s0 h => by
        dsimp only [keccak2_72_6_Spec] at h ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
        simp only [stripS_readReg64, stripS_sp, stripS_mem]
        exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
          mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2⟩, h.2⟩)
      (h_post := fun mpl a R s0 sf _ h => by
        dsimp only [keccak2_72_6_Spec] at h ⊢
        simpa only [stripS_sp] using h)
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  rintro ⟨slicesPtr, ptr, out0, out1, msg⟩ R s0 hpc hrun hpre hsp hL0
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, keccak2_72_6_RW1Spec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨hpure, hspat⟩ := hpre_body
  have hspat' : s0.mem ⊨
      (Keccak2SlicesRW slicesPtr ptr ptr msg.length msg.length ∗ (ptr ↦ₛ msg)) ∗
      ((memRegion out0 64 ∗ memRegion out1 64 ∗ stackAt s0.sp 720) ∗ R) := by
    simpa only [sepConj_assoc] using hspat
  have hpair := isROPair_sepConj
    (isROPair_keccak2Slices slicesPtr ptr ptr msg.length msg.length)
    (isROPair_pointsToBytes ptr msg)
  have hWf : OnlyRW ((out0 ↦ₛ sha3_512List msg) ∗ (out1 ↦ₛ sha3_512List msg) ∗ stackAt s0.sp 720) :=
    onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
      (onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
        (onlyRW_of_isBlock (IsBlock.memRegion _ _)))
  obtain ⟨R', hpre_ro, hrecover⟩ := rw_to_ro_preserve hpair hWf hspat'
  let args : Keccak2FixedArgs :=
    { slicesPtr := slicesPtr, ptr0 := ptr, ptr1 := ptr, out0 := out0, out1 := out1,
      in0 := msg, in1 := msg }
  have hcallee_pre : s0.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (withNonSyscallPreserved (keccak2_72_6_Spec mlkemMpl))).pre args s0 ∗ R' := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved, keccak2_72_6_Spec, args]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0, sepConj_assoc]
    rw [pure_sepConj_of_true ⟨hpure.1, hpure.2.1, hpure.2.2.1, rfl, hpure.2.2.2.1, hpure.2.2.2.2⟩]
    rw [← sepConj_assoc (ptr ↦ᵣ msg) (ptr ↦ᵣ msg), pointsToBytesRO_dup]
    simpa only [sepConj_assoc] using hpre_ro
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hok_nsp args R' s0 hpc hrun hcallee_pre hsp) hL0
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved, keccak2_72_6_Spec, args]
      at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hnsp, hpost_ro⟩ := hpost
    have hpost_wf : sf.mem ⊨
        (Keccak2SlicesRO slicesPtr ptr ptr msg.length msg.length ∗ (ptr ↦ᵣ msg) ∗ (ptr ↦ᵣ msg)) ∗
        (((out0 ↦ₛ sha3_512List msg) ∗ (out1 ↦ₛ sha3_512List msg) ∗ stackAt s0.sp 720) ∗ R') := by
      simpa only [sepConj_assoc] using hpost_ro
    have hpost_rw := hrecover hnsp (Satisfies.of_sep_right hpost_wf)
    dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, keccak2_72_6_RW1Spec]
    rw [sepConj_assoc, pure_sepConj_of_true hnsp]
    simpa only [sepConj_assoc] using hpost_rw
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- `B02` aliased single-buffer RW specialization (`keccak2_136_6_RW1Spec`). -/
theorem keccak2_136_6_RW1_ok (hok : MlKemBlockOk 2 keccak2_136_6_Spec) :
    MlKemBlockOk 2 keccak2_136_6_RW1Spec := by
  have hok_nsp : MlKemBlockOk 2 (fun mpl => withNonSyscallPreserved (keccak2_136_6_Spec mpl)) :=
    mlkemBlockOk_withNonSyscallPreserved hok (by decide)
      (h_pre := fun mpl a R s0 h => by
        dsimp only [keccak2_136_6_Spec] at h ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
        simp only [stripS_readReg64, stripS_sp, stripS_mem]
        exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
          mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2⟩, h.2⟩)
      (h_post := fun mpl a R s0 sf _ h => by
        dsimp only [keccak2_136_6_Spec] at h ⊢
        simpa only [stripS_sp] using h)
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  rintro ⟨slicesPtr, ptr, out0, out1, msg⟩ R s0 hpc hrun hpre hsp hL2
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, keccak2_136_6_RW1Spec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨hpure, hspat⟩ := hpre_body
  have hspat' : s0.mem ⊨
      (Keccak2SlicesRW slicesPtr ptr ptr msg.length msg.length ∗ (ptr ↦ₛ msg)) ∗
      ((memRegion out0 32 ∗ memRegion out1 32 ∗ stackAt s0.sp 1040) ∗ R) := by
    simpa only [sepConj_assoc] using hspat
  have hpair := isROPair_sepConj
    (isROPair_keccak2Slices slicesPtr ptr ptr msg.length msg.length)
    (isROPair_pointsToBytes ptr msg)
  have hWf : OnlyRW ((out0 ↦ₛ sha3_256List msg) ∗ (out1 ↦ₛ sha3_256List msg) ∗ stackAt s0.sp 1040) :=
    onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
      (onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
        (onlyRW_of_isBlock (IsBlock.memRegion _ _)))
  obtain ⟨R', hpre_ro, hrecover⟩ := rw_to_ro_preserve hpair hWf hspat'
  let args : Keccak2FixedArgs :=
    { slicesPtr := slicesPtr, ptr0 := ptr, ptr1 := ptr, out0 := out0, out1 := out1,
      in0 := msg, in1 := msg }
  have hcallee_pre : s0.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (withNonSyscallPreserved (keccak2_136_6_Spec mlkemMpl))).pre args s0 ∗ R' := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved, keccak2_136_6_Spec, args]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0, sepConj_assoc]
    rw [pure_sepConj_of_true ⟨hpure.1, hpure.2.1, hpure.2.2.1, rfl, hpure.2.2.2.1, hpure.2.2.2.2⟩]
    rw [← sepConj_assoc (ptr ↦ᵣ msg) (ptr ↦ᵣ msg), pointsToBytesRO_dup]
    simpa only [sepConj_assoc] using hpre_ro
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hok_nsp args R' s0 hpc hrun hcallee_pre hsp) hL2
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved, keccak2_136_6_Spec, args]
      at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hnsp, hpost_ro⟩ := hpost
    have hpost_wf : sf.mem ⊨
        (Keccak2SlicesRO slicesPtr ptr ptr msg.length msg.length ∗ (ptr ↦ᵣ msg) ∗ (ptr ↦ᵣ msg)) ∗
        (((out0 ↦ₛ sha3_256List msg) ∗ (out1 ↦ₛ sha3_256List msg) ∗ stackAt s0.sp 1040) ∗ R') := by
      simpa only [sepConj_assoc] using hpost_ro
    have hpost_rw := hrecover hnsp (Satisfies.of_sep_right hpost_wf)
    dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, keccak2_136_6_RW1Spec]
    rw [sepConj_assoc, pure_sepConj_of_true hnsp]
    simpa only [sepConj_assoc] using hpost_rw
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- `B01` distinct two-buffer RW specialization (`keccak2_136_31_RW2Spec`). -/
theorem keccak2_136_31_RW2_ok (hok : MlKemBlockOk 1 keccak2_136_31_Spec) :
    MlKemBlockOk 1 keccak2_136_31_RW2Spec := by
  have hok_nsp : MlKemBlockOk 1 (fun mpl => withNonSyscallPreserved (keccak2_136_31_Spec mpl)) :=
    mlkemBlockOk_withNonSyscallPreserved hok (by decide)
      (h_pre := fun mpl a R s0 h => by
        dsimp only [keccak2_136_31_Spec] at h ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
        simp only [stripS_readReg64, stripS_sp, stripS_mem]
        exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
          h.1.2.2.2.2.2.2.1, h.1.2.2.2.2.2.2.2.1,
          mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2.2.2.2⟩, h.2⟩)
      (h_post := fun mpl a R s0 sf _ h => by
        dsimp only [keccak2_136_31_Spec] at h ⊢
        simpa only [stripS_sp] using h)
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro a R s0 hpc hrun hpre hsp hL1
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, keccak2_136_31_RW2Spec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨hpure, hspat⟩ := hpre_body
  have hspat' : s0.mem ⊨
      (Keccak2SlicesRW a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ₛ a.in0) ∗ (a.ptr1 ↦ₛ a.in1)) ∗
      ((memRegion a.out0 a.outLen ∗ memRegion a.out1 a.outLen ∗ stackAt s0.sp 1136) ∗ R) := by
    simpa only [sepConj_assoc] using hspat
  have hpair := isROPair_sepConj
    (isROPair_keccak2Slices a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length)
    (isROPair_sepConj (isROPair_pointsToBytes a.ptr0 a.in0)
      (isROPair_pointsToBytes a.ptr1 a.in1))
  have hWf : OnlyRW ((a.out0 ↦ₛ shake256List a.outLen a.in0) ∗
      (a.out1 ↦ₛ shake256List a.outLen a.in1) ∗ stackAt s0.sp 1136) :=
    onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
      (onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
        (onlyRW_of_isBlock (IsBlock.memRegion _ _)))
  obtain ⟨R', hpre_ro, hrecover⟩ := rw_to_ro_preserve hpair hWf hspat'
  have hcallee_pre : s0.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (withNonSyscallPreserved (keccak2_136_31_Spec mlkemMpl))).pre a s0 ∗ R' := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved, keccak2_136_31_Spec]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0, sepConj_assoc,
      pure_sepConj_of_true hpure]
    simpa only [sepConj_assoc] using hpre_ro
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hok_nsp a R' s0 hpc hrun hcallee_pre hsp) hL1
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved, keccak2_136_31_Spec]
      at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hnsp, hpost_ro⟩ := hpost
    have hpost_wf : sf.mem ⊨
        (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1)) ∗
        (((a.out0 ↦ₛ shake256List a.outLen a.in0) ∗
          (a.out1 ↦ₛ shake256List a.outLen a.in1) ∗ stackAt s0.sp 1136) ∗ R') := by
      simpa only [sepConj_assoc] using hpost_ro
    have hpost_rw := hrecover hnsp (Satisfies.of_sep_right hpost_wf)
    dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, keccak2_136_31_RW2Spec]
    rw [sepConj_assoc, pure_sepConj_of_true hnsp]
    simpa only [sepConj_assoc] using hpost_rw
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- `B01` aliased single-buffer RW specialization (`keccak2_136_31_RW1Spec`). -/
theorem keccak2_136_31_RW1_ok (hok : MlKemBlockOk 1 keccak2_136_31_Spec) :
    MlKemBlockOk 1 keccak2_136_31_RW1Spec := by
  have hok_nsp : MlKemBlockOk 1 (fun mpl => withNonSyscallPreserved (keccak2_136_31_Spec mpl)) :=
    mlkemBlockOk_withNonSyscallPreserved hok (by decide)
      (h_pre := fun mpl a R s0 h => by
        dsimp only [keccak2_136_31_Spec] at h ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
        simp only [stripS_readReg64, stripS_sp, stripS_mem]
        exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
          h.1.2.2.2.2.2.2.1, h.1.2.2.2.2.2.2.2.1,
          mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2.2.2.2⟩, h.2⟩)
      (h_post := fun mpl a R s0 sf _ h => by
        dsimp only [keccak2_136_31_Spec] at h ⊢
        simpa only [stripS_sp] using h)
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  rintro ⟨slicesPtr, ptr, out0, out1, outLen, msg⟩ R s0 hpc hrun hpre hsp hL1
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, keccak2_136_31_RW1Spec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨hpure, hspat⟩ := hpre_body
  have hspat' : s0.mem ⊨
      (Keccak2SlicesRW slicesPtr ptr ptr msg.length msg.length ∗ (ptr ↦ₛ msg)) ∗
      ((memRegion out0 outLen ∗ memRegion out1 outLen ∗ stackAt s0.sp 1136) ∗ R) := by
    simpa only [sepConj_assoc] using hspat
  have hpair := isROPair_sepConj
    (isROPair_keccak2Slices slicesPtr ptr ptr msg.length msg.length)
    (isROPair_pointsToBytes ptr msg)
  have hWf : OnlyRW ((out0 ↦ₛ shake256List outLen msg) ∗
      (out1 ↦ₛ shake256List outLen msg) ∗ stackAt s0.sp 1136) :=
    onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
      (onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
        (onlyRW_of_isBlock (IsBlock.memRegion _ _)))
  obtain ⟨R', hpre_ro, hrecover⟩ := rw_to_ro_preserve hpair hWf hspat'
  let args : Keccak2ShakeArgs :=
    { slicesPtr := slicesPtr, ptr0 := ptr, ptr1 := ptr, out0 := out0, out1 := out1,
      outLen := outLen, in0 := msg, in1 := msg }
  have hcallee_pre : s0.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (withNonSyscallPreserved (keccak2_136_31_Spec mlkemMpl))).pre args s0 ∗ R' := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved, keccak2_136_31_Spec, args]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0, sepConj_assoc]
    rw [pure_sepConj_of_true
      ⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2.1, hpure.2.2.2.2.1, rfl,
       hpure.2.2.2.2.2.1, hpure.2.2.2.2.2.2.1, hpure.2.2.2.2.2.2.2⟩]
    rw [← sepConj_assoc (ptr ↦ᵣ msg) (ptr ↦ᵣ msg), pointsToBytesRO_dup]
    simpa only [sepConj_assoc] using hpre_ro
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hok_nsp args R' s0 hpc hrun hcallee_pre hsp) hL1
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, withNonSyscallPreserved, keccak2_136_31_Spec, args]
      at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hnsp, hpost_ro⟩ := hpost
    have hpost_wf : sf.mem ⊨
        (Keccak2SlicesRO slicesPtr ptr ptr msg.length msg.length ∗ (ptr ↦ᵣ msg) ∗ (ptr ↦ᵣ msg)) ∗
        (((out0 ↦ₛ shake256List outLen msg) ∗
          (out1 ↦ₛ shake256List outLen msg) ∗ stackAt s0.sp 1136) ∗ R') := by
      simpa only [sepConj_assoc] using hpost_ro
    have hpost_rw := hrecover hnsp (Satisfies.of_sep_right hpost_wf)
    dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, keccak2_136_31_RW1Spec]
    rw [sepConj_assoc, pure_sepConj_of_true hnsp]
    simpa only [sepConj_assoc] using hpost_rw
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift

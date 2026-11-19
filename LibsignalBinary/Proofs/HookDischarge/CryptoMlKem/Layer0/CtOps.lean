/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs
import ProofLib.Hoare.Model
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Compare
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.SelectCt

/-!
# Constant-time operations (`B12`–`B18`)

Re-exports the constant-time comparison and selection proofs `blk15_inz_ok`,
`blk12_is_non_zero_ok`, `blk17_compare_ok`, `blk13_compare_ct_ok`, `blk18_select_ct_ok`, and
`blk14_select_ss_ok`, and proves `B16` (`compare_ciphertexts_select_shared_secret_in_constant_time`):
- `blk16_compare_select_ok : MlKemBlockConstOk 16 mlkemCompareSelectROSpec`
- `blk16_compare_select_RW_ok : MlKemBlockConstOk 16 mlkemCompareSelectRWSpec` (for `B04`)
- `blk16_compare_select_RO1RW3_ok : MlKemBlockConstOk 16 mlkemCompareSelectRO1RW3Spec` (for `B06`)
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemBlockConstOk
  MlKemPlacement
  add_off_reloc_cancel
  add_reloc_cancel
  add_zero_reloc_cancel
  mbase
  mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk
  mlkemCaller_ok
  mlkemMpl
  resolve_blk13
  resolve_blk14
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap (
  OnlyRW
  isROPair_pointsToBytes
  isROPair_sepConj
  onlyRW_of_isBlock
  onlyRW_sepConj
  rw_to_ro_preserve
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  mlkemBlockConstOk_withNonSyscallPreserved
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep
  stripExecOutside_eq_iff_of_perm_eq
  stripS_mem
  stripS_readReg32
  stripS_readReg64
  stripS_regs
  stripS_sp
  stripS_vregs
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs (
  CtCompareSelectArgs
  CtCompareSelectPurePre
  CtSelectArgs
  mlkemCompareSelectRO1RW3Spec
  mlkemCompareSelectROSpec
  mlkemCompareSelectRWSpec
  mlkemCtCompareROSpec
  mlkemInzSpec
  mlkemIsNonZeroSpec
  mlkemSelectCtROSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare (
  mlkemConstOk_map_ct
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Compare (
  blk13_compare_ct_base_ok
  mlkemCtCompareBaseSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.SelectCt (
  blk14_select_ss_base_ok
  mlkemSelectCtBaseSpec
)

gen_block_fetches mlkem 16 mlkemMultiLib MlKemPlacement 21

@[simp, arm64_norm, wp_norm]
private theorem mlkemPl16_ρ [MlKemPlacement] (sym : String) :
    mlkemPl16.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

private theorem satisfies_stackAt112_six {m : Memory} {sp : BitVec 64} {R : SepProp}
    (hm : m ⊨ stackAt sp 112 ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 : BitVec 64),
      m ⊨ (stackAt (sp - 48#64) 64 ∗
        ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
        ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
        ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ∗ R := by
  rw [stackAt_frame sp 112 6 (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide), cells_zero] at hm
  simp only [sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  rcases hm with ⟨w0, w1, w2, w3, w4, w5, hm⟩
  exact ⟨w0, w1, w2, w3, w4, w5, Satisfies.mono (by sep_frame) hm⟩

private theorem stackAt112_six_entails (sp : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (stackAt (sp - 48#64) 64 ∗
      ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
      ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
      ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢ stackAt sp 112 := by
  rw [stackAt_frame sp 112 6 (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide), cells_zero]
  simp only [sepConj_emp]
  exact sepConj_mono_right
    (Entails.sepExists_right w0 (sepConj_mono_right
      (Entails.sepExists_right w1 (sepConj_mono_right
        (Entails.sepExists_right w2 (sepConj_mono_right
          (Entails.sepExists_right w3 (sepConj_mono_right
            (Entails.sepExists_right w4 (sepConj_mono_right
              (Entails.sepExists_right w5 (Entails.refl _))))))))))))

private theorem flag8_beq_zero (c : Bool) :
    ((if c then 0#8 else 1#8) == 0#8) = c := by
  cases c <;> rfl

private def mlkemCompareSelectBaseSpec : Spec CtCompareSelectArgs where
  pre := mlkemCompareSelectROSpec.pre
  post := fun a s0 _sf =>
    (a.outPtr ↦ₛ (if a.lhsCt == a.rhsCt then a.lhsSs else a.rhsSs)) ∗
      (a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ᵣ a.rhsCt) ∗
      (a.lhsSsPtr ↦ᵣ a.lhsSs) ∗ (a.rhsSsPtr ↦ᵣ a.rhsSs) ∗
      stackAt s0.sp 112
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem blk16_compare_select_base_ok :
    MlKemBlockConstOk 16 mlkemCompareSelectBaseSpec := by
  intro _
  refine mlkemCaller_ok (j := 16) mlkemPC16 mlkemPl16 (spec := mlkemCompareSelectBaseSpec)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemCompareSelectBaseSpec,
    mlkemCompareSelectROSpec, CtCompareSelectPurePre] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, h1, hrhsCt, hlt, hlhsSs, hrhsSs⟩, hspat⟩ :=
    hpre_body
  have hspat_stk : s0.mem ⊨ stackAt s0.sp 112 ∗
      (memRegion a.outPtr 32 ∗ (a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ᵣ a.rhsCt) ∗
        (a.lhsSsPtr ↦ᵣ a.lhsSs) ∗ (a.rhsSsPtr ↦ᵣ a.rhsSs) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  obtain ⟨w0, w1, w2, w3, w4, w5, hspat'⟩ := satisfies_stackAt112_six hspat_stk
  refine ⟨memRegion a.outPtr 32 ∗ (a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ᵣ a.rhsCt) ∗
    (a.lhsSsPtr ↦ᵣ a.lhsSs) ∗ (a.rhsSsPtr ↦ᵣ a.rhsSs) ∗
    stackAt (s0.sp - 48#64) 64 ∗
    ((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗
    ((s0.sp - 32#64) ↦₆₄ w2) ∗ ((s0.sp - 24#64) ↦₆₄ w3) ∗
    ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5),
    Satisfies.mono (by sep_frame) hspat', ?_⟩
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk13_compare_ct_base_ok (a.lhsCtPtr, a.rhsCtPtr, a.lhsCt, a.rhsCt)
  wp_steps 8
  apply SepWP.weaken_pre
    (Entails.trans
      (by sep_frame : _ ⊢
        memRegion a.outPtr 32 ∗ (a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ᵣ a.rhsCt) ∗
        (a.lhsSsPtr ↦ᵣ a.lhsSs) ∗ (a.rhsSsPtr ↦ᵣ a.rhsSs) ∗
        (stackAt (s0.sp - 48#64) 64 ∗
          ((s0.sp - 48#64) ↦₆₄ _) ∗ ((s0.sp - 40#64) ↦₆₄ _) ∗
          ((s0.sp - 32#64) ↦₆₄ _) ∗ ((s0.sp - 24#64) ↦₆₄ _) ∗
          ((s0.sp - 16#64) ↦₆₄ _) ∗ ((s0.sp - 8#64) ↦₆₄ _)))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (stackAt112_six_entails s0.sp _ _ _ _ _ _)))))))
  wp_mlkem_tailcall blk14_select_ss_base_ok
  simp only [wp_norm, width_norm, hpost, flag8_beq_zero] at *
  wp_done

public section

/-- `B15` (`inz`) total contract with `NonSyscallPreserved`. -/
theorem blk15_inz_ok : MlKemBlockConstOk 15 mlkemInzSpec :=
  InzCompare.blk15_inz_ok

/-- `B12` (`is_non_zero`) total contract with `NonSyscallPreserved`. -/
theorem blk12_is_non_zero_ok : MlKemBlockConstOk 12 mlkemIsNonZeroSpec :=
  InzCompare.blk12_is_non_zero_ok

/-- `B17` (`compare`) read-only contract (`32`-byte stack) with `NonSyscallPreserved`. -/
theorem blk17_compare_ok : MlKemBlockConstOk 17 (mlkemCtCompareROSpec 32) :=
  Compare.blk17_compare_ok

/-- `B13` (`compare_ciphertexts_in_constant_time`) read-only contract (`64`-byte stack)
    with `NonSyscallPreserved`. -/
theorem blk13_compare_ct_ok : MlKemBlockConstOk 13 (mlkemCtCompareROSpec 64) :=
  Compare.blk13_compare_ct_ok

/-- `B18` (`select_ct`) `32`-byte constant-time selection contract (`80`-byte stack)
    with `NonSyscallPreserved`. -/
theorem blk18_select_ct_ok : MlKemBlockConstOk 18 (mlkemSelectCtROSpec 80) :=
  SelectCt.blk18_select_ct_ok

/-- `B14` (`select_shared_secret_in_constant_time`) `32`-byte constant-time selection contract
    (`112`-byte stack) with `NonSyscallPreserved`. -/
theorem blk14_select_ss_ok : MlKemBlockConstOk 14 (mlkemSelectCtROSpec 112) :=
  SelectCt.blk14_select_ss_ok

/-- `B16` (`compare_ciphertexts_select_shared_secret_in_constant_time`) read-only contract
    (`112`-byte stack) with `NonSyscallPreserved`. -/
theorem blk16_compare_select_ok : MlKemBlockConstOk 16 mlkemCompareSelectROSpec := by
  intro _
  exact (mlkemConstOk_map_ct (spec' := mlkemCompareSelectROSpec)
    (mlkemBlockConstOk_withNonSyscallPreserved blk16_compare_select_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemCompareSelectBaseSpec, mlkemCompareSelectROSpec, CtCompareSelectPurePre] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemCompareSelectBaseSpec, mlkemCompareSelectROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun args R _s0 hpre => ⟨args, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemCompareSelectBaseSpec,
        mlkemCompareSelectROSpec] at hpost ⊢
      exact hpost⟩)

/-- `B16` all-RW input specialization (matches `B04`, where both ciphertexts and both
    shared-secret candidates reside in the caller's writable stack frame). -/
theorem blk16_compare_select_RW_ok : MlKemBlockConstOk 16 mlkemCompareSelectRWSpec := by
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro a R s0 hpc hrun hpre hsp hL1
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, mlkemCompareSelectRWSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨hpure, hspat⟩ := hpre_body
  have hspat' : s0.mem ⊨
      ((a.lhsCtPtr ↦ₛ a.lhsCt) ∗ (a.rhsCtPtr ↦ₛ a.rhsCt) ∗
        (a.lhsSsPtr ↦ₛ a.lhsSs) ∗ (a.rhsSsPtr ↦ₛ a.rhsSs)) ∗
      ((memRegion a.outPtr 32 ∗ stackAt s0.sp 112) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  have hpair := isROPair_sepConj (isROPair_pointsToBytes a.lhsCtPtr a.lhsCt)
    (isROPair_sepConj (isROPair_pointsToBytes a.rhsCtPtr a.rhsCt)
      (isROPair_sepConj (isROPair_pointsToBytes a.lhsSsPtr a.lhsSs)
        (isROPair_pointsToBytes a.rhsSsPtr a.rhsSs)))
  have hWf : OnlyRW ((a.outPtr ↦ₛ (if a.lhsCt == a.rhsCt then a.lhsSs else a.rhsSs)) ∗
      stackAt s0.sp 112) :=
    onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
      (onlyRW_of_isBlock (IsBlock.memRegion _ _))
  obtain ⟨R', hpre_ro, hrecover⟩ := rw_to_ro_preserve hpair hWf hspat'
  have hcallee_pre : s0.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemCompareSelectROSpec).pre a s0 ∗ R' := by
    dsimp only [MultiPlacedLib.withCodeLoaded, mlkemCompareSelectROSpec]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0, sepConj_assoc,
      pure_sepConj_of_true hpure]
    exact Satisfies.mono (by sep_frame) hpre_ro
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 blk16_compare_select_ok a R' s0 hpc hrun hcallee_pre hsp) hL1
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, mlkemCompareSelectROSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hnsp, hpost_ro⟩ := hpost
    have hpost_wf : sf.mem ⊨
        ((a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ᵣ a.rhsCt) ∗
          (a.lhsSsPtr ↦ᵣ a.lhsSs) ∗ (a.rhsSsPtr ↦ᵣ a.rhsSs)) ∗
        (((a.outPtr ↦ₛ (if a.lhsCt == a.rhsCt then a.lhsSs else a.rhsSs)) ∗
          stackAt s0.sp 112) ∗ R') :=
      Satisfies.mono (by sep_frame) hpost_ro
    have hpost_rw := hrecover hnsp (Satisfies.of_sep_right hpost_wf)
    dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, mlkemCompareSelectRWSpec]
    rw [sepConj_assoc, pure_sepConj_of_true hnsp]
    exact Satisfies.mono (by sep_frame) hpost_rw
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- `B16` RO-`lhsCt` + RW-`rhsCt`/`lhsSs`/`rhsSs` specialization (matches `B06`, where `lhsCt` is
    the read-only caller ciphertext slice and `rhsCt`, `lhsSs`, `rhsSs` reside on the stack). -/
theorem blk16_compare_select_RO1RW3_ok :
    MlKemBlockConstOk 16 mlkemCompareSelectRO1RW3Spec := by
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro a R s0 hpc hrun hpre hsp hL1
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, mlkemCompareSelectRO1RW3Spec]
    at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨hpure, hspat⟩ := hpre_body
  have hspat_dup : s0.mem ⊨
      ((a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.lhsCtPtr ↦ᵣ a.lhsCt)) ∗
      ((memRegion a.outPtr 32 ∗ (a.rhsCtPtr ↦ₛ a.rhsCt) ∗
        (a.lhsSsPtr ↦ₛ a.lhsSs) ∗ (a.rhsSsPtr ↦ₛ a.rhsSs) ∗ stackAt s0.sp 112) ∗ R) := by
    rw [pointsToBytesRO_dup]
    exact Satisfies.mono (by sep_frame) hspat
  have hspat' : s0.mem ⊨
      ((a.rhsCtPtr ↦ₛ a.rhsCt) ∗ (a.lhsSsPtr ↦ₛ a.lhsSs) ∗ (a.rhsSsPtr ↦ₛ a.rhsSs)) ∗
      ((memRegion a.outPtr 32 ∗ (a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ stackAt s0.sp 112) ∗
        ((a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ R)) :=
    Satisfies.mono (by sep_frame) hspat_dup
  have hpair := isROPair_sepConj (isROPair_pointsToBytes a.rhsCtPtr a.rhsCt)
    (isROPair_sepConj (isROPair_pointsToBytes a.lhsSsPtr a.lhsSs)
      (isROPair_pointsToBytes a.rhsSsPtr a.rhsSs))
  have hWf : OnlyRW ((a.outPtr ↦ₛ (if a.lhsCt == a.rhsCt then a.lhsSs else a.rhsSs)) ∗
      stackAt s0.sp 112) :=
    onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
      (onlyRW_of_isBlock (IsBlock.memRegion _ _))
  obtain ⟨R', hpre_ro, hrecover⟩ := rw_to_ro_preserve hpair hWf hspat'
  have hcallee_pre : s0.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemCompareSelectROSpec).pre a s0 ∗ R' := by
    dsimp only [MultiPlacedLib.withCodeLoaded, mlkemCompareSelectROSpec]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0, sepConj_assoc,
      pure_sepConj_of_true hpure]
    exact Satisfies.mono (by sep_frame) hpre_ro
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 blk16_compare_select_ok a R'
      s0 hpc hrun hcallee_pre hsp) hL1
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, mlkemCompareSelectROSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hnsp, hpost_ro⟩ := hpost
    have hpost_wf : sf.mem ⊨
        ((a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ᵣ a.rhsCt) ∗
          (a.lhsSsPtr ↦ᵣ a.lhsSs) ∗ (a.rhsSsPtr ↦ᵣ a.rhsSs)) ∗
        (((a.outPtr ↦ₛ (if a.lhsCt == a.rhsCt then a.lhsSs else a.rhsSs)) ∗
          stackAt s0.sp 112) ∗ R') :=
      Satisfies.mono (by sep_frame) hpost_ro
    have hpost_rw := hrecover hnsp (Satisfies.of_sep_right hpost_wf)
    dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, mlkemCompareSelectRO1RW3Spec]
    rw [sepConj_assoc, pure_sepConj_of_true hnsp]
    exact Satisfies.mono (by sep_frame) hpost_rw
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps

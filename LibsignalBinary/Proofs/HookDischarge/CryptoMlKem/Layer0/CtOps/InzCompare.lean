/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift

/-!
# Constant-time `inz` and `is_non_zero` (`B15`, `B12`)

Proves `blk15_inz_ok : MlKemBlockConstOk 15 mlkemInzSpec` and
`blk12_is_non_zero_ok : MlKemBlockConstOk 12 mlkemIsNonZeroSpec`, along with shared
`mlkemConstOk_map_ct` and `32`-byte stack frame lemmas for `CtOps` callers.
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare

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
  mlkemLeaf_ok
  mlkemMpl
  resolve_blk15
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
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
  mlkemInzSpec
  mlkemIsNonZeroSpec
)

gen_block_fetches mlkem 15 mlkemMultiLib MlKemPlacement 4
gen_block_fetches mlkem 12 mlkemMultiLib MlKemPlacement 11

@[simp, arm64_norm, wp_norm]
private theorem mlkemPl12_ρ [MlKemPlacement] (sym : String) :
    mlkemPl12.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

/-! ## `B15` (`inz`, 4 words, 0-byte stack) -/

private abbrev mlkemInzBaseSpec : Spec (BitVec 8) where
  pre := mlkemInzSpec.pre
  post := fun b _s0 sf =>
    ⌜sf.readReg32 .x0 = (if b == 0#8 then 0#32 else 1#32)⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem inz_arith (b : BitVec 8) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (0#32 - BitVec.zeroExtend 32 b) >>> 31) =
      (if b == 0#8 then 0#32 else 1#32) := by
  revert b; decide +kernel

private theorem blk15_inz_base_ok : MlKemBlockConstOk 15 mlkemInzBaseSpec := by
  intro _
  refine mlkemLeaf_ok (j := 15) mlkemPC15 mlkemPl15 (spec := mlkemInzBaseSpec)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro byteVal R s0 hpc hrun hpre _hsp
  dsimp only [ToBaseSpec.toSpec, mlkemInzBaseSpec, mlkemInzSpec] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨hx0, hR⟩ := hpre
  subst hx0
  refine ⟨emp, by rwa [emp_sepConj], ?_⟩
  wp_steps
  simp only [wp_norm, width_norm, inz_arith]
  wp_done

/-! ## `B12` (`is_non_zero`, 11 words, 32-byte stack) -/

public section

/-- Map a proved `MlKemBlockConstOk` contract to a weaker/equivalent `Spec`. -/
theorem mlkemConstOk_map_ct {j : Nat} {α β : Type} {spec : Spec α} {spec' : Spec β}
    (h : MlKemBlockConstOk j spec)
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ x R', (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        ∀ sf, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    MlKemBlockConstOk j spec' := by
  intro _
  refine subroutine_ok_map h (fun y R s0 hpre => ?_)
    (h_no_panic := fun x R' s0 sf _ hp => by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hp
      rw [hpan] at hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit := fun x c R' s0 sf _ he => by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at he
      rw [hex] at he; exact not_satisfies_false_sepConj he)
    (h_oom := fun x y R R' s0 sf _ ho => by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at ho
      rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_spec⟩ := hpre
  obtain ⟨x, R', hpre_x, hpost_x⟩ := hmap y R s0 hpre_spec
  refine ⟨x, R', ?_, fun sf hpost => ?_⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0]
    exact hpre_x
  · dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpost ⊢
    exact hpost_x sf hpost

theorem inz_flag_mask_roundtrip (c : Bool) :
    BitVec.zeroExtend 32 (BitVec.truncate 8 ((if c then 0#32 else 1#32) &&& 255#32)) =
      (if c then 0#32 else 1#32) := by
  cases c <;> rfl

theorem inz_flag_roundtrip (c : Bool) :
    BitVec.zeroExtend 32 (BitVec.truncate 8 (if c then 0#32 else 1#32)) =
      (if c then 0#32 else 1#32) := by
  cases c <;> rfl

theorem stackAt32_inz_eq (sp : BitVec 64) :
    stackAt sp 32 =
      (∃∗ b0 : BitVec 8, (sp - 20#64) ↦₈ b0) ∗
        memRegion (sp - 32#64) 12 ∗ memRegion (sp - 19#64) 3 ∗
        (∃∗ w0 : BitVec 64, (sp - 16#64) ↦₆₄ w0 ∗ ∃∗ w1 : BitVec 64, (sp - 8#64) ↦₆₄ w1) := by
  rw [stackAt_frame sp 32 2 (by decide)]
  change memRegion (sp - 16#64 - 16#64) 16 ∗ cells (sp - 16#64) 2 = _
  rw [memRegion_split3 (sp - 16#64 - 16#64) 16 12 1 (by decide) (by decide), memRegion_one]
  have h1 : sp - 16#64 - 16#64 = sp - 32#64 := by bv_omega
  have h2 : sp - 32#64 + 12#64 = sp - 20#64 := by bv_omega
  have h3 : sp - 32#64 + 13#64 = sp - 19#64 := by bv_omega
  rw [h1, h2, h3, cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide), cells_zero]
  simp only [Nat.reduceSub, sepConj_emp, sepConj_assoc]

theorem satisfies_stackAt32_inz {m : Memory} {sp : BitVec 64} {R : SepProp}
    (hm : m ⊨ stackAt sp 32 ∗ R) :
    ∃ (b0 : BitVec 8) (w0 w1 : BitVec 64),
      m ⊨ (((sp - 20#64) ↦₈ b0) ∗ ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) ∗
        memRegion (sp - 32#64) 12 ∗ memRegion (sp - 19#64) 3) ∗ R := by
  rw [stackAt32_inz_eq sp] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  rcases hm with ⟨w0, w1, b0, hm⟩
  exact ⟨b0, w0, w1, Satisfies.mono (by sep_frame) hm⟩

theorem stackAt32_inz_entails (sp : BitVec 64) (b0 : BitVec 8) (w0 w1 : BitVec 64) :
    (((sp - 20#64) ↦₈ b0) ∗ ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) ∗
      memRegion (sp - 32#64) 12 ∗ memRegion (sp - 19#64) 3) ⊢ stackAt sp 32 := by
  rw [stackAt32_inz_eq sp]
  refine Entails.trans (by sep_frame : _ ⊢
      ((sp - 20#64) ↦₈ b0) ∗ memRegion (sp - 32#64) 12 ∗
        memRegion (sp - 19#64) 3 ∗ (((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1))) ?_
  exact sepConj_mono (Entails.sepExists_right b0 (Entails.refl _))
    (sepConj_mono_right (sepConj_mono_right (Entails.sepExists_right w0
      (sepConj_mono_right (Entails.sepExists_right w1 (Entails.refl _))))))

/-- Base `B12` spec without `NonSyscallPreserved` (used directly by `B17` and `B18` before
    outer `mlkemBlockConstOk_withNonSyscallPreserved` lifting). -/
@[expose] def mlkemIsNonZeroBaseSpec : Spec (BitVec 8) where
  pre := mlkemIsNonZeroSpec.pre
  post := fun b s0 sf =>
    ⌜sf.readReg32 .x0 = (if b == 0#8 then 0#32 else 1#32)⌝ ∗
      stackAt s0.sp 32
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem blk12_is_non_zero_base_ok : MlKemBlockConstOk 12 mlkemIsNonZeroBaseSpec := by
  intro _
  refine mlkemCaller_ok (j := 12) mlkemPC12 mlkemPl12 (spec := mlkemIsNonZeroBaseSpec)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro byteVal R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemIsNonZeroBaseSpec,
    mlkemIsNonZeroSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨hx0, hspat⟩ := hpre_body
  have hx0' : BitVec.zeroExtend 8 (s0.readReg64 (Reg.gpr 0#5)) = byteVal := by
    simpa [State.readReg32] using hx0
  obtain ⟨b0, w0, w1, hspat'⟩ := satisfies_stackAt32_inz hspat
  refine ⟨((s0.sp - 20#64) ↦₈ b0) ∗ ((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1) ∗
    memRegion (s0.sp - 32#64) 12 ∗ memRegion (s0.sp - 19#64) 3, hspat', ?_⟩
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk15_inz_base_ok byteVal
  wp_steps
  apply SepWP.weaken_pre (stackAt32_inz_entails s0.sp _ _ _)
  simp only [wp_norm, width_norm]
  wp_done

/-- `B15` (`inz`) total contract with `NonSyscallPreserved`. -/
theorem blk15_inz_ok : MlKemBlockConstOk 15 mlkemInzSpec := by
  intro _
  exact (mlkemConstOk_map_ct (spec' := mlkemInzSpec)
    (mlkemBlockConstOk_withNonSyscallPreserved blk15_inz_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemInzBaseSpec, mlkemInzSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemInzBaseSpec, mlkemInzSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun byteVal R _s0 hpre => ⟨byteVal, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemInzBaseSpec, mlkemInzSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩)

/-- `B12` (`is_non_zero`) total contract with `NonSyscallPreserved`. -/
theorem blk12_is_non_zero_ok : MlKemBlockConstOk 12 mlkemIsNonZeroSpec := by
  intro _
  exact (mlkemConstOk_map_ct (spec' := mlkemIsNonZeroSpec)
    (mlkemBlockConstOk_withNonSyscallPreserved blk12_is_non_zero_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemIsNonZeroBaseSpec, mlkemIsNonZeroSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemIsNonZeroBaseSpec, mlkemIsNonZeroSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun byteVal R _s0 hpre => ⟨byteVal, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemIsNonZeroBaseSpec, mlkemIsNonZeroSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare

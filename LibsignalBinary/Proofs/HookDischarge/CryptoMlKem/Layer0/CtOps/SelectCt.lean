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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare

/-!
# Constant-time 32-byte secret selection (`B18`, `B14`)

Proves the constant-time 32-byte secret selection contracts:
- `blk18_select_ct_ok : MlKemBlockConstOk 18 (mlkemSelectCtROSpec 80)`
- `blk14_select_ss_ok : MlKemBlockConstOk 14 (mlkemSelectCtROSpec 112)`
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.SelectCt

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
  resolve_blk12
  resolve_blk18
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
  CtSelectArgs
  mlkemIsNonZeroSpec
  mlkemSelectCtROSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare (
  blk12_is_non_zero_base_ok
  mlkemConstOk_map_ct
  mlkemIsNonZeroBaseSpec
)

gen_block_fetches mlkem 18 mlkemMultiLib MlKemPlacement 433 [0x0 → 0x440]
gen_block_fetches mlkem 14 mlkemMultiLib MlKemPlacement 8

@[simp, arm64_norm, wp_norm]
private theorem mlkemPl18_ρ [MlKemPlacement] (sym : String) :
    mlkemPl18.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem mlkemPl14_ρ [MlKemPlacement] (sym : String) :
    mlkemPl14.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

/-! ## Prefix byte-write collapse (`writePrefix`) -/

private def writePrefix (bs : List (BitVec 8)) (f : Nat → BitVec 8) : Nat → List (BitVec 8)
  | 0 => bs
  | k + 1 => ByteSlice.write8 (writePrefix bs f k) k (f k)

private theorem writePrefix_length (bs : List (BitVec 8)) (f : Nat → BitVec 8) :
    ∀ k, k ≤ bs.length → (writePrefix bs f k).length = bs.length
  | 0, _ => rfl
  | k + 1, hk => by
    dsimp only [writePrefix]
    have ih := writePrefix_length bs f k (by omega)
    rw [ByteSlice.write8_length _ k (f k) (by omega), ih]

private theorem getD_writePrefix (bs : List (BitVec 8)) (f : Nat → BitVec 8) :
    ∀ k, k ≤ bs.length → ∀ i,
      (writePrefix bs f k).getD i 0#8 = if i < k then f i else bs.getD i 0#8
  | 0, _, _ => by simp [writePrefix]
  | k + 1, hk, i => by
    dsimp only [writePrefix]
    have hlen : (writePrefix bs f k).length = bs.length := writePrefix_length bs f k (by omega)
    rw [ByteSlice.getD_write8 _ k (f k) i 0#8 (by omega), getD_writePrefix bs f k (by omega) i]
    by_cases hik : i = k
    · subst hik; simp
    · by_cases hlt : i < k
      · have hlt' : i < k + 1 := by omega
        simp [hik, hlt, hlt']
      · have hlt' : ¬ i < k + 1 := by omega
        simp [hik, hlt, hlt']

private theorem writePrefix_eq_of_length {bs target : List (BitVec 8)} {f : Nat → BitVec 8}
    {n : Nat} (hbs : bs.length = n) (htarget : target.length = n)
    (hf : ∀ i, i < n → f i = target.getD i 0#8) :
    writePrefix bs f n = target := by
  apply ByteSlice.ext_getD
  · rw [writePrefix_length bs f n (by omega), hbs, htarget]
  · intro i hi
    rw [writePrefix_length bs f n (by omega), hbs] at hi
    rw [getD_writePrefix bs f n (by omega) i]
    simp only [hi, ↓reduceIte]
    exact hf i hi

/-! ## Constant-time mask identity -/

private theorem select_mask_byte (c : Bool) (l r : BitVec 8) :
    BitVec.zeroExtend 8
      ((BitVec.zeroExtend 64 r &&& BitVec.zeroExtend 64 (0#32 - if c then 0#32 else 1#32)) |||
        (BitVec.zeroExtend 64 l &&& BitVec.zeroExtend 64 ((if c then 0#32 else 1#32) - 1#32))) =
      (if c then l else r) := by
  cases c <;> {
    ext i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  }

/-! ## Stack frame split/join helpers for `B18` (`80` B) and `B14` (`112` B) -/

private theorem satisfies_stackAt80_six {m : Memory} {sp : BitVec 64} {R : SepProp}
    (hm : m ⊨ stackAt sp 80 ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 : BitVec 64),
      m ⊨ (stackAt (sp - 48#64) 32 ∗
        ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
        ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
        ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ∗ R := by
  rw [stackAt_frame sp 80 6 (by decide),
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

private theorem stackAt80_six_entails (sp : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (stackAt (sp - 48#64) 32 ∗
      ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
      ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
      ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢ stackAt sp 80 := by
  rw [stackAt_frame sp 80 6 (by decide),
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

private theorem satisfies_stackAt112_four {m : Memory} {sp : BitVec 64} {R : SepProp}
    (hm : m ⊨ stackAt sp 112 ∗ R) :
    ∃ (w0 w1 w2 w3 : BitVec 64),
      m ⊨ (stackAt (sp - 32#64) 80 ∗
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ∗ R := by
  rw [stackAt_frame sp 112 4 (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide), cells_zero] at hm
  simp only [sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  rcases hm with ⟨w0, w1, w2, w3, hm⟩
  exact ⟨w0, w1, w2, w3, Satisfies.mono (by sep_frame) hm⟩

private theorem stackAt112_four_entails (sp : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    (stackAt (sp - 32#64) 80 ∗
      ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
      ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢ stackAt sp 112 := by
  rw [stackAt_frame sp 112 4 (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide), cells_zero]
  simp only [sepConj_emp]
  exact sepConj_mono_right
    (Entails.sepExists_right w0 (sepConj_mono_right
      (Entails.sepExists_right w1 (sepConj_mono_right
        (Entails.sepExists_right w2 (sepConj_mono_right
          (Entails.sepExists_right w3 (Entails.refl _))))))))

public section

/-- Base `B18`/`B14` spec without `NonSyscallPreserved` (used by `B14` and `B16` before outer
    `mlkemBlockConstOk_withNonSyscallPreserved` lifting). -/
@[expose] def mlkemSelectCtBaseSpec (stkBytes : Nat) : Spec CtSelectArgs where
  pre := (mlkemSelectCtROSpec stkBytes).pre
  post := fun a s0 _sf =>
    (a.outPtr ↦ₛ (if a.sel == 0#8 then a.lhs else a.rhs)) ∗
      (a.lhsPtr ↦ᵣ a.lhs) ∗ (a.rhsPtr ↦ᵣ a.rhs) ∗ stackAt s0.sp stkBytes
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

set_option maxHeartbeats 400000 in
theorem blk18_select_ct_base_ok : MlKemBlockConstOk 18 (mlkemSelectCtBaseSpec 80) := by
  intro _
  refine mlkemCaller_ok (j := 18) mlkemPC18 mlkemPl18 (spec := mlkemSelectCtBaseSpec 80)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemSelectCtBaseSpec,
    mlkemSelectCtROSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨⟨hx0, hx1, hx2, hx3, hsel, hlhs, hrhs⟩, hspat⟩ := hpre_body
  have hsel' : BitVec.zeroExtend 8 (s0.readReg64 (Reg.gpr 4#5)) = a.sel := by
    simpa [State.readReg32] using hsel
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = a.outPtr := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = a.lhsPtr := hx1
  have hx2' : s0.readReg64 (Reg.gpr 2#5) = 32#64 := hx2
  have hx3' : s0.readReg64 (Reg.gpr 3#5) = a.rhsPtr := hx3
  have hspat_stk : s0.mem ⊨ stackAt s0.sp 80 ∗
      (memRegion a.outPtr 32 ∗ (a.lhsPtr ↦ᵣ a.lhs) ∗ (a.rhsPtr ↦ᵣ a.rhs) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  obtain ⟨w0, w1, w2, w3, w4, w5, hspat'⟩ := satisfies_stackAt80_six hspat_stk
  refine ⟨memRegion a.outPtr 32 ∗ (a.lhsPtr ↦ᵣ a.lhs) ∗ (a.rhsPtr ↦ᵣ a.rhs) ∗
    stackAt (s0.sp - 48#64) 32 ∗
    ((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗
    ((s0.sp - 32#64) ↦₆₄ w2) ∗ ((s0.sp - 24#64) ↦₆₄ w3) ∗
    ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5),
    Satisfies.mono (by sep_frame) hspat', ?_⟩
  apply SepWP.memRegion_bytes a.outPtr 32
  intro out₀ hout₀
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk12_is_non_zero_base_ok a.sel
  wp_steps 90
  wp_steps 90
  wp_steps 90
  have hout_eq :
      writePrefix (ByteSlice.write64 (ByteSlice.write64 out₀ 17 0#64) 24 0#64)
        (fun i => if (a.sel == 0#8) = true then a.lhs.getD i 0#8 else a.rhs.getD i 0#8) 32 =
      (if a.sel == 0#8 then a.lhs else a.rhs) := by
    apply writePrefix_eq_of_length
    · rw [ByteSlice.write64_length _ 24 0#64
        (by rw [ByteSlice.write64_length _ 17 0#64 (by omega)]; omega),
        ByteSlice.write64_length _ 17 0#64 (by omega), hout₀]
    · split <;> assumption
    · intro i _hi
      cases (a.sel == 0#8) <;> rfl
  simp only [select_mask_byte]
  change SepWP _ _ _
    (stackAt (s0.sp - 48#64) 32 ∗
      (a.outPtr ↦ₛ writePrefix (ByteSlice.write64 (ByteSlice.write64 out₀ 17 0#64) 24 0#64)
        (fun i => if (a.sel == 0#8) = true then a.lhs.getD i 0#8 else a.rhs.getD i 0#8) 32) ∗ _)
    _ _
  rw [hout_eq]
  apply SepWP.weaken_pre
    (Entails.trans
      (by sep_frame : _ ⊢
        (a.outPtr ↦ₛ (if a.sel == 0#8 then a.lhs else a.rhs)) ∗
        (a.lhsPtr ↦ᵣ a.lhs) ∗ (a.rhsPtr ↦ᵣ a.rhs) ∗
        (stackAt (s0.sp - 48#64) 32 ∗
          ((s0.sp - 48#64) ↦₆₄ _) ∗ ((s0.sp - 40#64) ↦₆₄ _) ∗
          ((s0.sp - 32#64) ↦₆₄ _) ∗ ((s0.sp - 24#64) ↦₆₄ _) ∗
          ((s0.sp - 16#64) ↦₆₄ _) ∗ ((s0.sp - 8#64) ↦₆₄ _)))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt80_six_entails s0.sp _ _ _ _ _ _)))))
  wp_done

theorem blk14_select_ss_base_ok : MlKemBlockConstOk 14 (mlkemSelectCtBaseSpec 112) := by
  intro _
  refine mlkemCaller_ok (j := 14) mlkemPC14 mlkemPl14 (spec := mlkemSelectCtBaseSpec 112)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemSelectCtBaseSpec,
    mlkemSelectCtROSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨⟨hx0, hx1, hx2, hx3, hsel, hlhs, hrhs⟩, hspat⟩ := hpre_body
  have hsel' : BitVec.zeroExtend 8 (s0.readReg64 (Reg.gpr 4#5)) = a.sel := by
    simpa [State.readReg32] using hsel
  have hspat_stk : s0.mem ⊨ stackAt s0.sp 112 ∗
      (memRegion a.outPtr 32 ∗ (a.lhsPtr ↦ᵣ a.lhs) ∗ (a.rhsPtr ↦ᵣ a.rhs) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  obtain ⟨w0, w1, w2, w3, hspat'⟩ := satisfies_stackAt112_four hspat_stk
  refine ⟨memRegion a.outPtr 32 ∗ (a.lhsPtr ↦ᵣ a.lhs) ∗ (a.rhsPtr ↦ᵣ a.rhs) ∗
    stackAt (s0.sp - 32#64) 80 ∗
    ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
    ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3),
    Satisfies.mono (by sep_frame) hspat', ?_⟩
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk18_select_ct_base_ok a
  wp_steps
  apply SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (stackAt112_four_entails s0.sp _ _ _ _))))
  wp_done

/-- `B18` (`select_ct`) `32`-byte constant-time selection contract (`80`-byte stack)
    with `NonSyscallPreserved`. -/
theorem blk18_select_ct_ok : MlKemBlockConstOk 18 (mlkemSelectCtROSpec 80) := by
  intro _
  exact (mlkemConstOk_map_ct (spec' := mlkemSelectCtROSpec 80)
    (mlkemBlockConstOk_withNonSyscallPreserved blk18_select_ct_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemSelectCtBaseSpec, mlkemSelectCtROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemSelectCtBaseSpec, mlkemSelectCtROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun args R _s0 hpre => ⟨args, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemSelectCtBaseSpec, mlkemSelectCtROSpec] at hpost ⊢
      exact hpost⟩)

/-- `B14` (`select_shared_secret_in_constant_time`) `32`-byte constant-time selection contract
    (`112`-byte stack) with `NonSyscallPreserved`. -/
theorem blk14_select_ss_ok : MlKemBlockConstOk 14 (mlkemSelectCtROSpec 112) := by
  intro _
  exact (mlkemConstOk_map_ct (spec' := mlkemSelectCtROSpec 112)
    (mlkemBlockConstOk_withNonSyscallPreserved blk14_select_ss_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemSelectCtBaseSpec, mlkemSelectCtROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemSelectCtBaseSpec, mlkemSelectCtROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun args R _s0 hpre => ⟨args, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemSelectCtBaseSpec, mlkemSelectCtROSpec] at hpost ⊢
      exact hpost⟩)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.SelectCt

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.LookupTableProj
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Variable-Base Edwards Scalar Multiplication Proofs

Pure bridge (`edVarBaseMul_spec`) and machine-code proofs in `dalekCliMultiLib` for
`<EdwardsPoint as Mul<Scalar>>::mul` (`edwards_point_mul_scalar_ok_of`,
`edwards_point_mul_scalar_ro_ok_of`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.VariableBaseMul

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (
  p25519 edD edD2 fpMul fpNeg EdPoint EdExtPoint edZero edExtZero
  edOnCurve edNeg edAdd edSmul edExtToAffine leBytesToNat)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase dalekCaller_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51ValOfBytes fe51_one fe51OneBytes fe51_edwards_d2 fe51EdwardsD2Bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded scalarRadix16Digits scalarRadix16Digits_length
  Fe51MulOk Fe51MulRoRightOk ScalarAsRadix16Ok ScalarAsRadix16RoOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes
  edProjDouble edAsExtended edAddProjNiels
  edExtToProjNiels projNielsTableStep projNielsTablePoints fe51ProjNielsTable8Bounded
  edSelectProjNiels edSelectProjNielsPoints edSelectProjNiels_eq_points
  edDouble4 edVarBaseStep edVarBaseLoopWith edVarBaseLoop edVarBaseMul
  ProjectivePointDoubleOk EdwardsPointAddProjNielsOk
  LookupTableProjNielsFromOk LookupTableProjNielsSelectOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs (
  EdwardsPointMulScalarOk EdwardsPointMulScalarRoOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add write64_length_eq
  readLE_write64_self' readLE_write64_ne readLE_append_left readLE_append_right
  fold_fe51ValOfBytes edAsExtended_of_append4
  fe51_mul_post_props proj_copy15_loop_post
  sepWP_abstract_bytes sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_split4_160 sepWP_merge4_160 sepWP_merge4_stack_bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (fe51LimbsBoundedAt_mono)
open scoped LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  fe51OneBytes_length fe51One_readLE_0 fe51One_readLE_8 fe51One_readLE_16 fe51One_readLE_24)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.LookupTableProj (
  lookup_table_proj_niels_from_ok_of lookup_table_proj_niels_select_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  Fp Fp.ofNat_ne_zero_iff Fp.ofNat_edD2 EdExtValid edOnCurve_edZero edZero_edAdd
  edExtToAffine_fp_x edExtToAffine_fp_y edExtToAffine_edExtZero edExtValid_edExtZero
  edNatSmul edNatSmul_one edNatSmul_succ edSmul_eq_edNatSmul)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (leBytesToNat_lt)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1 (
  EdCompValid edCompToAffine edAsExtended_toAffine edExtValid_edAsExtended
  edDouble4_spec EdProjNielsValid edProjNielsValid_neg
  edAddProjNiels_toAffine edCompValid_edAddProjNiels)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul2 (
  edIntSmul edOnCurve_edIntSmul edIntSmul_zero edIntSmul_ofNat edIntSmul_add edIntSmul_mul
  signedRadix16Val scalarRadix16Digits_spec)

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 33 dalekCliMultiLib DalekCliPlacement 219 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl33_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl33.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

/-! ## 1. Pure Mathematical Bridge Helpers (`edVarBaseMul` → `edSmul`) -/

private theorem edExtToProjNiels_valid {P : EdExtPoint} (hP : EdExtValid P) :
    EdProjNielsValid (edExtToProjNiels P) (edExtToAffine P) where
  on_curve := hP.on_curve
  z_ne_zero := by dsimp only [edExtToProjNiels]; rw [Fp.ofNat_mod]; exact hP.z_ne_zero
  ypx_eq := by
    have hZ := hP.z_ne_zero
    dsimp only [edExtToProjNiels]
    rw [edExtToAffine_fp_x P, edExtToAffine_fp_y P]
    simp only [Fp.ofNat_fpAdd, Fp.ofNat_mod]; grind
  ymx_eq := by
    have hZ := hP.z_ne_zero
    dsimp only [edExtToProjNiels]
    rw [edExtToAffine_fp_x P, edExtToAffine_fp_y P]
    simp only [Fp.ofNat_fpSub, Fp.ofNat_mod]; grind
  t2d_eq := by
    have hZ := hP.z_ne_zero
    have hTZ := hP.tz_eq_xy
    dsimp only [edExtToProjNiels]
    rw [edExtToAffine_fp_x P, edExtToAffine_fp_y P]
    simp only [Fp.ofNat_fpMul, Fp.ofNat_mod, Fp.ofNat_edD2]; grind

private theorem projNielsTablePoints_valid {A : EdExtPoint} (hA : EdExtValid A) :
    ∀ i : Nat, EdProjNielsValid (projNielsTablePoints A i) (edNatSmul (i + 1) (edExtToAffine A))
  | 0 => by
    rw [Nat.zero_add, edNatSmul_one hA.on_curve]
    exact edExtToProjNiels_valid hA
  | i + 1 => by
    have ih := projNielsTablePoints_valid hA i
    dsimp only [projNielsTablePoints, projNielsTableStep]
    have hC : EdCompValid (edAddProjNiels A (projNielsTablePoints A i)) :=
      edCompValid_edAddProjNiels hA ih
    have hE : EdExtValid (edAsExtended (edAddProjNiels A (projNielsTablePoints A i))) :=
      edExtValid_edAsExtended hC
    have haff : edExtToAffine (edAsExtended (edAddProjNiels A (projNielsTablePoints A i))) =
        edNatSmul (i + 1 + 1) (edExtToAffine A) := by
      rw [edAsExtended_toAffine hC, edAddProjNiels_toAffine hA ih, ← edNatSmul_succ]
    rw [← haff]
    exact edExtToProjNiels_valid hE

private theorem edProjNielsValid_identity : EdProjNielsValid ⟨1, 1, 1, 0⟩ edZero where
  on_curve := edOnCurve_edZero
  z_ne_zero := by rw [Fp.ofNat_ne_zero_iff]; decide
  ypx_eq := by simp [edZero]; grind
  ymx_eq := by simp [edZero]; grind
  t2d_eq := by simp [edZero]; grind

private theorem bv8_radix16_cases :
    ∀ x : BitVec 8, (-8 ≤ x.toInt ∧ x.toInt ≤ 8) →
      (x = 0#8 ∨
       x = 1#8 ∨ x = 2#8 ∨ x = 3#8 ∨ x = 4#8 ∨ x = 5#8 ∨ x = 6#8 ∨ x = 7#8 ∨ x = 8#8 ∨
       x = -1#8 ∨ x = -2#8 ∨ x = -3#8 ∨ x = -4#8 ∨ x = -5#8 ∨ x = -6#8 ∨ x = -7#8 ∨ x = -8#8) := by
  decide

private theorem edSelectProjNielsPoints_pos {T : Nat → EdExtPoint} {Q : EdPoint}
    (x : BitVec 8) (j : Nat)
    (hx : edSelectProjNielsPoints T x = T j)
    (hto : x.toInt = Int.ofNat (j + 1))
    (hj : EdProjNielsValid (T j) (edNatSmul (j + 1) Q)) :
    EdProjNielsValid (edSelectProjNielsPoints T x) (edIntSmul x.toInt Q) := by
  rw [hx, hto, edIntSmul_ofNat]; exact hj

private theorem edSelectProjNielsPoints_neg {T : Nat → EdExtPoint} {Q : EdPoint}
    (x : BitVec 8) (j : Nat)
    (hx : edSelectProjNielsPoints T x = ⟨(T j).Y, (T j).X, (T j).Z, fpNeg (T j).T⟩)
    (hneg : ¬(x.toInt ≥ 0)) (habs : (-x.toInt).toNat = j + 1)
    (hj : EdProjNielsValid (T j) (edNatSmul (j + 1) Q)) :
    EdProjNielsValid (edSelectProjNielsPoints T x) (edIntSmul x.toInt Q) := by
  have hint : edIntSmul x.toInt Q = edNeg (edNatSmul (j + 1) Q) := by
    unfold edIntSmul; simp only [hneg, ↓reduceIte, habs]
  rw [hx, hint]
  exact edProjNielsValid_neg hj

private theorem edSelectProjNielsPoints_valid {A : EdExtPoint} {d : BitVec 8}
    (hA : EdExtValid A) (hd : -8 ≤ d.toInt ∧ d.toInt ≤ 8) :
    EdProjNielsValid (edSelectProjNielsPoints (projNielsTablePoints A) d)
      (edIntSmul d.toInt (edExtToAffine A)) := by
  have h0 := projNielsTablePoints_valid hA 0
  have h1 := projNielsTablePoints_valid hA 1
  have h2 := projNielsTablePoints_valid hA 2
  have h3 := projNielsTablePoints_valid hA 3
  have h4 := projNielsTablePoints_valid hA 4
  have h5 := projNielsTablePoints_valid hA 5
  have h6 := projNielsTablePoints_valid hA 6
  have h7 := projNielsTablePoints_valid hA 7
  rcases bv8_radix16_cases d hd with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change EdProjNielsValid ⟨1, 1, 1, 0⟩ (edIntSmul (0#8).toInt (edExtToAffine A))
    rw [show (0#8).toInt = 0 by decide, edIntSmul_zero]
    exact edProjNielsValid_identity
  · exact edSelectProjNielsPoints_pos 1#8 0 rfl (by decide) h0
  · exact edSelectProjNielsPoints_pos 2#8 1 rfl (by decide) h1
  · exact edSelectProjNielsPoints_pos 3#8 2 rfl (by decide) h2
  · exact edSelectProjNielsPoints_pos 4#8 3 rfl (by decide) h3
  · exact edSelectProjNielsPoints_pos 5#8 4 rfl (by decide) h4
  · exact edSelectProjNielsPoints_pos 6#8 5 rfl (by decide) h5
  · exact edSelectProjNielsPoints_pos 7#8 6 rfl (by decide) h6
  · exact edSelectProjNielsPoints_pos 8#8 7 rfl (by decide) h7
  · exact edSelectProjNielsPoints_neg (-1#8) 0 rfl (by decide) (by decide) h0
  · exact edSelectProjNielsPoints_neg (-2#8) 1 rfl (by decide) (by decide) h1
  · exact edSelectProjNielsPoints_neg (-3#8) 2 rfl (by decide) (by decide) h2
  · exact edSelectProjNielsPoints_neg (-4#8) 3 rfl (by decide) (by decide) h3
  · exact edSelectProjNielsPoints_neg (-5#8) 4 rfl (by decide) (by decide) h4
  · exact edSelectProjNielsPoints_neg (-6#8) 5 rfl (by decide) (by decide) h5
  · exact edSelectProjNielsPoints_neg (-7#8) 6 rfl (by decide) (by decide) h6
  · exact edSelectProjNielsPoints_neg (-8#8) 7 rfl (by decide) (by decide) h7

private theorem signedRadix16Val_drop_step (digits : List (BitVec 8)) (m : Nat)
    (hm : m < digits.length) :
    signedRadix16Val (digits.drop m) =
      (digits.getD m 0#8).toInt + 16 * signedRadix16Val (digits.drop (m + 1)) := by
  induction m generalizing digits with
  | zero =>
    rcases digits with _ | ⟨x, xs⟩
    · simp at hm
    · simp [signedRadix16Val]
  | succ k ih =>
    rcases digits with _ | ⟨x, xs⟩
    · simp at hm
    · simp only [List.drop_succ_cons, List.getD_cons_succ]
      exact ih xs (by simp at hm; omega)

private theorem edVarBaseLoopWith_inv {α : Type} (step : Nat → α → α) (inv : Nat → α → Prop)
    (hstep : ∀ k x, k < 63 → inv (k + 1) x → inv k (step k x)) :
    ∀ m, m ≤ 63 → ∀ x, inv m x → inv 0 (edVarBaseLoopWith step m x)
  | 0, _, _, hx => hx
  | m + 1, hm, x, hx =>
    edVarBaseLoopWith_inv step inv hstep m (Nat.le_of_succ_le hm) (step m x)
      (hstep m x (Nat.lt_of_succ_le hm) hx)

private theorem edVarBaseStep_spec {A C : EdExtPoint} {d : BitVec 8}
    (hA : EdExtValid A) (hC : EdCompValid C)
    (hd : -8 ≤ d.toInt ∧ d.toInt ≤ 8) :
    EdCompValid (edVarBaseStep (projNielsTablePoints A) d C) ∧
    edCompToAffine (edVarBaseStep (projNielsTablePoints A) d C) =
      edAdd (edNatSmul 16 (edCompToAffine C)) (edIntSmul d.toInt (edExtToAffine A)) := by
  unfold edVarBaseStep
  have hE : EdExtValid (edAsExtended C) := edExtValid_edAsExtended hC
  obtain ⟨hD4_v, hD4_a⟩ := edDouble4_spec hE
  have hSel := edSelectProjNielsPoints_valid hA hd
  generalize edDouble4 (edAsExtended C) = D at hD4_v hD4_a ⊢
  generalize edSelectProjNielsPoints (projNielsTablePoints A) d = N at hSel ⊢
  refine ⟨edCompValid_edAddProjNiels hD4_v hSel, ?_⟩
  rw [edAddProjNiels_toAffine hD4_v hSel, hD4_a, edAsExtended_toAffine hC]

private theorem edVarBaseLoop_spec {A : EdExtPoint} {digits : List (BitVec 8)}
    (hA : EdExtValid A)
    (hlen : digits.length = 64)
    (hdigits : ∀ k < 64, -8 ≤ (digits.getD k 0#8).toInt ∧ (digits.getD k 0#8).toInt ≤ 8)
    (m : Nat) (hm : m ≤ 63) (C : EdExtPoint)
    (hC : EdCompValid C)
    (hC_aff : edCompToAffine C = edIntSmul (signedRadix16Val (digits.drop m)) (edExtToAffine A)) :
    EdCompValid (edVarBaseLoop (projNielsTablePoints A) digits m C) ∧
    edCompToAffine (edVarBaseLoop (projNielsTablePoints A) digits m C) =
      edIntSmul (signedRadix16Val digits) (edExtToAffine A) := by
  have h0 := edVarBaseLoopWith_inv
    (fun k acc => edVarBaseStep (projNielsTablePoints A) (digits.getD k 0#8) acc)
    (fun k acc => EdCompValid acc ∧
      edCompToAffine acc = edIntSmul (signedRadix16Val (digits.drop k)) (edExtToAffine A))
    (fun k acc hk ⟨hacc_v, hacc_a⟩ => by
      obtain ⟨hS_v, hS_a⟩ := edVarBaseStep_spec hA hacc_v (hdigits k (by omega))
      refine ⟨hS_v, ?_⟩
      rw [hS_a, hacc_a, ← edIntSmul_ofNat 16,
          ← edIntSmul_mul (Int.ofNat 16) _ hA.on_curve,
          ← edIntSmul_add _ _ hA.on_curve,
          signedRadix16Val_drop_step digits k (by omega), Int.add_comm]
      rfl)
    m hm C ⟨hC, hC_aff⟩
  unfold edVarBaseLoop
  simpa only [List.drop_zero] using h0

private theorem edVarBaseMul_spec_aux {point_bs s_bs : List (BitVec 8)}
    (hA : EdExtValid (edExtOfBytes point_bs))
    (hs_len : s_bs.length = 32)
    (hs_31 : (s_bs.getD 31 0#8).toNat ≤ 127) :
    EdExtValid (edVarBaseMul point_bs s_bs) ∧
    edExtToAffine (edVarBaseMul point_bs s_bs) =
      edSmul (leBytesToNat s_bs) (edExtToAffine (edExtOfBytes point_bs)) := by
  dsimp only [edVarBaseMul]
  have hlen64 : (scalarRadix16Digits s_bs).length = 64 := scalarRadix16Digits_length s_bs
  obtain ⟨hdigits, hval⟩ := scalarRadix16Digits_spec hs_len hs_31
  have hSel63 := edSelectProjNielsPoints_valid hA (hdigits 63 (by decide))
  have hdrop64 : (scalarRadix16Digits s_bs).drop 64 = [] := List.drop_eq_nil_of_le (by omega)
  have hC_init : EdCompValid (edAddProjNiels edExtZero
      (edSelectProjNielsPoints (projNielsTablePoints (edExtOfBytes point_bs))
        ((scalarRadix16Digits s_bs).getD 63 0#8))) ∧
    edCompToAffine (edAddProjNiels edExtZero
      (edSelectProjNielsPoints (projNielsTablePoints (edExtOfBytes point_bs))
        ((scalarRadix16Digits s_bs).getD 63 0#8))) =
      edIntSmul (signedRadix16Val ((scalarRadix16Digits s_bs).drop 63))
        (edExtToAffine (edExtOfBytes point_bs)) := by
    generalize edSelectProjNielsPoints (projNielsTablePoints (edExtOfBytes point_bs))
      ((scalarRadix16Digits s_bs).getD 63 0#8) = N63 at hSel63 ⊢
    refine ⟨edCompValid_edAddProjNiels edExtValid_edExtZero hSel63, ?_⟩
    rw [edAddProjNiels_toAffine edExtValid_edExtZero hSel63, edExtToAffine_edExtZero,
        edZero_edAdd (edOnCurve_edIntSmul _ hA.on_curve),
        signedRadix16Val_drop_step (scalarRadix16Digits s_bs) 63 (by omega), hdrop64]
    simp [signedRadix16Val]
  obtain ⟨hC_fin, hC_fin_aff⟩ :=
    edVarBaseLoop_spec hA hlen64 hdigits 63 (by decide) _ hC_init.1 hC_init.2
  generalize edVarBaseLoop (projNielsTablePoints (edExtOfBytes point_bs))
    (scalarRadix16Digits s_bs) 63 _ = C_fin at hC_fin hC_fin_aff ⊢
  refine ⟨edExtValid_edAsExtended hC_fin, ?_⟩
  have hlt : leBytesToNat s_bs < 2 ^ 256 := by
    have h1 := leBytesToNat_lt s_bs
    rwa [hs_len, show 256 ^ 32 = 2 ^ 256 by decide] at h1
  rw [edAsExtended_toAffine hC_fin, hC_fin_aff, hval, edIntSmul_ofNat,
      ← edSmul_eq_edNatSmul hlt hA.on_curve]

/-! ## 2. Stack, Completed-Point Split/Merge, & Loop Helpers for `B33` -/

private def edCompDoubleStep (C : EdExtPoint) : EdExtPoint :=
  edProjDouble (fpMul C.X C.T) (fpMul C.Y C.Z) (fpMul C.Z C.T)

attribute [local irreducible] edProjDouble fpMul in
private theorem edCompDoubleStep_4_eq (C : EdExtPoint) :
    edAsExtended (edCompDoubleStep (edCompDoubleStep (edCompDoubleStep (edCompDoubleStep C)))) =
      edDouble4 (edAsExtended C) := rfl

private theorem sepWP_resize_callee_2480 (sp0 : BitVec 64) (low k off_k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 2480 := by decide) (hok : 2016 + k = off_k := by decide)
    (hf : Full = memRegion (sp0 - 4496#64) 2480 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s
      ((memRegion (sp0 - BitVec.ofNat 64 off_k) k ∗
        stackAt (sp0 - BitVec.ofNat 64 off_k) low) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha0 : sp0 - 4496#64 = sp0 - 2016#64 - 2480#64 := by rw [BitVec.sub_sub]; rfl
  have ha : sp0 - 2016#64 - BitVec.ofNat 64 k = sp0 - BitVec.ofNat 64 off_k := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, hok]
  rw [hf, ha0]; change SepWP prog target_pc s (stackAt (sp0 - 2016#64) 2480 ∗ P) post oom
  rw [← hsum, stackAt_region (sp0 - 2016#64) low k (by omega),
      sepConj_comm (stackAt _ _) (memRegion _ _)]
  conv => arg 4; arg 1; rw [ha]
  exact hnext

private theorem sepWP_unresize_callee_2480 (sp0 : BitVec 64) (low k off_k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 2480 := by decide) (hok : 2016 + k = off_k := by decide)
    (hf : Full = (memRegion (sp0 - BitVec.ofNat 64 off_k) k ∗
        stackAt (sp0 - BitVec.ofNat 64 off_k) low) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp0 - 4496#64) 2480 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha0 : sp0 - 2016#64 - 2480#64 = sp0 - 4496#64 := by rw [BitVec.sub_sub]; rfl
  have ha : sp0 - BitVec.ofNat 64 off_k = sp0 - 2016#64 - BitVec.ofNat 64 k := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, hok]
  rw [hf, ha, sepConj_comm (memRegion _ _) (stackAt _ _),
      ← stackAt_region (sp0 - 2016#64) low k (by omega), hsum]
  change SepWP prog target_pc s (memRegion (sp0 - 2016#64 - 2480#64) 2480 ∗ P) post oom
  rw [ha0]; exact hnext

private theorem sepWP_split4_completed_384 (sp : BitVec 64) (C : EdExtPoint) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 384#64) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (h0 : fe51LimbsBoundedAt bs 0 (2 ^ 54) := by assumption)
    (h40 : fe51LimbsBoundedAt bs 40 (2 ^ 54) := by assumption)
    (h80 : fe51LimbsBoundedAt bs 80 (2 ^ 54) := by assumption)
    (h120 : fe51LimbsBoundedAt bs 120 (2 ^ 54) := by assumption)
    (hval : edExtOfBytes bs = C := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      fe51LimbsBounded b0 (2 ^ 54) → fe51LimbsBounded b1 (2 ^ 54) →
      fe51LimbsBounded b2 (2 ^ 54) → fe51LimbsBounded b3 (2 ^ 54) →
      fe51ValOfBytes b0 % p25519 = C.X → fe51ValOfBytes b1 % p25519 = C.Y →
      fe51ValOfBytes b2 % p25519 = C.Z → fe51ValOfBytes b3 % p25519 = C.T →
      SepWP prog target_pc s
        ((((sp - 384#64) ↦ₛ b0) ∗ ((sp - 344#64) ↦ₛ b1) ∗
          ((sp - 304#64) ↦ₛ b2) ∗ ((sp - 264#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let b0 := bs.take 40; let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let b1 := d1.take 40; let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  let b2 := d2.take 40; let b3 := d2.drop 40
  have hb0_l : b0.length = 40 := by simp [b0, hbs]
  have hb1_l : b1.length = 40 := by simp [b1, hd1]
  have hb2_l : b2.length = 40 := by simp [b2, hd2]
  have hb3_l : b3.length = 40 := by simp [b3, hd2]
  have hs0 : ((sp - 384#64) ↦ₛ bs) = ((sp - 384#64) ↦ₛ b0) ∗ ((sp - 344#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 384 40]
  have hs1 : ((sp - 344#64) ↦ₛ d1) = ((sp - 344#64) ↦ₛ b1) ∗ ((sp - 304#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 344 40]
  have hs2 : ((sp - 304#64) ↦ₛ d2) = ((sp - 304#64) ↦ₛ b2) ∗ ((sp - 264#64) ↦ₛ b3) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 304 40]
  have hbs_eq : bs = b0 ++ (b1 ++ (b2 ++ b3)) := by
    have e0 : b0 ++ d1 = bs := List.take_append_drop 40 bs
    have e1 : b1 ++ d2 = d1 := List.take_append_drop 40 d1
    have e2 : b2 ++ b3 = d2 := List.take_append_drop 40 d2; rw [e2, e1, e0]
  have hr0 (off : Nat) (ho : off + 8 ≤ 40) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b0 off 8 := by
    rw [hbs_eq]; exact readLE_append_left b0 _ off 8 (by omega)
  have hr1 (off : Nat) (ho1 : 40 ≤ off) (ho2 : off + 8 ≤ 80) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b1 (off - 40) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_left b1 _ (off - 40) 8 (by omega)]
  have hr2 (off : Nat) (ho1 : 80 ≤ off) (ho2 : off + 8 ≤ 120) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b2 (off - 80) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_right b1 _ (off - 40) 8 (by omega),
        hb1_l, show off - 40 - 40 = off - 80 by omega, readLE_append_left b2 _ (off - 80) 8 (by omega)]
  have hr3 (off : Nat) (ho1 : 120 ≤ off) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b3 (off - 120) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_right b1 _ (off - 40) 8 (by omega),
        hb1_l, readLE_append_right b2 _ (off - 40 - 40) 8 (by omega), hb2_l, show off - 40 - 40 - 40 = off - 120 by omega]
  unfold fe51LimbsBoundedAt at h0 h40 h80 h120
  simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub] at h0 h40 h80 h120
  have hval' : edExtOfBytes bs = ⟨fe51ValOfBytes b0 % p25519, fe51ValOfBytes b1 % p25519,
      fe51ValOfBytes b2 % p25519, fe51ValOfBytes b3 % p25519⟩ := by
    unfold edExtOfBytes fe51ValAt
    simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub,
      fold_fe51ValOfBytes b0, fold_fe51ValOfBytes b1, fold_fe51ValOfBytes b2, fold_fe51ValOfBytes b3]
  rw [hval] at hval'; rw [hf, hs0, hs1, hs2]
  exact hnext b0 b1 b2 b3 hb0_l hb1_l hb2_l hb3_l ⟨hb0_l, h0⟩ ⟨hb1_l, h40⟩ ⟨hb2_l, h80⟩ ⟨hb3_l, h120⟩
    (congrArg EdExtPoint.X hval').symm (congrArg EdExtPoint.Y hval').symm
    (congrArg EdExtPoint.Z hval').symm (congrArg EdExtPoint.T hval').symm

private theorem sepWP_merge4_stack_384 (sp : BitVec 64) {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 384#64) ↦ₛ b0) ∗ ((sp - 344#64) ↦ₛ b1) ∗
                  ((sp - 304#64) ↦ₛ b2) ∗ ((sp - 264#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption)
    (h2 : b2.length = 40 := by assumption) (h3 : b3.length = 40 := by assumption)
    (hnext : ∀ b160 : List (BitVec 8), b160.length = 160 →
      SepWP prog target_pc s (((sp - 384#64) ↦ₛ b160) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 304#64 + BitVec.ofNat 64 b2.length = sp - 264#64 := by rw [h2]; exact sub_ofNat64_add sp 304 40
  have ha1 : sp - 344#64 + BitVec.ofNat 64 b1.length = sp - 304#64 := by rw [h1]; exact sub_ofNat64_add sp 344 40
  have ha0 : sp - 384#64 + BitVec.ofNat 64 b0.length = sp - 344#64 := by rw [h0]; exact sub_ofNat64_add sp 384 40
  have hm : ((sp - 384#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 384#64) ↦ₛ b0) ∗ ((sp - 344#64) ↦ₛ b1) ∗ ((sp - 304#64) ↦ₛ b2) ∗ ((sp - 264#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) (by simp [List.length_append, h0, h1, h2, h3])

private theorem sepWP_split4_stack_224 (sp : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 224#64) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      SepWP prog target_pc s
        ((((sp - 224#64) ↦ₛ b0) ∗ ((sp - 184#64) ↦ₛ b1) ∗
          ((sp - 144#64) ↦ₛ b2) ∗ ((sp - 104#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - 224#64) ↦ₛ bs) = ((sp - 224#64) ↦ₛ bs.take 40) ∗ ((sp - 184#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 224 40]
  have hs1 : ((sp - 184#64) ↦ₛ d1) = ((sp - 184#64) ↦ₛ d1.take 40) ∗ ((sp - 144#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 184 40]
  have hs2 : ((sp - 144#64) ↦ₛ d2) = ((sp - 144#64) ↦ₛ d2.take 40) ∗ ((sp - 104#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 144 40]
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40)
    (by simp [hbs]) (by simp [hd1]) (by simp [hd2]) (by simp [hd2])

private theorem sepWP_merge4_224_prop (sp : BitVec 64) {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (Q : List (BitVec 8) → Prop)
    (hf : Full = (((sp - 224#64) ↦ₛ b0) ∗ ((sp - 184#64) ↦ₛ b1) ∗
                  ((sp - 144#64) ↦ₛ b2) ∗ ((sp - 104#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption)
    (h2 : b2.length = 40 := by assumption)
    (hQ : Q (b0 ++ (b1 ++ (b2 ++ b3))))
    (hnext : ∀ res_bs : List (BitVec 8), Q res_bs →
      SepWP prog target_pc s (((sp - 224#64) ↦ₛ res_bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 144#64 + BitVec.ofNat 64 b2.length = sp - 104#64 := by rw [h2]; exact sub_ofNat64_add sp 144 40
  have ha1 : sp - 184#64 + BitVec.ofNat 64 b1.length = sp - 144#64 := by rw [h1]; exact sub_ofNat64_add sp 184 40
  have ha0 : sp - 224#64 + BitVec.ofNat 64 b0.length = sp - 184#64 := by rw [h0]; exact sub_ofNat64_add sp 224 40
  have hm : ((sp - 224#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 224#64) ↦ₛ b0) ∗ ((sp - 184#64) ↦ₛ b1) ∗ ((sp - 144#64) ↦ₛ b2) ∗ ((sp - 104#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) hQ

private theorem mul_init_ext_zero_post (dst : List (BitVec 8)) (hdst : dst.length = 160) :
    let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 32 0#64) 72 0#64)
        40 (ByteSlice.readLE fe51OneBytes 0 8)) 48 (ByteSlice.readLE fe51OneBytes 8 8))
        16 0#64) 24 0#64) 0 0#64) 8 0#64)
        56 (ByteSlice.readLE fe51OneBytes 16 8)) 64 (ByteSlice.readLE fe51OneBytes 24 8))
        80 (ByteSlice.readLE fe51OneBytes 0 8)) 88 (ByteSlice.readLE fe51OneBytes 8 8))
        96 (ByteSlice.readLE fe51OneBytes 16 8)) 104 (ByteSlice.readLE fe51OneBytes 24 8))
        120 0#64) 128 0#64) 136 0#64) 144 0#64) 112 0#64) 152 0#64
    fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edExtZero := by
  haveI : HasLenGe dst 160 := ⟨by omega⟩; unfold fe51Point4Bounded fe51LimbsBoundedAt edExtOfBytes edExtZero
  simp (disch := decide) only [fe51ValAt, ↓readLE_write64_self', ↓readLE_write64_ne,
    write64_length_eq, hdst, fe51One_readLE_0, fe51One_readLE_8, fe51One_readLE_16, fe51One_readLE_24]
  decide +kernel

private theorem mul_copy20_post (dst src : List (BitVec 8)) (P : EdExtPoint) (bound : Nat)
    (hdst : dst.length = 160) (hsrc_b : fe51Point4Bounded src bound) (hsrc_v : edExtOfBytes src = P) :
    let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 96 (ByteSlice.readLE src 96 8)) 104 (ByteSlice.readLE src 104 8))
        112 (ByteSlice.readLE src 112 8)) 120 (ByteSlice.readLE src 120 8))
        128 (ByteSlice.readLE src 128 8)) 136 (ByteSlice.readLE src 136 8))
        144 (ByteSlice.readLE src 144 8)) 152 (ByteSlice.readLE src 152 8))
        48 (ByteSlice.readLE src 48 8)) 56 (ByteSlice.readLE src 56 8))
        32 (ByteSlice.readLE src 32 8)) 40 (ByteSlice.readLE src 40 8))
        80 (ByteSlice.readLE src 80 8)) 88 (ByteSlice.readLE src 88 8))
        64 (ByteSlice.readLE src 64 8)) 72 (ByteSlice.readLE src 72 8))
        0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8))
        16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8)
    fe51Point4Bounded buf bound ∧ edExtOfBytes buf = P := by
  haveI : HasLenGe dst 160 := ⟨by omega⟩; obtain ⟨_, h0, h40, h80, h120⟩ := hsrc_b
  unfold fe51Point4Bounded fe51LimbsBoundedAt edExtOfBytes
  simp (disch := decide) only [fe51ValAt, ↓readLE_write64_self', ↓readLE_write64_ne, write64_length_eq, hdst]
  exact ⟨⟨rfl, h0, h40, h80, h120⟩, hsrc_v⟩

private def mulLoopPre (sp0 : BitVec 64)
    (table_bs digits proj_bs ext_bs comp_bs tmp_bs : List (BitVec 8)) (F : SepProp) : SepProp :=
  memRegion (sp0 - 4496#64) 2480 ∗ ((sp0 - 2016#64) ↦ₛ table_bs) ∗
  ((sp0 - 736#64) ↦ₛ digits) ∗ ((sp0 - 672#64) ↦ₛ proj_bs) ∗
  ((sp0 - 544#64) ↦ₛ ext_bs) ∗ ((sp0 - 384#64) ↦ₛ comp_bs) ∗
  ((sp0 - 224#64) ↦ₛ tmp_bs) ∗ F

private theorem sepWP_fold_mulLoopPre (sp0 : BitVec 64)
    {table_bs digits proj_bs ext_bs comp_bs tmp_bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp0 - 4496#64) 2480 ∗ ((sp0 - 2016#64) ↦ₛ table_bs) ∗
      ((sp0 - 736#64) ↦ₛ digits) ∗ ((sp0 - 672#64) ↦ₛ proj_bs) ∗
      ((sp0 - 544#64) ↦ₛ ext_bs) ∗ ((sp0 - 384#64) ↦ₛ comp_bs) ∗
      ((sp0 - 224#64) ↦ₛ tmp_bs)) ∗ F := by sep_frame)
    (hnext : SepWP prog target_pc s
      (mulLoopPre sp0 table_bs digits proj_bs ext_bs comp_bs tmp_bs F) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hm : mulLoopPre sp0 table_bs digits proj_bs ext_bs comp_bs tmp_bs F =
      (memRegion (sp0 - 4496#64) 2480 ∗ ((sp0 - 2016#64) ↦ₛ table_bs) ∗
       ((sp0 - 736#64) ↦ₛ digits) ∗ ((sp0 - 672#64) ↦ₛ proj_bs) ∗
       ((sp0 - 544#64) ↦ₛ ext_bs) ∗ ((sp0 - 384#64) ↦ₛ comp_bs) ∗
       ((sp0 - 224#64) ↦ₛ tmp_bs)) ∗ F := by unfold mulLoopPre; sep_ac_rfl
  rw [hf, ← hm]; exact hnext

private structure MulLoopRegs [DalekCliPlacement] (s0 s : State) (out pc_val x23_val : BitVec 64) : Prop where
  hpc : s.pc = pc_val
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 2016#64
  hx19 : s.readReg64 (Reg.gpr 19#5) = out
  hx20 : s.readReg64 (Reg.gpr 20#5) = s0.sp - 736#64
  hx21 : s.readReg64 (Reg.gpr 21#5) = s0.sp - 384#64
  hx22 : s.readReg64 (Reg.gpr 22#5) = s0.sp - 224#64
  hx23 : s.readReg64 (Reg.gpr 23#5) = x23_val
  hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5)
  hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5)
  hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5)
  hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5)
  hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 64#64
  hvregs : calleeSavedVRegs s = calleeSavedVRegs s0
  hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem

set_option hygiene false in
local macro "prove_mul_double_block" : tactic => `(tactic| (
  intro _ b hb hbase hDouble hMul s0 s target_pc out x23_val
    table_bs digits proj_bs ext_bs comp_bs tmp_bs C F post oom
    hsp0_align hregs hproj_len hcomp_b hcomp_v htmp_len hnext
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx29, hvregs, hcl⟩
  unfold mulLoopPre
  obtain ⟨hcomp_l, hc_0, hc_40, hc_80, hc_120⟩ := hcomp_b
  apply sepWP_split4_completed_384 s0.sp C
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack_224 s0.sp; intro t0 t1 t2 t3 ht0_l ht1_l ht2_l ht3_l
  apply sepWP_resize_callee_2480 s0.sp 2256 224 2240
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [s]; try clear s
  obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w (fpMul C.X C.T)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [sf]; try clear sf
  obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_1 (fpMul C.Y C.Z)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [sf_1]; try clear sf_1
  obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_2 (fpMul C.Z C.T)
  norm_sf 224
  apply sepWP_unresize_callee_2480 s0.sp 2256 224 2240
  apply sepWP_merge4_stack_384 s0.sp; intro comp_mid hcomp_mid_l
  haveI : HasLenGe w 40 := ⟨by omega⟩; haveI : HasLenGe w_1 40 := ⟨by omega⟩
  haveI : HasLenGe w_2 40 := ⟨by omega⟩; haveI : HasLenGe proj_bs 120 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 15
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro _hcl_copy; simp only [arm64_norm] at _hcl_copy
  apply sepWP_abstract_bytes (s0.sp - 672#64)
    (fun buf => buf.length = 120 ∧ fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧ fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) = edCompDoubleStep C)
    (hQ := proj_copy15_loop_post proj_bs w w_1 w_2 (fpMul C.X C.T) (fpMul C.Y C.Z) (fpMul C.Z C.T)
      hproj_len hr0_b hr1_b hr2_b hr0_v hr1_v hr2_v)
  intro proj' ⟨hp_len, hp_0, hp_40, hp_80, hp_val⟩
  unpack_fe51_at hp_0; unpack_fe51_at hp_40; unpack_fe51_at hp_80
  apply sepWP_merge4_stack_bytes s0.sp; intro tmp' htmp'_len
  clear_dead_vars [c0, c1, c2, c3, t0, t1, t2, t3, w, w_1, w_2, proj_bs, comp_bs, tmp_bs]
  apply sepWP_resize_callee_2480 s0.sp 2080 400 2416
  wp_steps; wp_dalek_call hDouble; clean_prev_sf; clear_dead_vars [sf]; try clear sf; norm_sf 400
  apply sepWP_unresize_callee_2480 s0.sp 2080 400 2416
  have hw3_b : fe51Point4Bounded w_3 (2 ^ 54) :=
    ⟨by assumption, fe51LimbsBoundedAt_mono (by assumption), fe51LimbsBoundedAt_mono (by assumption),
     fe51LimbsBoundedAt_mono (by assumption), fe51LimbsBoundedAt_mono (by assumption)⟩
  have hw3_v : edExtOfBytes w_3 = edCompDoubleStep C := by rw [← hp_val]; assumption
  apply sepWP_fold_mulLoopPre s0.sp
  exact hnext _ proj' w_3 tmp'
    ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
     by assumption, by assumption, by assumption, by assumption, by assumption,
     by assumption, by assumption, by assumption, by assumption, by assumption⟩
    hp_len hw3_b hw3_v htmp'_len))

private abbrev MulDoubleBlockType (off_in off_out : BitVec 64) : Prop :=
  ∀ [DalekCliPlacement] (b : BitVec 64), DalekBase dalekCliPl33 b → dalekCliPl33.base = b →
    ProjectivePointDoubleOk → Fe51MulOk →
    ∀ (s0 s : State) (target_pc out x23_val : BitVec 64)
      (table_bs digits proj_bs ext_bs comp_bs tmp_bs : List (BitVec 8))
      (C : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) (oom : State → SepProp),
      s0.spAligned = true →
      MulLoopRegs s0 s out (b + off_in) x23_val →
      proj_bs.length = 120 →
      fe51Point4Bounded comp_bs (2 ^ 54) →
      edExtOfBytes comp_bs = C →
      tmp_bs.length = 160 →
      (∀ (sf' : State) (proj' comp' tmp' : List (BitVec 8)),
        MulLoopRegs s0 sf' out (b + off_out) x23_val →
        proj'.length = 120 →
        fe51Point4Bounded comp' (2 ^ 54) →
        edExtOfBytes comp' = edCompDoubleStep C →
        tmp'.length = 160 →
        SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc sf'
          (mulLoopPre s0.sp table_bs digits proj' ext_bs comp' tmp' F) post oom) →
      SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc s
        (mulLoopPre s0.sp table_bs digits proj_bs ext_bs comp_bs tmp_bs F) post oom

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_double_1 : MulDoubleBlockType 172#64 284#64 := by prove_mul_double_block

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_double_2 : MulDoubleBlockType 284#64 396#64 := by prove_mul_double_block

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_double_3 : MulDoubleBlockType 396#64 508#64 := by prove_mul_double_block

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_double_4 : MulDoubleBlockType 508#64 620#64 := by prove_mul_double_block

private theorem x23_step_val {k : Nat} (hk : k < 63) :
    BitVec.ofNat 64 k - 1#64 = if k == 0 then -1#64 else BitVec.ofNat 64 (k - 1) :=
  (by decide : ∀ j : Fin 63,
    BitVec.ofNat 64 j.val - 1#64 = if j.val == 0 then -1#64 else BitVec.ofNat 64 (j.val - 1)) ⟨k, hk⟩

private theorem x23_bne_zero {k : Nat} (hk : k < 63) :
    ((BitVec.ofNat 64 k != 0#64) = true) = ((!(k == 0)) = true) :=
  (by decide : ∀ j : Fin 63,
    ((BitVec.ofNat 64 j.val != 0#64) = true) = ((!(j.val == 0)) = true)) ⟨k, hk⟩

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_iter_as_extended [DalekCliPlacement]
    (b : BitVec 64) (_hb : DalekBase dalekCliPl33 b) (hbase : dalekCliPl33.base = b) (hMul : Fe51MulOk)
    (s0 s : State) (target_pc out x23_val : BitVec 64)
    (table_bs digits proj_bs ext_bs comp_bs tmp_bs : List (BitVec 8))
    (C4 D4 : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true) (hregs : MulLoopRegs s0 s out (b + 620#64) x23_val)
    (hcomp_b : fe51Point4Bounded comp_bs (2 ^ 54)) (hcomp_v : edExtOfBytes comp_bs = C4)
    (hC4 : edAsExtended C4 = D4) (htmp_len : tmp_bs.length = 160)
    (hnext : ∀ (sf' : State) (comp_mid tmp_d4 : List (BitVec 8)),
      MulLoopRegs s0 sf' out (b + 684#64) x23_val →
      comp_mid.length = 160 → fe51Point4Bounded tmp_d4 (2 ^ 52) → edExtOfBytes tmp_d4 = D4 →
      SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc sf'
        (mulLoopPre s0.sp table_bs digits proj_bs ext_bs comp_mid tmp_d4 F) post oom) :
    SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc s
      (mulLoopPre s0.sp table_bs digits proj_bs ext_bs comp_bs tmp_bs F) post oom := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx29, hvregs, hcl⟩
  unfold mulLoopPre
  obtain ⟨hcomp_l, hc_0, hc_40, hc_80, hc_120⟩ := hcomp_b
  apply sepWP_split4_completed_384 s0.sp C4
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack_224 s0.sp; intro t0 t1 t2 t3 ht0_l ht1_l ht2_l ht3_l
  apply sepWP_resize_callee_2480 s0.sp 2256 224 2240
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [s]; try clear s
  obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w (fpMul C4.X C4.T)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [sf]; try clear sf
  obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_1 (fpMul C4.Y C4.Z)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [sf_1]; try clear sf_1
  obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_2 (fpMul C4.Z C4.T)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [sf]; try clear sf
  obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_3 (fpMul C4.X C4.Y)
  norm_sf 224
  apply sepWP_unresize_callee_2480 s0.sp 2256 224 2240
  apply sepWP_merge4_stack_384 s0.sp; intro comp_mid hcomp_mid_l
  apply sepWP_merge4_224_prop s0.sp (fun res => fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = D4)
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ :=
      edAsExtended_of_append4 w w_1 w_2 w_3 C4 hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    exact ⟨⟨hl, hb0, hb1, hb2, hb3⟩, hv.trans hC4⟩
  intro tmp_d4 ⟨htmp_d4_b, htmp_d4_v⟩
  apply sepWP_fold_mulLoopPre s0.sp
  exact hnext _ comp_mid tmp_d4 ⟨by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, by assumption⟩ hcomp_mid_l htmp_d4_b htmp_d4_v

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_iter_select [DalekCliPlacement]
    (b : BitVec 64) (_hb : DalekBase dalekCliPl33 b) (hbase : dalekCliPl33.base = b)
    (hSelect : LookupTableProjNielsSelectOk) (T : Nat → EdExtPoint) (k : Nat) (hk : k < 63)
    (s0 s : State) (target_pc out : BitVec 64)
    (table_bs digits proj_bs ext_bs comp_mid tmp_d4 : List (BitVec 8))
    (D4 : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true) (hregs : MulLoopRegs s0 s out (b + 684#64) (BitVec.ofNat 64 k))
    (htab_b : fe51ProjNielsTable8Bounded table_bs (2 ^ 54))
    (htab_v : ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice table_bs (160 * i) 160) = T i)
    (hdigits_len : digits.length = 64) (hext_len : ext_bs.length = 160)
    (htmp_d4_b : fe51Point4Bounded tmp_d4 (2 ^ 52)) (htmp_d4_v : edExtOfBytes tmp_d4 = D4)
    (hnext : ∀ (sf' : State) (ext' sel_bs : List (BitVec 8)),
      MulLoopRegs s0 sf' out (b + 760#64) (BitVec.ofNat 64 k) →
      fe51Point4Bounded ext' (2 ^ 52) → edExtOfBytes ext' = D4 →
      fe51Point4Bounded sel_bs (2 ^ 54) →
      edExtOfBytes sel_bs = edSelectProjNielsPoints T (digits.getD k 0#8) →
      SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc sf'
        (mulLoopPre s0.sp table_bs digits proj_bs ext' comp_mid sel_bs F) post oom) :
    SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc s
      (mulLoopPre s0.sp table_bs digits proj_bs ext_bs comp_mid tmp_d4 F) post oom := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx29, hvregs, hcl⟩
  unfold mulLoopPre
  have htmp_d4_l : tmp_d4.length = 160 := htmp_d4_b.1
  haveI : HasLenGe tmp_d4 160 := ⟨by omega⟩; haveI : HasLenGe ext_bs 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 18
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro _hcl_copy; simp only [arm64_norm] at _hcl_copy
  apply sepWP_abstract_bytes (s0.sp - 544#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = D4)
    (hQ := mul_copy20_post ext_bs tmp_d4 D4 (2 ^ 52) hext_len htmp_d4_b htmp_d4_v)
  intro ext' ⟨hext'_b, hext'_v⟩; obtain ⟨htab_l, htab_b8⟩ := htab_b
  apply sepWP_resize_callee_2480 s0.sp 2240 240 2256
  wp_steps; wp_dalek_call hSelect; clean_prev_sf; clear_dead_vars [s]; try clear s; norm_sf 240
  apply sepWP_unresize_callee_2480 s0.sp 2240 240 2256
  have hw_v : edExtOfBytes w = edSelectProjNielsPoints T (digits.getD k 0#8) := by
    rw [show edExtOfBytes w = edSelectProjNiels table_bs (digits.getD k 0#8) by assumption,
        edSelectProjNiels_eq_points _ htab_v]
  apply sepWP_fold_mulLoopPre s0.sp
  exact hnext _ ext' w ⟨by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, by assumption⟩ hext'_b hext'_v (by assumption) hw_v

set_option maxHeartbeats 800000 in
attribute [local irreducible] edDouble4 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_iter_add_branch [DalekCliPlacement]
    (b : BitVec 64) (_hb : DalekBase dalekCliPl33 b) (hbase : dalekCliPl33.base = b)
    (hAdd : EdwardsPointAddProjNielsOk) (T : Nat → EdExtPoint) (k : Nat) (hk : k < 63)
    (s0 s : State) (target_pc out : BitVec 64)
    (table_bs digits proj_bs ext' comp_mid sel_bs : List (BitVec 8))
    (C D4 S : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true) (hregs : MulLoopRegs s0 s out (b + 760#64) (BitVec.ofNat 64 k))
    (hcomp_mid_l : comp_mid.length = 160)
    (hext'_b : fe51Point4Bounded ext' (2 ^ 52)) (hext'_v : edExtOfBytes ext' = D4)
    (hsel_b : fe51Point4Bounded sel_bs (2 ^ 54)) (hsel_v : edExtOfBytes sel_bs = S)
    (hstep : edAddProjNiels D4 S = edVarBaseStep T (digits.getD k 0#8) C)
    (hnext : ∀ (sf' : State) (ext'' comp' tmp' : List (BitVec 8)),
      MulLoopRegs s0 sf' out (if k == 0 then b + 788#64 else b + 172#64)
        (if k == 0 then -1#64 else BitVec.ofNat 64 (k - 1)) →
      ext''.length = 160 → fe51Point4Bounded comp' (2 ^ 54) →
      edExtOfBytes comp' = edVarBaseStep T (digits.getD k 0#8) C → tmp'.length = 160 →
      SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc sf'
        (mulLoopPre s0.sp table_bs digits proj_bs ext'' comp' tmp' F) post oom) :
    SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc s
      (mulLoopPre s0.sp table_bs digits proj_bs ext' comp_mid sel_bs F) post oom := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx29, hvregs, hcl⟩
  unfold mulLoopPre
  obtain ⟨hext'_l, he0, he40, he80, he120⟩ := hext'_b
  replace he0 := fe51LimbsBoundedAt_mono he0 (b2 := 2 ^ 53); unpack_fe51_at he0
  replace he40 := fe51LimbsBoundedAt_mono he40 (b2 := 2 ^ 53); unpack_fe51_at he40
  replace he80 := fe51LimbsBoundedAt_mono he80 (b2 := 2 ^ 54); unpack_fe51_at he80
  replace he120 := fe51LimbsBoundedAt_mono he120 (b2 := 2 ^ 54); unpack_fe51_at he120
  obtain ⟨hsel_l, hs0, hs40, hs80, hs120⟩ := hsel_b
  unpack_fe51_at hs0; unpack_fe51_at hs40; unpack_fe51_at hs80; unpack_fe51_at hs120
  wp_sym_steps 3; apply sepWP_resize_callee_2480 s0.sp 1904 576 2592
  wp_steps; wp_dalek_call hAdd; clean_prev_sf; clear_dead_vars [s]; try clear s; norm_sf 576
  apply sepWP_unresize_callee_2480 s0.sp 1904 576 2592
  have hw_b : fe51Point4Bounded w (2 ^ 54) :=
    ⟨by assumption, fe51LimbsBoundedAt_mono (by assumption), fe51LimbsBoundedAt_mono (by assumption),
     by assumption, fe51LimbsBoundedAt_mono (by assumption)⟩
  have hw_v : edExtOfBytes w = edVarBaseStep T (digits.getD k 0#8) C := by
    rw [show edExtOfBytes w = edAddProjNiels (edExtOfBytes ext') (edExtOfBytes sel_bs) by assumption,
        hext'_v, hsel_v, hstep]
  wp_sym_steps 3; apply sepWP_fold_mulLoopPre s0.sp
  refine hnext _ ext' w sel_bs ⟨?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by assumption⟩ hext'_l hw_b hw_v hsel_l
  · simp only [arm64_norm]
    rw [show (if k == 0 then b + 788#64 else b + 172#64) =
          (if !(k == 0) then b + 172#64 else b + 788#64) by cases (k == 0) <;> rfl]
    exact ite_congr (x23_bne_zero hk) (fun _ => rfl) (fun _ => rfl)
  · simp only [arm64_norm, x23_step_val hk]

attribute [local irreducible] edDouble4 in
private theorem mul_iter_tail [DalekCliPlacement]
    (b : BitVec 64) (hb : DalekBase dalekCliPl33 b) (hbase : dalekCliPl33.base = b)
    (hSelect : LookupTableProjNielsSelectOk) (hAdd : EdwardsPointAddProjNielsOk) (hMul : Fe51MulOk)
    (T : Nat → EdExtPoint) (k : Nat) (hk : k < 63) (s0 s : State) (target_pc out : BitVec 64)
    (table_bs digits proj_bs ext_bs comp_bs tmp_bs : List (BitVec 8))
    (C C4 : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true) (hregs : MulLoopRegs s0 s out (b + 620#64) (BitVec.ofNat 64 k))
    (htab_b : fe51ProjNielsTable8Bounded table_bs (2 ^ 54))
    (htab_v : ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice table_bs (160 * i) 160) = T i)
    (hdigits_len : digits.length = 64) (hext_len : ext_bs.length = 160)
    (hcomp_b : fe51Point4Bounded comp_bs (2 ^ 54)) (hcomp_v : edExtOfBytes comp_bs = C4)
    (hC4 : edAsExtended C4 = edDouble4 (edAsExtended C)) (htmp_len : tmp_bs.length = 160)
    (hnext : ∀ (sf' : State) (ext' comp' tmp' : List (BitVec 8)),
      MulLoopRegs s0 sf' out (if k == 0 then b + 788#64 else b + 172#64)
        (if k == 0 then -1#64 else BitVec.ofNat 64 (k - 1)) →
      ext'.length = 160 → fe51Point4Bounded comp' (2 ^ 54) →
      edExtOfBytes comp' = edVarBaseStep T (digits.getD k 0#8) C → tmp'.length = 160 →
      SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc sf'
        (mulLoopPre s0.sp table_bs digits proj_bs ext' comp' tmp' F) post oom) :
    SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc s
      (mulLoopPre s0.sp table_bs digits proj_bs ext_bs comp_bs tmp_bs F) post oom :=
  mul_iter_as_extended b hb hbase hMul s0 s target_pc out (BitVec.ofNat 64 k)
    table_bs digits proj_bs ext_bs comp_bs tmp_bs C4 (edDouble4 (edAsExtended C)) F post
    hsp0_align hregs hcomp_b hcomp_v hC4 htmp_len
    (fun sf1 comp_mid tmp_d4 hregs1 hc_mid htd4_b htd4_v =>
      mul_iter_select b hb hbase hSelect T k hk s0 sf1 target_pc out
        table_bs digits proj_bs ext_bs comp_mid tmp_d4 (edDouble4 (edAsExtended C)) F post
        hsp0_align hregs1 htab_b htab_v hdigits_len hext_len htd4_b htd4_v
        (fun sf2 ext' sel_bs hregs2 hext'_b hext'_v hsel_b hsel_v =>
          mul_iter_add_branch b hb hbase hAdd T k hk s0 sf2 target_pc out
            table_bs digits proj_bs ext' comp_mid sel_bs C (edDouble4 (edAsExtended C))
            (edSelectProjNielsPoints T (digits.getD k 0#8)) F post
            hsp0_align hregs2 hc_mid hext'_b hext'_v hsel_b hsel_v rfl hnext))

private theorem mul_loop_iter [DalekCliPlacement]
    (b : BitVec 64) (hb : DalekBase dalekCliPl33 b) (hbase : dalekCliPl33.base = b)
    (hDouble : ProjectivePointDoubleOk) (hSelect : LookupTableProjNielsSelectOk)
    (hAdd : EdwardsPointAddProjNielsOk) (hMul : Fe51MulOk) (T : Nat → EdExtPoint) (k : Nat) (hk : k < 63)
    (s0 s : State) (target_pc out : BitVec 64) (table_bs digits proj_bs ext_bs comp_bs tmp_bs : List (BitVec 8))
    (C : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulLoopRegs s0 s out (b + 172#64) (BitVec.ofNat 64 k))
    (htab_b : fe51ProjNielsTable8Bounded table_bs (2 ^ 54))
    (htab_v : ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice table_bs (160 * i) 160) = T i)
    (hdigits_len : digits.length = 64) (hproj_len : proj_bs.length = 120) (hext_len : ext_bs.length = 160)
    (hcomp_b : fe51Point4Bounded comp_bs (2 ^ 54)) (hcomp_v : edExtOfBytes comp_bs = C) (htmp_len : tmp_bs.length = 160)
    (hnext : ∀ (sf' : State) (proj' ext' comp' tmp' : List (BitVec 8)),
      MulLoopRegs s0 sf' out (if k == 0 then b + 788#64 else b + 172#64)
        (if k == 0 then -1#64 else BitVec.ofNat 64 (k - 1)) →
      proj'.length = 120 → ext'.length = 160 → fe51Point4Bounded comp' (2 ^ 54) →
      edExtOfBytes comp' = edVarBaseStep T (digits.getD k 0#8) C → tmp'.length = 160 →
      SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc sf'
        (mulLoopPre s0.sp table_bs digits proj' ext' comp' tmp' F) post oom) :
    SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc s
      (mulLoopPre s0.sp table_bs digits proj_bs ext_bs comp_bs tmp_bs F) post oom := by
  apply mul_double_1 b hb hbase hDouble hMul s0 s target_pc out (BitVec.ofNat 64 k)
    table_bs digits proj_bs ext_bs comp_bs tmp_bs C F post oom hsp0_align hregs hproj_len hcomp_b hcomp_v htmp_len
  intro s1 p1 c1 t1 hr1 hp1 hc1_b hc1_v ht1
  apply mul_double_2 b hb hbase hDouble hMul s0 s1 target_pc out (BitVec.ofNat 64 k)
    table_bs digits p1 ext_bs c1 t1 (edCompDoubleStep C) F post oom hsp0_align hr1 hp1 hc1_b hc1_v ht1
  intro s2 p2 c2 t2 hr2 hp2 hc2_b hc2_v ht2
  apply mul_double_3 b hb hbase hDouble hMul s0 s2 target_pc out (BitVec.ofNat 64 k)
    table_bs digits p2 ext_bs c2 t2 (edCompDoubleStep (edCompDoubleStep C)) F post oom hsp0_align hr2 hp2 hc2_b hc2_v ht2
  intro s3 p3 c3 t3 hr3 hp3 hc3_b hc3_v ht3
  apply mul_double_4 b hb hbase hDouble hMul s0 s3 target_pc out (BitVec.ofNat 64 k) table_bs digits p3 ext_bs c3 t3
    (edCompDoubleStep (edCompDoubleStep (edCompDoubleStep C))) F post oom hsp0_align hr3 hp3 hc3_b hc3_v ht3
  intro s4 p4 c4 t4 hr4 hp4 hc4_b hc4_v ht4
  apply mul_iter_tail b hb hbase hSelect hAdd hMul T k hk s0 s4 target_pc out table_bs digits p4 ext_bs c4 t4 C
    (edCompDoubleStep (edCompDoubleStep (edCompDoubleStep (edCompDoubleStep C)))) F post
    hsp0_align hr4 htab_b htab_v hdigits_len hext_len hc4_b hc4_v (edCompDoubleStep_4_eq C) ht4
  intro s5 ext' comp' tmp' hr5 hext' hcomp'_b hcomp'_v htmp'
  exact hnext s5 p4 ext' comp' tmp' hr5 hp4 hext' hcomp'_b hcomp'_v htmp'

private theorem edVarBaseLoopWith_succ {α : Type} (step : Nat → α → α) (k : Nat) (acc : α) :
    edVarBaseLoopWith step (k + 1) acc = edVarBaseLoopWith step k (step k acc) := rfl

private theorem edVarBaseLoop_succ (T : Nat → EdExtPoint) (digits : List (BitVec 8)) (k : Nat) (C : EdExtPoint) :
    edVarBaseLoop T digits (k + 1) C = edVarBaseLoop T digits k (edVarBaseStep T (digits.getD k 0#8) C) :=
  edVarBaseLoopWith_succ (fun i acc => edVarBaseStep T (digits.getD i 0#8) acc) k C

private theorem mul_loop [DalekCliPlacement]
    (b : BitVec 64) (hb : DalekBase dalekCliPl33 b) (hbase : dalekCliPl33.base = b)
    (hDouble : ProjectivePointDoubleOk) (hSelect : LookupTableProjNielsSelectOk)
    (hAdd : EdwardsPointAddProjNielsOk) (hMul : Fe51MulOk) (T : Nat → EdExtPoint) (m : Nat) (hm : m ≤ 63)
    (s0 s : State) (target_pc out : BitVec 64) (table_bs digits proj_bs ext_bs comp_bs tmp_bs : List (BitVec 8))
    (C : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulLoopRegs s0 s out (if m == 0 then b + 788#64 else b + 172#64)
      (if m == 0 then -1#64 else BitVec.ofNat 64 (m - 1)))
    (htab_b : fe51ProjNielsTable8Bounded table_bs (2 ^ 54))
    (htab_v : ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice table_bs (160 * i) 160) = T i)
    (hdigits_len : digits.length = 64) (hproj_len : proj_bs.length = 120) (hext_len : ext_bs.length = 160)
    (hcomp_b : fe51Point4Bounded comp_bs (2 ^ 54)) (hcomp_v : edExtOfBytes comp_bs = C) (htmp_len : tmp_bs.length = 160)
    (hnext : ∀ (sf' : State) (proj' ext' comp' tmp' : List (BitVec 8)),
      MulLoopRegs s0 sf' out (b + 788#64) (-1#64) →
      proj'.length = 120 → ext'.length = 160 → fe51Point4Bounded comp' (2 ^ 54) →
      edExtOfBytes comp' = edVarBaseLoop T digits m C → tmp'.length = 160 →
      SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc sf'
        (mulLoopPre s0.sp table_bs digits proj' ext' comp' tmp' F) post oom) :
    SepWP (dalekCliPC33.rebase b (fun _ => none)) target_pc s
      (mulLoopPre s0.sp table_bs digits proj_bs ext_bs comp_bs tmp_bs F) post oom := by
  induction m generalizing s proj_bs ext_bs comp_bs tmp_bs C with
  | zero => exact hnext s proj_bs ext_bs comp_bs tmp_bs hregs hproj_len hext_len hcomp_b hcomp_v htmp_len
  | succ k ih =>
    have hk : k < 63 := Nat.lt_of_succ_le hm
    have hregs' : MulLoopRegs s0 s out (b + 172#64) (BitVec.ofNat 64 k) := by
      rw [Nat.add_sub_cancel] at hregs; exact hregs
    apply mul_loop_iter b hb hbase hDouble hSelect hAdd hMul T k hk s0 s target_pc out
      table_bs digits proj_bs ext_bs comp_bs tmp_bs C F post
      hsp0_align hregs' htab_b htab_v hdigits_len hproj_len hext_len hcomp_b hcomp_v htmp_len
    intro s1 proj1 ext1 comp1 tmp1 hr1 hp1 he1 hc1_b hc1_v ht1
    refine ih (Nat.le_of_succ_le hm) s1 proj1 ext1 comp1 tmp1
      (edVarBaseStep T (digits.getD k 0#8) C) hr1 hp1 he1 hc1_b hc1_v ht1 ?_
    intro sf' proj' ext' comp' tmp' hr' hp' he' hcb' hcv' ht'
    rw [← edVarBaseLoop_succ] at hcv'
    exact hnext sf' proj' ext' comp' tmp' hr' hp' he' hcb' hcv' ht'

private theorem sepWP_eq_pre {prog : Program} {target_pc : BitVec 64} {s : State} {P Q : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hnext : SepWP prog target_pc s Q post oom) (h : P = Q) : SepWP prog target_pc s P post oom :=
  h ▸ hnext

private abbrev MulDoneCont [DalekCliPlacement] (b : BitVec 64) (s0 : State) (out point : BitVec 64)
    (scalar_frame : SepProp) (point_bs s_bs : List (BitVec 8))
    (post : State → SepProp → Prop) (oom : State → SepProp) : Prop :=
  ∀ (sf_ret : State) (res_bs : List (BitVec 8)),
    sf_ret.pc = s0.readReg64 Reg.lr → sf_ret.status = .Running → sf_ret.sp = s0.sp →
    sf_ret.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) →
    sf_ret.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) →
    sf_ret.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) →
    sf_ret.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) →
    sf_ret.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) →
    sf_ret.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) →
    sf_ret.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) →
    sf_ret.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) →
    sf_ret.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) →
    sf_ret.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) →
    sf_ret.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5) →
    calleeSavedVRegs sf_ret = calleeSavedVRegs s0 →
    fe51Point4Bounded res_bs (2 ^ 52) → edExtOfBytes res_bs = edVarBaseMul point_bs s_bs →
    (EdExtValid (edExtOfBytes point_bs) → EdExtValid (edExtOfBytes res_bs) ∧
      edOnCurve (edExtToAffine (edExtOfBytes res_bs)) = true ∧
      edExtToAffine (edExtOfBytes res_bs) =
        edSmul (leBytesToNat s_bs) (edExtToAffine (edExtOfBytes point_bs))) →
    SepWP (dalekCliPC33.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) sf_ret
      ((out ↦ₛ res_bs) ∗ (point ↦ₛ point_bs) ∗ scalar_frame ∗
       (fe51_one dalekCliMpl ↦ᵣ fe51OneBytes) ∗
       (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗ stackFrame s0 4496) post oom

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_epilogue [DalekCliPlacement]
    (b : BitVec 64) (_hb : DalekBase dalekCliPl33 b) (hbase : dalekCliPl33.base = b)
    (hMul : Fe51MulOk) (s0 s : State) (out point : BitVec 64) (scalar_frame : SepProp)
    (out_bs point_bs s_bs table_bs proj_bs pad8 ext_bs comp_bs tmp_bs : List (BitVec 8))
    (C_fin : EdExtPoint) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulLoopRegs s0 s out (b + 788#64) (-1#64))
    (hout_len : out_bs.length = 160) (hs_len : s_bs.length = 32) (hs_31 : (s_bs.getD 31 0#8).toNat ≤ 127)
    (htab_len : table_bs.length = 1280) (hproj_len : proj_bs.length = 120)
    (hpad8_len : pad8.length = 8) (hext_len : ext_bs.length = 160)
    (hcomp_b : fe51Point4Bounded comp_bs (2 ^ 54)) (hcomp_v : edExtOfBytes comp_bs = C_fin)
    (hC_fin : edAsExtended C_fin = edVarBaseMul point_bs s_bs) (htmp_len : tmp_bs.length = 160)
    (hdone : MulDoneCont b s0 out point scalar_frame point_bs s_bs post oom) :
    SepWP (dalekCliPC33.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) s
      (mulLoopPre s0.sp table_bs (scalarRadix16Digits s_bs) proj_bs ext_bs comp_bs tmp_bs
        (((s0.sp - 552#64) ↦ₛ pad8) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
         (out ↦ₛ out_bs) ∗ (point ↦ₛ point_bs) ∗ scalar_frame ∗
         (fe51_one dalekCliMpl ↦ᵣ fe51OneBytes) ∗
         (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes))) post oom := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx29, hvregs, hcl⟩
  unfold mulLoopPre
  have hdigits_len : (scalarRadix16Digits s_bs).length = 64 := scalarRadix16Digits_length s_bs
  obtain ⟨hcomp_l, hc_0, hc_40, hc_80, hc_120⟩ := hcomp_b
  apply sepWP_split4_completed_384 s0.sp C_fin
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_160 out; intro o0 o1 o2 o3 ho0_l ho1_l ho2_l ho3_l
  apply sepWP_resize_callee_2480 s0.sp 2256 224 2240
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [s]; try clear s
  obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w (fpMul C_fin.X C_fin.T)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [sf]; try clear sf
  obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_1 (fpMul C_fin.Y C_fin.Z)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [sf_1]; try clear sf_1
  obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_2 (fpMul C_fin.Z C_fin.T)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; clear_dead_vars [sf]; try clear sf
  obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_3 (fpMul C_fin.X C_fin.Y)
  norm_sf 224; apply sepWP_unresize_callee_2480 s0.sp 2256 224 2240
  apply sepWP_merge4_stack_384 s0.sp; intro comp_done hcomp_done_l
  apply sepWP_merge4_160 out
    (fun res => fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = edVarBaseMul point_bs s_bs)
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ :=
      edAsExtended_of_append4 w w_1 w_2 w_3 C_fin hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    exact ⟨⟨hl, hb0, hb1, hb2, hb3⟩, hv.trans hC_fin⟩
  intro res_bs ⟨hres_b, hres_v⟩; wp_sym_steps 6; close_cells (s0.sp - 64#64) 64 8
  apply sepWP_unpeel_stack_bytes s0.sp 224 160 64; apply sepWP_unpeel_stack_bytes s0.sp 384 160 224
  apply sepWP_unpeel_stack_bytes s0.sp 544 160 384; apply sepWP_unpeel_stack_bytes s0.sp 552 8 544
  apply sepWP_unpeel_stack_bytes s0.sp 672 120 552; apply sepWP_unpeel_stack_bytes s0.sp 736 64 672
  apply sepWP_unpeel_stack_bytes s0.sp 2016 1280 736; apply sepWP_merge_stack_callee 2480 2016
  have hres_spec : EdExtValid (edExtOfBytes point_bs) → EdExtValid (edExtOfBytes res_bs) ∧
      edOnCurve (edExtToAffine (edExtOfBytes res_bs)) = true ∧
      edExtToAffine (edExtOfBytes res_bs) =
        edSmul (leBytesToNat s_bs) (edExtToAffine (edExtOfBytes point_bs)) := by
    intro hP; obtain ⟨hV, hAff⟩ := edVarBaseMul_spec_aux hP hs_len hs_31
    rw [hres_v]; exact ⟨hV, hV.on_curve, hAff⟩
  refine sepWP_eq_pre (hdone _ res_bs (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hres_b hres_v hres_spec) (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_post_radix16 [DalekCliPlacement]
    (b : BitVec 64) (hb : DalekBase dalekCliPl33 b) (hbase : dalekCliPl33.base = b)
    (hDouble : ProjectivePointDoubleOk) (hSelect : LookupTableProjNielsSelectOk)
    (hAdd : EdwardsPointAddProjNielsOk) (hMul : Fe51MulOk)
    (s0 s : State) (out point : BitVec 64) (scalar_frame : SepProp) {Full : SepProp}
    (out_bs point_bs s_bs table_bs proj_bs pad8 ext_bs comp_bs tmp_bs : List (BitVec 8))
    (post : State → SepProp → Prop) {oom : State → SepProp}
    (hf : Full = (memRegion (s0.sp - 4496#64) 2480 ∗ ((s0.sp - 2016#64) ↦ₛ table_bs) ∗
       ((s0.sp - 736#64) ↦ₛ scalarRadix16Digits s_bs) ∗ ((s0.sp - 672#64) ↦ₛ proj_bs) ∗
       ((s0.sp - 552#64) ↦ₛ pad8) ∗ ((s0.sp - 544#64) ↦ₛ ext_bs) ∗
       ((s0.sp - 384#64) ↦ₛ comp_bs) ∗ ((s0.sp - 224#64) ↦ₛ tmp_bs) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
       (out ↦ₛ out_bs) ∗ (point ↦ₛ point_bs) ∗ (fe51_one dalekCliMpl ↦ᵣ fe51OneBytes) ∗
       (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ scalar_frame := by sep_frame)
    (hsp0_align : s0.spAligned = true) (hpc : s.pc = b + 64#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2016#64) (hx19 : s.readReg64 (Reg.gpr 19#5) = out)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = s0.sp - 736#64) (hx21 : s.readReg64 (Reg.gpr 21#5) = s0.sp - 544#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 64#64) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (hout_len : out_bs.length = 160) (hs_len : s_bs.length = 32) (hs_31 : (s_bs.getD 31 0#8).toNat ≤ 127)
    (htab_b : fe51ProjNielsTable8Bounded table_bs (2 ^ 54))
    (htab_v : ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice table_bs (160 * i) 160) =
      projNielsTablePoints (edExtOfBytes point_bs) i)
    (hproj_len : proj_bs.length = 120) (hpad8_len : pad8.length = 8) (hext_len : ext_bs.length = 160)
    (hcomp_len : comp_bs.length = 160) (htmp_len : tmp_bs.length = 160)
    (hdone : MulDoneCont b s0 out point scalar_frame point_bs s_bs post oom) :
    SepWP (dalekCliPC33.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) s Full post oom := by
  rw [hf]
  have h1_len : fe51OneBytes.length = 40 := fe51OneBytes_length
  have hdigits_len : (scalarRadix16Digits s_bs).length = 64 := scalarRadix16Digits_length s_bs
  haveI : HasLenGe fe51OneBytes 40 := ⟨by omega⟩
  haveI : HasLenGe (scalarRadix16Digits s_bs) 64 := ⟨by omega⟩; haveI : HasLenGe ext_bs 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 20
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro _hcl_copy; simp only [arm64_norm] at _hcl_copy
  apply sepWP_abstract_bytes (s0.sp - 544#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edExtZero)
    (hQ := mul_init_ext_zero_post ext_bs hext_len)
  intro ext0 ⟨hext0_b, hext0_v⟩; obtain ⟨htab_l, htab_b8⟩ := htab_b
  apply sepWP_resize_callee_2480 s0.sp 2240 240 2256
  wp_steps; wp_dalek_call hSelect; clean_prev_sf; clear_dead_vars [s]; try clear s; norm_sf 240
  apply sepWP_unresize_callee_2480 s0.sp 2240 240 2256
  obtain ⟨hext0_l, he0, he40, he80, he120⟩ := hext0_b
  replace he0 := fe51LimbsBoundedAt_mono he0 (b2 := 2 ^ 53); unpack_fe51_at he0
  replace he40 := fe51LimbsBoundedAt_mono he40 (b2 := 2 ^ 53); unpack_fe51_at he40
  replace he80 := fe51LimbsBoundedAt_mono he80 (b2 := 2 ^ 54); unpack_fe51_at he80
  replace he120 := fe51LimbsBoundedAt_mono he120 (b2 := 2 ^ 54); unpack_fe51_at he120
  obtain ⟨hsel_l, hs0, hs40, hs80, hs120⟩ : fe51Point4Bounded w (2 ^ 54) := by assumption
  unpack_fe51_at hs0; unpack_fe51_at hs40; unpack_fe51_at hs80; unpack_fe51_at hs120
  wp_sym_steps 4; apply sepWP_resize_callee_2480 s0.sp 1904 576 2592
  wp_steps; wp_dalek_call hAdd; clean_prev_sf; clear_dead_vars [sf]; try clear sf; norm_sf 576
  apply sepWP_unresize_callee_2480 s0.sp 1904 576 2592
  have hw1_b : fe51Point4Bounded w_1 (2 ^ 54) :=
    ⟨by assumption, fe51LimbsBoundedAt_mono (by assumption), fe51LimbsBoundedAt_mono (by assumption),
     by assumption, fe51LimbsBoundedAt_mono (by assumption)⟩
  have hw1_v : edExtOfBytes w_1 = edAddProjNiels edExtZero
      (edSelectProjNielsPoints (projNielsTablePoints (edExtOfBytes point_bs))
        ((scalarRadix16Digits s_bs).getD 63 0#8)) := by
    rw [show edExtOfBytes w_1 = edAddProjNiels (edExtOfBytes ext0) (edExtOfBytes w) by assumption,
        hext0_v, show edExtOfBytes w = edSelectProjNiels table_bs
          ((scalarRadix16Digits s_bs).getD 63 0#8) by assumption, edSelectProjNiels_eq_points _ htab_v]
  wp_sym_steps 1; apply sepWP_fold_mulLoopPre s0.sp
  apply mul_loop b hb hbase hDouble hSelect hAdd hMul (projNielsTablePoints (edExtOfBytes point_bs)) 63 (by decide)
    s0 _ _ out table_bs (scalarRadix16Digits s_bs) proj_bs ext0 w_1 w _ _ _ hsp0_align
    ⟨by simp only [State.pc_setPC]; rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by assumption⟩
    ⟨htab_l, htab_b8⟩ htab_v hdigits_len hproj_len hext0_l hw1_b hw1_v hsel_l
  intro sf_end proj_end ext_end comp_end tmp_end hregs_end hproj_end hext_end hcomp_end_b hcomp_end_v htmp_end
  refine sepWP_eq_pre (mul_epilogue b hb hbase hMul s0 sf_end out point scalar_frame
    out_bs point_bs s_bs table_bs proj_end pad8 ext_end comp_end tmp_end _ post
    hsp0_align hregs_end hout_len hs_len hs_31 htab_l hproj_end hpad8_len hext_end
    hcomp_end_b hcomp_end_v rfl htmp_end hdone) (by unfold mulLoopPre; sep_ac_rfl)

/-! ## 3. Public Bridge & Machine-Code Theorems -/

public section

/-- For any valid extended Edwards point `edExtOfBytes point_bs` and 32-byte scalar `s_bs` with
    `s_bs[31] ≤ 127`, `edVarBaseMul point_bs s_bs` is a valid extended Edwards point whose affine
    projection equals `edSmul (leBytesToNat s_bs) (edExtToAffine (edExtOfBytes point_bs))`. -/
theorem edVarBaseMul_spec {point_bs s_bs : List (BitVec 8)}
    (hA : EdExtValid (edExtOfBytes point_bs))
    (hs_len : s_bs.length = 32)
    (hs_31 : (s_bs.getD 31 0#8).toNat ≤ 127) :
    EdExtValid (edVarBaseMul point_bs s_bs) ∧
    edExtToAffine (edVarBaseMul point_bs s_bs) =
      edSmul (leBytesToNat s_bs) (edExtToAffine (edExtOfBytes point_bs)) :=
  edVarBaseMul_spec_aux hA hs_len hs_31

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
theorem edwards_point_mul_scalar_ok_of
    (hMul : Fe51MulOk) (hMulRo : Fe51MulRoRightOk)
    (hDbl : ProjectivePointDoubleOk) (hAddPN : EdwardsPointAddProjNielsOk)
    (hRadix16 : ScalarAsRadix16Ok) :
    EdwardsPointMulScalarOk := by
  have hFrom : LookupTableProjNielsFromOk := lookup_table_proj_niels_from_ok_of hMul hMulRo hAddPN
  have hSelect : LookupTableProjNielsSelectOk := lookup_table_proj_niels_select_ok
  intro _
  apply dalekCaller_ok dalekCliPC33 dalekCliPl33
  intro b hb hbase
  wp_init
  obtain ⟨hp_l, hp0, hp40, hp80, hp120⟩ : fe51Point4Bounded a_4 (2 ^ 53) := by assumption
  unpack_fe51_at hp0; unpack_fe51_at hp40; unpack_fe51_at hp80; unpack_fe51_at hp120
  apply sepWP_split_stack_callee 2480 2016; apply sepWP_peel_stack_bytes s0.sp 2016 1280 736
  intro sp_2016 h_2016; apply sepWP_peel_stack_bytes s0.sp 736 64 672; intro sp_736 h_736
  apply sepWP_peel_stack_bytes s0.sp 672 120 552; intro sp_672 h_672
  apply sepWP_peel_stack_bytes s0.sp 552 8 544; intro sp_552 h_552
  apply sepWP_peel_stack_bytes s0.sp 544 160 384; intro sp_544 h_544
  apply sepWP_peel_stack_bytes s0.sp 384 160 224; intro sp_384 h_384
  apply sepWP_peel_stack_bytes s0.sp 224 160 64; intro sp_224 h_224
  open_cells (s0.sp - 64#64) 64 8; haveI : HasLenGe sp_2016 1280 := ⟨by omega⟩
  have h2016_w : (ByteSlice.write64 sp_2016 0 0#64).length = 1280 := by rw [write64_length_eq]; omega
  wp_cut_codeLoaded; wp_steps; wp_dalek_call hFrom; clean_prev_sf; norm_sf 2480
  wp_steps; wp_dalek_call hRadix16; clean_prev_sf
  apply mul_post_radix16 b hb hbase hDbl hSelect hAddPN hMul s0 _ a_1 a (a_2 ↦ₛ a_rest)
    a_3 a_4 a_rest w sp_672 sp_552 sp_544 sp_384 sp_224 _ (by sep_frame) hsp_align (by assumption)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by assumption)
    (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) h_672 h_552 h_544 h_384 h_224
  intro sf_ret res_bs hpc_r hrun_r hsp_r hx19_r hx20_r hx21_r hx22_r hx23_r hx24_r hx25_r hx26_r hx27_r hx28_r
    hx29_r hvregs_r ⟨hres_l, hres0, hres40, hres80, hres120⟩ hres_v hres_spec
  unpack_fe51_at hres0; unpack_fe51_at hres40; unpack_fe51_at hres80; unpack_fe51_at hres120; wp_done

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
theorem edwards_point_mul_scalar_ro_ok_of
    (hMul : Fe51MulOk) (hMulRo : Fe51MulRoRightOk)
    (hDbl : ProjectivePointDoubleOk) (hAddPN : EdwardsPointAddProjNielsOk)
    (hRadix16Ro : ScalarAsRadix16RoOk) :
    EdwardsPointMulScalarRoOk := by
  have hFrom : LookupTableProjNielsFromOk := lookup_table_proj_niels_from_ok_of hMul hMulRo hAddPN
  have hSelect : LookupTableProjNielsSelectOk := lookup_table_proj_niels_select_ok
  intro _
  apply dalekCaller_ok dalekCliPC33 dalekCliPl33
  intro b hb hbase
  wp_init
  obtain ⟨hp_l, hp0, hp40, hp80, hp120⟩ : fe51Point4Bounded a_4 (2 ^ 53) := by assumption
  unpack_fe51_at hp0; unpack_fe51_at hp40; unpack_fe51_at hp80; unpack_fe51_at hp120
  apply sepWP_split_stack_callee 2480 2016; apply sepWP_peel_stack_bytes s0.sp 2016 1280 736
  intro sp_2016 h_2016; apply sepWP_peel_stack_bytes s0.sp 736 64 672; intro sp_736 h_736
  apply sepWP_peel_stack_bytes s0.sp 672 120 552; intro sp_672 h_672
  apply sepWP_peel_stack_bytes s0.sp 552 8 544; intro sp_552 h_552
  apply sepWP_peel_stack_bytes s0.sp 544 160 384; intro sp_544 h_544
  apply sepWP_peel_stack_bytes s0.sp 384 160 224; intro sp_384 h_384
  apply sepWP_peel_stack_bytes s0.sp 224 160 64; intro sp_224 h_224
  open_cells (s0.sp - 64#64) 64 8; haveI : HasLenGe sp_2016 1280 := ⟨by omega⟩
  have h2016_w : (ByteSlice.write64 sp_2016 0 0#64).length = 1280 := by rw [write64_length_eq]; omega
  wp_cut_codeLoaded; wp_steps; wp_dalek_call hFrom; clean_prev_sf; norm_sf 2480
  wp_steps; wp_dalek_call hRadix16Ro; clean_prev_sf
  apply mul_post_radix16 b hb hbase hDbl hSelect hAddPN hMul s0 _ a_1 a (a_2 ↦ᵣ a_rest)
    a_3 a_4 a_rest w sp_672 sp_552 sp_544 sp_384 sp_224 _ (by sep_frame) hsp_align (by assumption)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by assumption)
    (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) h_672 h_552 h_544 h_384 h_224
  intro sf_ret res_bs hpc_r hrun_r hsp_r hx19_r hx20_r hx21_r hx22_r hx23_r hx24_r hx25_r hx26_r hx27_r hx28_r
    hx29_r hvregs_r ⟨hres_l, hres0, hres40, hres80, hres120⟩ hres_v hres_spec
  unpack_fe51_at hres0; unpack_fe51_at hres40; unpack_fe51_at hres80; unpack_fe51_at hres120; wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.VariableBaseMul

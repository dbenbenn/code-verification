/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Pow
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveModels2
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveModels3
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Scalar52
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Scalar
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.LookupTableProj
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.VariableBaseMul
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.BasepointTable
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.IsTorsionFree -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PointCompress2
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PointCompress3
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MontToEdwards
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.NafLookupTable2
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DoubleScalarMul

/-!
# Unconditional `dalekCliMultiLib` Machine-Code Contracts

Instantiates the conditional `*_ok_of` proofs across `dalekCliMultiLib` (`B00..B36`,
37 `.text.*` blocks / 10,836 bytes) into unconditional `DalekBlockOk` / `DalekBlockConstOk`
contracts and `dalekCliMultiLib.subroutineOk` exports for the 11 `dalekCliExports` entry points.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.AllBlocksOk

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open CryptoVerification.SignalSession.CliExt (pureByteFunctionSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  BlackBoxU8Ok blackBoxU8Spec
  MemcpyOk memcpySpec MemcpyRoOk memcpyRoSpec
  Slice32CtEqOk
  Fe51MulOk Fe51MulRoRightOk Fe51Pow2kOk Fe51ToBytesOk Fe51ToBytesRoOk
  Fe51Pow22501Ok Fe51SqrtRatioIOk
  Sc52MontgomeryMulCoreOk Sc52MontgomeryMulRoRightOk Sc52MulCoreOk Sc52MulOk ScalarReduceOk
  ScalarFromBytesModOrderOk ScalarFromBytesModOrderWideOk
  ScalarMulRefOk ScalarMulValOk scalarMulSpec
  ScalarAddRefOk ScalarAddValOk scalarAddSpec
  ScalarAsRadix16Ok ScalarAsRadix16RoOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  ProjectivePointDoubleOk
  EdwardsPointAddProjNielsOk EdwardsPointSubProjNielsOk
  EdwardsPointAddAffineNielsOk EdwardsPointAddAffineNielsRoOk
  EdwardsPointSubAffineNielsOk EdwardsPointSubAffineNielsRoOk
  EdwardsPointMulByPow2Ok EdwardsPointMulByPow2_4Ok
  LookupTableAffineNielsSelectOk
  EdwardsBasepointTableMulBaseOk ScalarMulBasepointTableOk scalarMulBasepointTableSpec
  LookupTableProjNielsFromOk LookupTableProjNielsSelectOk
  NafLookupTable5FromOk
  VartimeDoubleScalarMulBasepointOk vartimeDoubleScalarMulBasepointSpec
  EdwardsPointCtEqOk
  EdwardsPointCompressOk edwardsPointCompressSpec
  CompressedEdwardsYDecompressOk
  MontgomeryPointToEdwardsOk montgomeryPointToEdwardsSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs (
  EdwardsPointMulScalarOk EdwardsPointMulScalarRoOk
  EdwardsPointIsTorsionFreeOk edwardsPointIsTorsionFreeSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.IsTorsionFree (
  EdwardsPointIsTorsionFreeU32Ok edwardsPointIsTorsionFreeU32Spec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges (
  DalekCliRoOk withRoOk dalekScalarModVec dalekScalarWideVec
  dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved
  scalarFromBytesModOrder_cliExt_subroutineOk_of
  scalarFromBytesModOrderWide_cliExt_subroutineOk_of
  blackBoxU8_subroutineOk_of
  memcpy_subroutineOk_of memcpyRo_subroutineOk_of
  montgomeryPointToEdwards_subroutineOk_of
  edwardsPointCompress_subroutineOk_of
  vartimeDoubleScalarMulBasepoint_subroutineOk_of
  edwardsPointIsTorsionFree_subroutineOk_of
  scalarMulBasepointTable_subroutineOk_of
  scalarMulVal_subroutineOk_of
  scalarAddVal_subroutineOk_of)

/-! ## 1. Unconditional Block-Level Contracts (`B00..B36`) -/

/-- `B00`: `subtle::black_box::<u8>` -/
theorem black_box_u8_ok : BlackBoxU8Ok := Layer0.black_box_u8_ok

/-- `B01`: `<Scalar>::from_bytes_mod_order` -/
theorem scalar_from_bytes_mod_order_ok : ScalarFromBytesModOrderOk :=
  Scalar.scalar_from_bytes_mod_order_ok

/-- `B02`: `<Scalar>::from_bytes_mod_order_wide` -/
theorem scalar_from_bytes_mod_order_wide_ok : ScalarFromBytesModOrderWideOk :=
  Scalar.scalar_from_bytes_mod_order_wide_ok

/-- `B03`: `<FieldElement51>::sqrt_ratio_i` -/
theorem fe51_sqrt_ratio_i_ok : Fe51SqrtRatioIOk := Field51Pow.fe51_sqrt_ratio_i_ok

/-- `B04`: `<FieldElement51>::pow22501` -/
theorem fe51_pow22501_ok : Fe51Pow22501Ok := Field51Pow.fe51_pow22501_ok

/-- `B05`: `<CompressedEdwardsY>::decompress` -/
theorem compressed_edwards_y_decompress_ok : CompressedEdwardsYDecompressOk :=
  PointCompress3.compressed_edwards_y_decompress_ok_of
    Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok
    Field51.fe51_pow2k_ok Field51Pow.fe51_sqrt_ratio_i_ok

/-- `B06`: `<Scalar52>::montgomery_mul` (mutable right operand) -/
theorem sc52_montgomery_mul_core_ok : Sc52MontgomeryMulCoreOk :=
  Scalar52.sc52_montgomery_mul_core_ok

/-- `B06`: `<Scalar52>::montgomery_mul` (read-only right operand) -/
theorem sc52_montgomery_mul_ro_right_ok : Sc52MontgomeryMulRoRightOk :=
  Scalar52.sc52_montgomery_mul_ro_right_ok

/-- `B07`: `<Scalar52>::mul` (core limb contract) -/
theorem sc52_mul_core_ok : Sc52MulCoreOk := Scalar52.sc52_mul_core_ok

/-- `B07`: `<Scalar52>::mul` (modulo `ℓ` contract) -/
theorem sc52_mul_ok : Sc52MulOk := Scalar52.sc52_mul_ok

/-- `B08`: `<MontgomeryPoint>::to_edwards` -/
theorem montgomery_point_to_edwards_ok : MontgomeryPointToEdwardsOk :=
  MontToEdwards.montgomery_point_to_edwards_ok_of
    Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok
    Field51.fe51_pow2k_ok Field51.fe51_to_bytes_ok
    Field51Pow.fe51_pow22501_ok compressed_edwards_y_decompress_ok

/-- `B09`: `<LookupTable<AffineNielsPoint>>::select` -/
theorem lookup_table_affine_niels_select_ok : LookupTableAffineNielsSelectOk :=
  BasepointTable.lookup_table_affine_niels_select_ok

/-- `B10`: `<LookupTable<ProjectiveNielsPoint>>::select` -/
theorem lookup_table_proj_niels_select_ok : LookupTableProjNielsSelectOk :=
  LookupTableProj.lookup_table_proj_niels_select_ok

/-- `B11`: `<FieldElement51>::pow2k` -/
theorem fe51_pow2k_ok : Fe51Pow2kOk := Field51.fe51_pow2k_ok

/-- `B12`: `<FieldElement51>::to_bytes` (mutable input) -/
theorem fe51_to_bytes_ok : Fe51ToBytesOk := Field51.fe51_to_bytes_ok

/-- `B12`: `<FieldElement51>::to_bytes` (read-only input) -/
theorem fe51_to_bytes_ro_ok : Fe51ToBytesRoOk := Field51.fe51_to_bytes_ro_ok

/-- `B13`: `<ProjectivePoint>::double` -/
theorem projective_point_double_ok : ProjectivePointDoubleOk :=
  CurveModels2.projective_point_double_ok

/-- `B14`: `<EdwardsPoint>::compress` -/
theorem edwards_point_compress_ok : EdwardsPointCompressOk :=
  PointCompress2.edwards_point_compress_ok_of
    Field51.fe51_mul_ok Field51.fe51_pow2k_ok Field51Pow.fe51_pow22501_ok

/-- `B15`: `<Scalar>::as_radix_16` (mutable input) -/
theorem scalar_as_radix_16_ok : ScalarAsRadix16Ok := Scalar.scalar_as_radix_16_ok

/-- `B15`: `<Scalar>::as_radix_16` (read-only input) -/
theorem scalar_as_radix_16_ro_ok : ScalarAsRadix16RoOk := Scalar.scalar_as_radix_16_ro_ok

/-- `B16`: `<Scalar>::reduce` -/
theorem scalar_reduce_ok : ScalarReduceOk := Scalar52.scalar_reduce_ok

/-- `B17`: `<EdwardsPoint>::vartime_double_scalar_mul_basepoint` -/
theorem vartime_double_scalar_mul_basepoint_ok : VartimeDoubleScalarMulBasepointOk :=
  DoubleScalarMul.vartime_double_scalar_mul_basepoint_ok_of
    Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok Field51.fe51_pow2k_ok
    CurveModels2.projective_point_double_ok
    CurveModels2.edwards_point_add_proj_niels_ok CurveModels2.edwards_point_sub_proj_niels_ok
    CurveModels2.edwards_point_add_affine_niels_ro_ok
    CurveModels2.edwards_point_sub_affine_niels_ro_ok
    (NafLookupTable2.naf_lookup_table5_from_ok_of
      Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok
      CurveModels2.projective_point_double_ok CurveModels2.edwards_point_add_proj_niels_ok)

/-- `B18`: `<EdwardsPoint>::mul_by_pow_2` (general `k`) -/
theorem edwards_point_mul_by_pow_2_ok : EdwardsPointMulByPow2Ok :=
  CurveModels3.edwards_point_mul_by_pow_2_ok

/-- `B18`: `<EdwardsPoint>::mul_by_pow_2` (`k = 4` specialization) -/
theorem edwards_point_mul_by_pow_2_4_ok : EdwardsPointMulByPow2_4Ok :=
  CurveModels3.edwards_point_mul_by_pow_2_4_ok

/-- `B19`: `<EdwardsPoint>::is_torsion_free` -/
theorem edwards_point_is_torsion_free_ok : EdwardsPointIsTorsionFreeOk :=
  IsTorsionFree.edwards_point_is_torsion_free_ok_of
    (VariableBaseMul.edwards_point_mul_scalar_ro_ok_of
      Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok
      CurveModels2.projective_point_double_ok CurveModels2.edwards_point_add_proj_niels_ok
      Scalar.scalar_as_radix_16_ro_ok)
    (PointCompress2.edwards_point_ct_eq_ok_of Field51.fe51_mul_ok)

/-- `B19`: `<EdwardsPoint>::is_torsion_free` (32-bit `w0` `u32` contract matching
    `CliExternsFixed.torsionFreeSpec`) -/
theorem edwards_point_is_torsion_free_u32_ok : EdwardsPointIsTorsionFreeU32Ok :=
  IsTorsionFree.edwards_point_is_torsion_free_u32_ok_of
    (VariableBaseMul.edwards_point_mul_scalar_ro_ok_of
      Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok
      CurveModels2.projective_point_double_ok CurveModels2.edwards_point_add_proj_niels_ok
      Scalar.scalar_as_radix_16_ro_ok)
    (PointCompress2.edwards_point_ct_eq_ok_of Field51.fe51_mul_ok)

/-- `B20`: `<NafLookupTable5<ProjectiveNielsPoint>>::from::<&EdwardsPoint>` -/
theorem naf_lookup_table5_from_ok : NafLookupTable5FromOk :=
  NafLookupTable2.naf_lookup_table5_from_ok_of
    Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok
    CurveModels2.projective_point_double_ok CurveModels2.edwards_point_add_proj_niels_ok

/-- `B21`: `<&Scalar as Mul<&Scalar>>::mul` -/
theorem scalar_mul_ref_ok : ScalarMulRefOk := Scalar.scalar_mul_ref_ok

/-- `B22`: `<&FieldElement51 as Mul<&FieldElement51>>::mul` (mutable operands) -/
theorem fe51_mul_ok : Fe51MulOk := Field51.fe51_mul_ok

/-- `B22`: `<&FieldElement51 as Mul<&FieldElement51>>::mul` (read-only right operand) -/
theorem fe51_mul_ro_right_ok : Fe51MulRoRightOk := Field51.fe51_mul_ro_right_ok

/-- `B23`: `<&Scalar as Add<&Scalar>>::add` -/
theorem scalar_add_ref_ok : ScalarAddRefOk := Scalar.scalar_add_ref_ok

/-- `B24`: `<[u8] as ConstantTimeEq>::ct_eq` (32-byte slice equality) -/
theorem slice32_ct_eq_ok : Slice32CtEqOk := Layer0.slice32_ct_eq_ok

/-- `B25`: `<LookupTable<ProjectiveNielsPoint>>::from::<&EdwardsPoint>` -/
theorem lookup_table_proj_niels_from_ok : LookupTableProjNielsFromOk :=
  LookupTableProj.lookup_table_proj_niels_from_ok_of
    Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok CurveModels2.edwards_point_add_proj_niels_ok

/-- `B26`: `<EdwardsBasepointTable>::mul_base` -/
theorem edwards_basepoint_table_mul_base_ok : EdwardsBasepointTableMulBaseOk :=
  BasepointTable.edwards_basepoint_table_mul_base_ok_of
    Field51.fe51_mul_ok CurveModels3.edwards_point_mul_by_pow_2_4_ok
    CurveModels2.edwards_point_add_affine_niels_ok Scalar.scalar_as_radix_16_ok

/-- `B27`: `<&Scalar as Mul<&EdwardsBasepointTable>>::mul` -/
theorem scalar_mul_basepoint_table_ok : ScalarMulBasepointTableOk :=
  BasepointTable.scalar_mul_basepoint_table_ok_of edwards_basepoint_table_mul_base_ok

/-- `B28`: `<&EdwardsPoint as Add<&ProjectiveNielsPoint>>::add` -/
theorem edwards_point_add_proj_niels_ok : EdwardsPointAddProjNielsOk :=
  CurveModels2.edwards_point_add_proj_niels_ok

/-- `B29`: `<&EdwardsPoint as Sub<&ProjectiveNielsPoint>>::sub` -/
theorem edwards_point_sub_proj_niels_ok : EdwardsPointSubProjNielsOk :=
  CurveModels2.edwards_point_sub_proj_niels_ok

/-- `B30`: `<EdwardsPoint as ConstantTimeEq>::ct_eq` -/
theorem edwards_point_ct_eq_ok : EdwardsPointCtEqOk :=
  PointCompress2.edwards_point_ct_eq_ok_of Field51.fe51_mul_ok

/-- `B31`: `<&EdwardsPoint as Add<&AffineNielsPoint>>::add` (mutable right operand) -/
theorem edwards_point_add_affine_niels_ok : EdwardsPointAddAffineNielsOk :=
  CurveModels2.edwards_point_add_affine_niels_ok

/-- `B31`: `<&EdwardsPoint as Add<&AffineNielsPoint>>::add` (read-only right operand) -/
theorem edwards_point_add_affine_niels_ro_ok : EdwardsPointAddAffineNielsRoOk :=
  CurveModels2.edwards_point_add_affine_niels_ro_ok

/-- `B32`: `<&EdwardsPoint as Sub<&AffineNielsPoint>>::sub` (mutable right operand) -/
theorem edwards_point_sub_affine_niels_ok : EdwardsPointSubAffineNielsOk :=
  CurveModels2.edwards_point_sub_affine_niels_ok

/-- `B32`: `<&EdwardsPoint as Sub<&AffineNielsPoint>>::sub` (read-only right operand) -/
theorem edwards_point_sub_affine_niels_ro_ok : EdwardsPointSubAffineNielsRoOk :=
  CurveModels2.edwards_point_sub_affine_niels_ro_ok

/-- `B33`: `<&EdwardsPoint as Mul<&Scalar>>::mul` (mutable scalar) -/
theorem edwards_point_mul_scalar_ok : EdwardsPointMulScalarOk :=
  VariableBaseMul.edwards_point_mul_scalar_ok_of
    Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok
    CurveModels2.projective_point_double_ok CurveModels2.edwards_point_add_proj_niels_ok
    Scalar.scalar_as_radix_16_ok

/-- `B33`: `<&EdwardsPoint as Mul<&Scalar>>::mul` (read-only scalar) -/
theorem edwards_point_mul_scalar_ro_ok : EdwardsPointMulScalarRoOk :=
  VariableBaseMul.edwards_point_mul_scalar_ro_ok_of
    Field51.fe51_mul_ok Field51.fe51_mul_ro_right_ok
    CurveModels2.projective_point_double_ok CurveModels2.edwards_point_add_proj_niels_ok
    Scalar.scalar_as_radix_16_ro_ok

/-- `B34`: `<Scalar as Mul>::mul` -/
theorem scalar_mul_val_ok : ScalarMulValOk := Scalar.scalar_mul_val_ok

/-- `B35`: `<Scalar as Add>::add` -/
theorem scalar_add_val_ok : ScalarAddValOk := Scalar.scalar_add_val_ok

/-- `B36`: `memcpy` (mutable source) -/
theorem memcpy_ok : MemcpyOk := Layer0.memcpy_ok

/-- `B36`: `memcpy` (read-only source) -/
theorem memcpy_ro_ok : MemcpyRoOk := Layer0.memcpy_ro_ok

/-! ## 2. Unconditional `dalekCliMultiLib.subroutineOk` Contracts for All 11 `dalekCliExports` -/

theorem blackBoxU8_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "subtle::black_box::<u8>"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved blackBoxU8Spec))) externs :=
  blackBoxU8_subroutineOk_of black_box_u8_ok externs

theorem scalarFromBytesModOrder_cliExt_subroutineOk (byVal : Bool)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order"
      (fun _ => keepsFs (withVmPreserved (pureByteFunctionSpec dalekScalarModVec byVal)))
      externs :=
  scalarFromBytesModOrder_cliExt_subroutineOk_of scalar_from_bytes_mod_order_ok byVal externs

theorem scalarFromBytesModOrderWide_cliExt_subroutineOk (byVal : Bool)
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide"
      (fun mpl =>
        withRoOk (DalekCliRoOk mpl)
          (keepsFs (withVmPreserved (pureByteFunctionSpec dalekScalarWideVec byVal))))
      externs :=
  scalarFromBytesModOrderWide_cliExt_subroutineOk_of scalar_from_bytes_mod_order_wide_ok byVal externs

theorem montgomeryPointToEdwards_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards"
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (montgomeryPointToEdwardsSpec mpl))))
      externs :=
  montgomeryPointToEdwards_subroutineOk_of montgomery_point_to_edwards_ok externs

theorem edwardsPointCompress_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::edwards::EdwardsPoint>::compress"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved edwardsPointCompressSpec))) externs :=
  edwardsPointCompress_subroutineOk_of edwards_point_compress_ok externs

theorem vartimeDoubleScalarMulBasepoint_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk
      "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint"
      (fun mpl =>
        Spec.withTraceEq (keepsFs (withVmPreserved (vartimeDoubleScalarMulBasepointSpec mpl))))
      externs :=
  vartimeDoubleScalarMulBasepoint_subroutineOk_of vartime_double_scalar_mul_basepoint_ok externs

theorem edwardsPointIsTorsionFree_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (edwardsPointIsTorsionFreeSpec mpl))))
      externs :=
  edwardsPointIsTorsionFree_subroutineOk_of edwards_point_is_torsion_free_ok externs

theorem edwardsPointIsTorsionFreeU32_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"
      (fun mpl =>
        Spec.withTraceEq (keepsFs (withVmPreserved (edwardsPointIsTorsionFreeU32Spec mpl))))
      externs :=
  dalekSubroutineOk_withTraceEq_keepsFs_vmPreserved
    "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"
    edwards_point_is_torsion_free_u32_ok externs

theorem scalarMulBasepointTable_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk
      "<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul<&curve25519_dalek::edwards::EdwardsBasepointTable>>::mul"
      (fun mpl => Spec.withTraceEq (keepsFs (withVmPreserved (scalarMulBasepointTableSpec mpl))))
      externs :=
  scalarMulBasepointTable_subroutineOk_of scalar_mul_basepoint_table_ok externs

theorem scalarMulVal_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved scalarMulSpec))) externs :=
  scalarMulVal_subroutineOk_of scalar_mul_val_ok externs

theorem scalarAddVal_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "<curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved scalarAddSpec))) externs :=
  scalarAddVal_subroutineOk_of scalar_add_val_ok externs

theorem memcpy_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "memcpy"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved memcpySpec))) externs :=
  memcpy_subroutineOk_of memcpy_ok externs

theorem memcpyRo_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    dalekCliMultiLib.subroutineOk "memcpy"
      (fun _ => Spec.withTraceEq (keepsFs (withVmPreserved memcpyRoSpec))) externs :=
  memcpyRo_subroutineOk_of memcpy_ro_ok externs

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.AllBlocksOk

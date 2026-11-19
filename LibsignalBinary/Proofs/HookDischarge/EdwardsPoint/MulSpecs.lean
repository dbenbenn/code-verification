/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards -- proof-setup: allow-public-import

/-!
# Variable-Base Scalar Multiplication and Subgroup Check Specifications

Internal specifications for `B33` and `B19` (which depend on `Math.Edwards.EdExtValid`):
- `edwardsPointMulScalarSpec` / `edwardsPointMulScalarRoSpec` (`B33`, 219 insns, stack 4496)
- `edwardsPointIsTorsionFreeSpec` (`B19`, 32 insns, stack 4848)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib
open VerifiedLibraries.Common (
  EdExtPoint edExtZero edZero edOrderL edOnCurve edSmul edExtToAffine leBytesToNat)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (DalekBlockOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51_one fe51OneBytes fe51_edwards_d2 fe51EdwardsD2Bytes
  basepoint_order basepointOrderBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51Point4Bounded edExtOfBytes edVarBaseMul edPointEq)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (EdExtValid)

/-- `<&EdwardsPoint as Mul<&Scalar>>::mul` (`B33`, 219 insns, stack 4496):
    variable-base scalar multiplication with mutable/stack scalar (`scalar ↦ₛ s_bs`). -/
abbrev rust_spec edwardsPointMulScalarSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (point : ptr) (scalar : ptr)
    (ghost out_bs point_bs s_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧
                fe51Point4Bounded point_bs (2 ^ 53) ∧
                s_bs.length = 32 ∧
                (s_bs.getD 31 0#8).toNat ≤ 127
  preserves     (point ↦ₛ point_bs) ∗ (scalar ↦ₛ s_bs) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes)
  requires      out ↦ₛ out_bs
  stack         4496
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
                    edExtOfBytes res_bs = edVarBaseMul point_bs s_bs ∧
                    (EdExtValid (edExtOfBytes point_bs) →
                      EdExtValid (edExtOfBytes res_bs) ∧
                      edOnCurve (edExtToAffine (edExtOfBytes res_bs)) = true ∧
                      edExtToAffine (edExtOfBytes res_bs) =
                        edSmul (leBytesToNat s_bs) (edExtToAffine (edExtOfBytes point_bs)))⌝

abbrev EdwardsPointMulScalarOk : Prop :=
  DalekBlockOk 33 edwardsPointMulScalarSpec

/-- Read-only-scalar variant of `<&EdwardsPoint as Mul<&Scalar>>::mul` (`B33`, stack 4496),
    used when `EdwardsPoint::is_torsion_free` passes `.rodata` `constants::BASEPOINT_ORDER_PRIVATE`
    (`scalar ↦ᵣ s_bs`). -/
abbrev rust_spec edwardsPointMulScalarRoSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (point : ptr) (scalar : ptr)
    (ghost out_bs point_bs s_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧
                fe51Point4Bounded point_bs (2 ^ 53) ∧
                s_bs.length = 32 ∧
                (s_bs.getD 31 0#8).toNat ≤ 127
  preserves     (point ↦ₛ point_bs) ∗ (scalar ↦ᵣ s_bs) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes)
  requires      out ↦ₛ out_bs
  stack         4496
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
                    edExtOfBytes res_bs = edVarBaseMul point_bs s_bs ∧
                    (EdExtValid (edExtOfBytes point_bs) →
                      EdExtValid (edExtOfBytes res_bs) ∧
                      edOnCurve (edExtToAffine (edExtOfBytes res_bs)) = true ∧
                      edExtToAffine (edExtOfBytes res_bs) =
                        edSmul (leBytesToNat s_bs) (edExtToAffine (edExtOfBytes point_bs)))⌝

abbrev EdwardsPointMulScalarRoOk : Prop :=
  DalekBlockOk 33 edwardsPointMulScalarRoSpec

/-- `<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free` (`B19`, 32 insns, stack 4848):
    multiplies `self` (`x0`, 160-byte `EdwardsPoint`) by `BASEPOINT_ORDER` (`ℓ = edOrderL`)
    via `<&EdwardsPoint as Mul<&Scalar>>::mul` and compares the resulting extended point in
    constant time against `EdwardsPoint::IDENTITY` (`edExtZero`) via `EdwardsPoint::ct_eq`,
    returning `1#8` in `w0` iff `[ℓ]self == 𝒪` and `0#8` otherwise. -/
abbrev rust_spec edwardsPointIsTorsionFreeSpec
    (ctx mpl : Obj.MultiPlacement)
    (self : ptr)
    (ghost self_bs : List (BitVec 8)) : (ret : u8)
  requires_cond fe51Point4Bounded self_bs (2 ^ 53)
  preserves     (self ↦ₛ self_bs) ∗
                (basepoint_order mpl ↦ᵣ basepointOrderBytes) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
                (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes)
  stack         4848
  ensures       ⌜ret = (if edPointEq (edVarBaseMul self_bs basepointOrderBytes) edExtZero
                        then 1#8 else 0#8) ∧
                  (EdExtValid (edExtOfBytes self_bs) →
                    ret = if edSmul edOrderL (edExtToAffine (edExtOfBytes self_bs)) == edZero
                          then 1#8 else 0#8)⌝

abbrev EdwardsPointIsTorsionFreeOk : Prop :=
  DalekBlockOk 19 edwardsPointIsTorsionFreeSpec

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs

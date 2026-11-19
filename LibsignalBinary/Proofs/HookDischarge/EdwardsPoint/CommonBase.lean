/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Common.Spec.Curve25519
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase

/-!
# Shared `.rodata` Addresses, Limb Encodings, and `dataInit` Partition

Defines symbol addresses over `Obj.MultiPlacement` and byte-list aliases for the 11
`.rodata`/`.data.rel.ro` objects of `dalekCliMultiLib`, `2^51`/`2^52` radix evaluation helpers
(`fe51Val`, `sc52Val`, `checkWords64`), and the `dataInit` partition theorem `DalekCliData_eq`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (
  dalekCliMultiLib dalekCliData
  dalekCliData00 dalekCliData01 dalekCliData02 dalekCliData03 dalekCliData04
  dalekCliData05 dalekCliData06 dalekCliData07 dalekCliData08 dalekCliData09 dalekCliData10
  dalekCliData00Bytes dalekCliData01Bytes dalekCliData02Bytes dalekCliData03Bytes
  dalekCliData04Bytes dalekCliData05Bytes dalekCliData06Bytes dalekCliData07Bytes
  dalekCliData08Bytes dalekCliData09Bytes dalekCliData10Bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (resolve_ro10)

/-! ## 1. `.rodata` / `.data.rel.ro` Addresses & Byte Lists -/

/-- `constants::ED25519_BASEPOINT_TABLE` (`&'static EdwardsBasepointTable` 8-byte pointer cell). -/
abbrev ed25519_basepoint_table_ref (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE"
/-- `FieldElement51::ONE` (40 bytes, 5 `u64` limbs). -/
abbrev fe51_one (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.0"
/-- `constants::EDWARDS_D` (40 bytes, 5 `u64` limbs). -/
abbrev fe51_edwards_d (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.6"
/-- `FieldElement51::MINUS_ONE` (`p - 1`, 40 bytes, 5 `u64` limbs). -/
abbrev fe51_minus_one (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.7"
/-- `constants::SQRT_M1` (40 bytes, 5 `u64` limbs). -/
abbrev fe51_sqrt_m1 (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.8"
/-- `constants::RR` (`R^2 mod ℓ = 2^520 mod ℓ`, 40 bytes, 5 `u64` limbs). -/
abbrev sc52_l (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.16"
/-- `constants::R` (`R mod ℓ = 2^260 mod ℓ`, 40 bytes, 5 `u64` limbs). -/
abbrev sc52_rr (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.17"
/-- `constants::EDWARDS_D2` (`2 * d`, 40 bytes, 5 `u64` limbs). -/
abbrev fe51_edwards_d2 (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.22"
/-- `constants::BASEPOINT_ORDER_PRIVATE` (`edOrderL`, 32 bytes). -/
abbrev basepoint_order (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata.cst32+0x0"
/-- `constants::ODD_MULTIPLES_OF_BASEPOINT` (`NafLookupTable8<AffineNielsPoint>`, 7,680 bytes). -/
abbrev odd_multiples_basepoint (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.36"
/-- `constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN` (`EdwardsBasepointTable`, 30,720 bytes). -/
abbrev ed25519_basepoint_table (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN"

abbrev fe51OneBytes : List (BitVec 8) := dalekCliData01Bytes
abbrev fe51EdwardsDBytes : List (BitVec 8) := dalekCliData02Bytes
abbrev fe51MinusOneBytes : List (BitVec 8) := dalekCliData03Bytes
abbrev fe51SqrtM1Bytes : List (BitVec 8) := dalekCliData04Bytes
abbrev sc52LBytes : List (BitVec 8) := dalekCliData05Bytes
abbrev sc52RRBytes : List (BitVec 8) := dalekCliData06Bytes
abbrev fe51EdwardsD2Bytes : List (BitVec 8) := dalekCliData07Bytes
abbrev basepointOrderBytes : List (BitVec 8) := dalekCliData08Bytes
abbrev oddMultiplesBasepointBytes : List (BitVec 8) := dalekCliData09Bytes
abbrev ed25519BasepointTableBytes : List (BitVec 8) := dalekCliData10Bytes

/-! ## 2. 5-Limb `FieldElement51` & `Scalar52` Radix Evaluations -/

/-- Linear checker: the 8-byte chunks of `bs` equal `expected idx, expected (idx + 1), …`
    (`rem` entries) as little-endian `u64` words. -/
@[expose] def checkWords64 (bs : List (BitVec 8)) (expected : Nat → BitVec 64) : Nat → Nat → Bool
  | _, 0 => true
  | idx, rem + 1 =>
    match bs with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      (pack64 b0 b1 b2 b3 b4 b5 b6 b7 == expected idx) &&
      checkWords64 rest expected (idx + 1) rem
    | _ => false

/-- Value of a 5-limb `FieldElement51` (`2^51` radix) in `Nat`. -/
@[expose] def fe51Val (l0 l1 l2 l3 l4 : BitVec 64) : Nat :=
  l0.toNat + l1.toNat * 2 ^ 51 + l2.toNat * 2 ^ 102 + l3.toNat * 2 ^ 153 + l4.toNat * 2 ^ 204

/-- Read a 5-limb `FieldElement51` value from a 40-byte little-endian buffer. -/
@[expose] def fe51ValOfBytes (bs : List (BitVec 8)) : Nat :=
  fe51Val
    (ByteSlice.readLE bs 0 8)
    (ByteSlice.readLE bs 8 8)
    (ByteSlice.readLE bs 16 8)
    (ByteSlice.readLE bs 24 8)
    (ByteSlice.readLE bs 32 8)

/-- Value of a 5-limb `Scalar52` (`2^52` radix) in `Nat`. -/
@[expose] def sc52Val (l0 l1 l2 l3 l4 : BitVec 64) : Nat :=
  l0.toNat + l1.toNat * 2 ^ 52 + l2.toNat * 2 ^ 104 + l3.toNat * 2 ^ 156 + l4.toNat * 2 ^ 208

/-- Read a 5-limb `Scalar52` value from a 40-byte little-endian buffer. -/
@[expose] def sc52ValOfBytes (bs : List (BitVec 8)) : Nat :=
  sc52Val
    (ByteSlice.readLE bs 0 8)
    (ByteSlice.readLE bs 8 8)
    (ByteSlice.readLE bs 16 8)
    (ByteSlice.readLE bs 24 8)
    (ByteSlice.readLE bs 32 8)

/-! ## 3. Exact `dalekCliMultiLib.dataInit` Decomposition -/

/-- The 11 active read-only `.rodata` / `.data.rel.ro` objects of `dalekCliMultiLib` under `mpl`. -/
@[expose] def DalekCliRoActive (mpl : Obj.MultiPlacement) : SepProp :=
  (ed25519_basepoint_table_ref mpl ↦ᵣ Obj.bytesLE 8 (ed25519_basepoint_table mpl)) ∗
  (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
  (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗
  (fe51_minus_one mpl ↦ᵣ fe51MinusOneBytes) ∗
  (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes) ∗
  (sc52_l mpl ↦ᵣ sc52LBytes) ∗
  (sc52_rr mpl ↦ᵣ sc52RRBytes) ∗
  (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes) ∗
  (basepoint_order mpl ↦ᵣ basepointOrderBytes) ∗
  (odd_multiples_basepoint mpl ↦ᵣ oddMultiplesBasepointBytes) ∗
  (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes)

private theorem dalekCliData00Bytes_drop8 : dalekCliData00Bytes.drop 8 = [] := by
  decide +kernel

private theorem patchedData_data00 (mpl : Obj.MultiPlacement) :
    dalekCliMultiLib.patchedData mpl dalekCliData00 =
      Obj.bytesLE 8 (ed25519_basepoint_table mpl) := by
  simp only [dalekCliData00, Obj.MultiPlacedLib.patchedData, List.foldl_cons, List.foldl_nil,
    List.replicate_zero, List.append_nil, Obj.MultiPlacedLib.patchDataReloc, resolve_ro10,
    Obj.addSignedAddr, beq_self_eq_true, ↓reduceIte, List.take_zero, List.nil_append,
    Nat.zero_add, dalekCliData00Bytes_drop8, ed25519_basepoint_table]

/-- Exact equality between `dalekCliMultiLib.dataInit mpl` and `DalekCliRoActive mpl`. -/
theorem DalekCliData_eq (mpl : Obj.MultiPlacement) :
    dalekCliMultiLib.dataInit mpl = DalekCliRoActive mpl := by
  unfold Obj.MultiPlacedLib.dataInit
  have hdata : dalekCliMultiLib.data = dalekCliData := rfl
  rw [hdata]
  simp only [dalekCliData, List.map, patchedData_data00]
  simp only [dalekCliData00, dalekCliData01, dalekCliData02, dalekCliData03, dalekCliData04,
    dalekCliData05, dalekCliData06, dalekCliData07, dalekCliData08, dalekCliData09, dalekCliData10,
    ↓reduceIte, Obj.MultiPlacedLib.patchedData, List.foldl_nil, List.replicate_zero,
    List.append_nil, Obj.sepAll, DalekCliRoActive, ed25519_basepoint_table_ref, fe51_one,
    fe51_edwards_d, fe51_minus_one, fe51_sqrt_m1, sc52_l, sc52_rr, fe51_edwards_d2,
    basepoint_order, odd_multiples_basepoint, ed25519_basepoint_table, fe51OneBytes,
    fe51EdwardsDBytes, fe51MinusOneBytes, fe51SqrtM1Bytes, sc52LBytes, sc52RRBytes,
    fe51EdwardsD2Bytes, basepointOrderBytes, oddMultiplesBasepointBytes,
    ed25519BasepointTableBytes]

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase

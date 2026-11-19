/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Common.Spec.Curve25519
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase

/-!
# Shared `.rodata` addresses, limb encodings, and `dataInit` partition

Shared `.rodata` definitions and radix-`2^51` encodings for `x25519CliMultiLib`:

- `.rodata` symbol addresses (`fe51_one`, `fe51_mont_a24`, `ed25519_basepoint_table`) over
  `Obj.MultiPlacement`.
- Byte-list aliases (`fe51OneBytes`, `fe51MontA24Bytes`, `ed25519BasepointTableBytes`), `a24`,
  `fe51Val`, `fe51ValOfBytes`, and `checkWords64`.
- `X25519CliRoActive` and `X25519CliData_eq : x25519CliMultiLib.dataInit mpl = X25519CliRoActive mpl`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (
  x25519CliMultiLib x25519CliData
  x25519CliData00 x25519CliData01 x25519CliData02
  x25519CliData00Bytes x25519CliData01Bytes x25519CliData02Bytes)

/-! ## 1. `.rodata` Addresses & Byte Lists -/

/-- Montgomery curve constant $a_{24} = (486662 - 2) / 4 = 121665$ (RFC 7748 §5). -/
abbrev a24 : Nat := 121665

/-- `FieldElement51::ONE` (40 bytes, 5 `u64` limbs). -/
abbrev fe51_one (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.0"

/-- `constants::MONTGOMERY_A_PLUS_TWO_OVER_FOUR` (`121666 = a24 + 1`, 40 bytes, 5 `u64` limbs). -/
abbrev fe51_mont_a24 (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.35"

/-- `constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN` (`EdwardsBasepointTable`, 30,720 bytes). -/
abbrev ed25519_basepoint_table (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN"

abbrev fe51OneBytes : List (BitVec 8) := x25519CliData00Bytes
abbrev fe51MontA24Bytes : List (BitVec 8) := x25519CliData01Bytes
abbrev ed25519BasepointTableBytes : List (BitVec 8) := x25519CliData02Bytes

/-! ## 2. 5-Limb `FieldElement51` Radix Evaluation -/

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

/-! ## 3. Exact `x25519CliMultiLib.dataInit` Decomposition -/

/-- The 3 active read-only `.rodata` objects of `x25519CliMultiLib` under `mpl`. -/
@[expose] def X25519CliRoActive (mpl : Obj.MultiPlacement) : SepProp :=
  (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
  (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗
  (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes)

/-- Exact equality between `x25519CliMultiLib.dataInit mpl` and `X25519CliRoActive mpl`. -/
theorem X25519CliData_eq (mpl : Obj.MultiPlacement) :
    x25519CliMultiLib.dataInit mpl = X25519CliRoActive mpl := by
  unfold Obj.MultiPlacedLib.dataInit
  have hdata : x25519CliMultiLib.data = x25519CliData := rfl
  rw [hdata]
  simp only [x25519CliData, List.map, x25519CliData00, x25519CliData01, x25519CliData02,
    ↓reduceIte, Obj.MultiPlacedLib.patchedData, List.foldl_nil, List.replicate_zero,
    List.append_nil, Obj.sepAll, X25519CliRoActive, fe51_one, fe51_mont_a24,
    ed25519_basepoint_table, fe51OneBytes, fe51MontA24Bytes, ed25519BasepointTableBytes]

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase

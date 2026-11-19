/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables

/-!
# Internal subroutine specifications and pure curve/ladder models

Internal specifications for `x25519CliMultiLib` blocks `00..18`. Imports only
`Shared51.CommonBase` and `X25519Ref` (plus proof-body `RoTables`), keeping `Shared51/Math/*`
decoupled from the machine-code proof modules so leaf and caller proofs build in parallel.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (
  p25519 fpAdd fpSub fpMul fpNeg fpSq fpInv fpPow modPow modPowLoop
  leBytesToNat natToLeBytes EdExtPoint edExtZero clampScalarBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519BlockOk X25519BlockConstOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  decodeU255 MontProjPoint montDiffAddAndDouble montLadderLoop x25519 x25519Pubkey)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  fe51Val fe51ValOfBytes
  fe51_one fe51OneBytes fe51_mont_a24 fe51MontA24Bytes
  ed25519_basepoint_table ed25519BasepointTableBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables (
  readLE_cons8 ed25519BasepointTableBytes_length)

/-! ## 1. Little-Endian Word Encoding, Limb Bounds, & Radix-16 Recoding -/

/-- Encode a 64-bit word as 8 little-endian bytes. -/
@[expose] def encodeU64LE (w : BitVec 64) : List (BitVec 8) :=
  [ w.extractLsb' 0 8,
    w.extractLsb' 8 8,
    w.extractLsb' 16 8,
    w.extractLsb' 24 8,
    w.extractLsb' 32 8,
    w.extractLsb' 40 8,
    w.extractLsb' 48 8,
    w.extractLsb' 56 8 ]

/-- Encode a list of 64-bit words as little-endian bytes (`8 * ws.length` bytes). -/
@[expose] def encodeU64LEWords (ws : List (BitVec 64)) : List (BitVec 8) :=
  ws.flatMap encodeU64LE

/-- All 5 limbs of a 40-byte `FieldElement51` buffer are bounded by `bound`. -/
@[expose] def fe51LimbsBounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 40 ∧
  (ByteSlice.readLE bs 0 8).toNat < bound ∧
  (ByteSlice.readLE bs 8 8).toNat < bound ∧
  (ByteSlice.readLE bs 16 8).toNat < bound ∧
  (ByteSlice.readLE bs 24 8).toNat < bound ∧
  (ByteSlice.readLE bs 32 8).toNat < bound

/-- Signed radix-16 recoding (`[i8; 64]`) of a 32-byte scalar `a_bs` (`a_bs[31] ≤ 127`). -/
@[expose] def scalarRadix16Digits (a_bs : List (BitVec 8)) : List (BitVec 8) :=
  let rec go (idx : Nat) (carry : Int) (acc : List (BitVec 8)) : List (BitVec 8) :=
    match idx with
    | 0 => acc.reverse
    | k + 1 =>
      let i := 63 - k
      let byte := (a_bs.getD (i / 2) 0#8).toNat
      let botHalf : Int := if i % 2 == 0 then Int.ofNat (byte &&& 0x0f) else Int.ofNat (byte >>> 4)
      let d := botHalf + carry
      if i < 63 then
        let carry' : Int := (d + 8) / 16
        let digit' : Int := d - carry' * 16
        go k carry' (BitVec.ofInt 8 digit' :: acc)
      else
        go k 0 (BitVec.ofInt 8 d :: acc)
  go 64 0 []

private theorem scalarRadix16Digits_go_length (a_bs : List (BitVec 8)) :
    ∀ (idx : Nat) (carry : Int) (acc : List (BitVec 8)),
      (scalarRadix16Digits.go a_bs idx carry acc).length = acc.length + idx
  | 0, _, acc => by simp [scalarRadix16Digits.go]
  | k + 1, carry, acc => by
    unfold scalarRadix16Digits.go
    dsimp only
    split <;> simp only [scalarRadix16Digits_go_length, List.length_cons] <;> omega

theorem scalarRadix16Digits_length (a_bs : List (BitVec 8)) :
    (scalarRadix16Digits a_bs).length = 64 := by
  simpa [scalarRadix16Digits] using scalarRadix16Digits_go_length a_bs 64 0 []

theorem readLE_congr_off (bs bs' : List (BitVec 8)) (off1 off2 n : Nat)
    (h : ∀ i, i < n → bs.getD (off1 + i) 0#8 = bs'.getD (off2 + i) 0#8) :
    ByteSlice.readLE bs off1 n = ByteSlice.readLE bs' off2 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [ByteSlice.readLE_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem readLE_slice_eq (bs : List (BitVec 8)) (off m k : Nat)
    (h1 : decide (k + 8 ≤ m) = true) :
    ByteSlice.readLE (ProofLib.ByteSlice.slice bs off m) k 8 = ByteSlice.readLE bs (off + k) 8 := by
  have hk : k + 8 ≤ m := of_decide_eq_true h1
  apply readLE_congr_off
  intro i hi
  rw [ByteSlice.getD_slice bs off m (k + i) 0#8 (by omega), Nat.add_assoc]

theorem fpPow_two_eq_fpSq (x : Nat) : fpPow x 2 = fpSq x := by
  unfold fpPow modPow fpSq fpMul
  rw [modPowLoop, modPowLoop, modPowLoop]
  change (1 * (x % p25519 * (x % p25519) % p25519) % p25519) % p25519 =
    x % p25519 * (x % p25519) % p25519
  simp only [Nat.mod_mod, Nat.one_mul]

/-! ## 2. 5-Limb `FieldElement51` Edwards & Montgomery Point Encodings -/

/-- All 5 limbs of a `FieldElement51` at byte offset `off` in `bs` are `< bound`. -/
@[expose] def fe51LimbsBoundedAt (bs : List (BitVec 8)) (off bound : Nat) : Prop :=
  (ByteSlice.readLE bs off 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 8) 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 16) 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 24) 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 32) 8).toNat < bound

/-- Radix-`2^51` integer value of the `FieldElement51` at byte offset `off` in `bs`. -/
@[expose] def fe51ValAt (bs : List (BitVec 8)) (off : Nat) : Nat :=
  fe51Val
    (ByteSlice.readLE bs off 8)
    (ByteSlice.readLE bs (off + 8) 8)
    (ByteSlice.readLE bs (off + 16) 8)
    (ByteSlice.readLE bs (off + 24) 8)
    (ByteSlice.readLE bs (off + 32) 8)

/-- A 160-byte `EdwardsPoint` or `CompletedPoint` buffer has 4 limb-bounded `FieldElement51`
    coordinates `(X, Y, Z, T)` at offsets `0, 40, 80, 120`. -/
@[expose] def fe51Point4Bounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 160 ∧
  fe51LimbsBoundedAt bs 0 bound ∧
  fe51LimbsBoundedAt bs 40 bound ∧
  fe51LimbsBoundedAt bs 80 bound ∧
  fe51LimbsBoundedAt bs 120 bound

/-- A 120-byte `ProjectivePoint` buffer has 3 limb-bounded `FieldElement51`
    coordinates `(X, Y, Z)` at offsets `0, 40, 80`. -/
@[expose] def fe51Point3Bounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 120 ∧
  fe51LimbsBoundedAt bs 0 bound ∧
  fe51LimbsBoundedAt bs 40 bound ∧
  fe51LimbsBoundedAt bs 80 bound

/-- Extract the 4 field coordinates `(X, Y, Z, T) mod p25519` of a 160-byte point buffer. -/
@[expose] def edExtOfBytes (bs : List (BitVec 8)) : EdExtPoint :=
  ⟨fe51ValAt bs 0 % p25519,
   fe51ValAt bs 40 % p25519,
   fe51ValAt bs 80 % p25519,
   fe51ValAt bs 120 % p25519⟩

/-- Extract the 3 projective coordinates `(X, Y, Z) mod p25519` (with `T = 0`) of a 120-byte buffer. -/
@[expose] def edProjOfBytes (bs : List (BitVec 8)) : EdExtPoint :=
  ⟨fe51ValAt bs 0 % p25519,
   fe51ValAt bs 40 % p25519,
   fe51ValAt bs 80 % p25519,
   0⟩

/-- Extended point negation `-(X, Y, Z, T) = (-X mod p, Y mod p, Z mod p, -T mod p)`. -/
@[expose] def edExtNeg (P : EdExtPoint) : EdExtPoint :=
  ⟨fpNeg P.X, P.Y % p25519, P.Z % p25519, fpNeg P.T⟩

/-- `CompletedPoint` result `(X', Y', Z', T')` of `ProjectivePoint::double(X, Y, Z)`. -/
@[expose] def edProjDouble (X Y Z : Nat) : EdExtPoint :=
  let XX := fpSq (X % p25519)
  let YY := fpSq (Y % p25519)
  let ZZ2 := fpAdd (fpSq (Z % p25519)) (fpSq (Z % p25519))
  let Y_plus_X_sq := fpSq (fpAdd (X % p25519) (Y % p25519))
  let YpX2 := fpAdd XX YY
  let YmX2 := fpSub YY XX
  ⟨fpSub Y_plus_X_sq YpX2, YpX2, YmX2, fpSub ZZ2 YmX2⟩

/-- `CompletedPoint` result `(X', Y', Z', T')` of `&EdwardsPoint + &AffineNielsPoint`. -/
@[expose] def edAddAffineNiels (P : EdExtPoint) (y_plus_x y_minus_x xy2d : Nat) : EdExtPoint :=
  let PP := fpMul (fpAdd P.X P.Y) y_plus_x
  let MM := fpMul (fpSub P.Y P.X) y_minus_x
  let TT2d := fpMul P.T xy2d
  let ZZ2 := fpAdd P.Z P.Z
  ⟨fpSub PP MM, fpAdd MM PP, fpAdd TT2d ZZ2, fpSub ZZ2 TT2d⟩

/-- Convert a `CompletedPoint` to a `ProjectivePoint` (`X*T, Y*Z, Z*T`). -/
@[expose] def edAsProjective (C : EdExtPoint) : EdExtPoint :=
  ⟨fpMul C.X C.T, fpMul C.Y C.Z, fpMul C.Z C.T, 0⟩

/-- Convert a `CompletedPoint` to an `EdwardsPoint` (`X*T, Y*Z, Z*T, X*Y`). -/
@[expose] def edAsExtended (C : EdExtPoint) : EdExtPoint :=
  ⟨fpMul C.X C.T, fpMul C.Y C.Z, fpMul C.Z C.T, fpMul C.X C.Y⟩

/-- Quadruple point doubling (`[16]P`) computed by `mul_by_pow_2(P, 4)`. -/
@[expose] def edDouble4 (P : EdExtPoint) : EdExtPoint :=
  let P1 := edAsProjective (edProjDouble P.X P.Y P.Z)
  let P2 := edAsProjective (edProjDouble P1.X P1.Y P1.Z)
  let P3 := edAsProjective (edProjDouble P2.X P2.Y P2.Z)
  edAsExtended (edProjDouble P3.X P3.Y P3.Z)

/-- Montgomery `u`-coordinate `(Z + Y) * (Z - Y)⁻¹ mod p` computed by `EdwardsPoint::to_montgomery`. -/
@[expose] def edExtToMontgomeryU (P : EdExtPoint) : Nat :=
  fpMul (fpAdd P.Z P.Y) (fpInv (fpSub P.Z P.Y))

/-- All 3 `FieldElement51` coordinates of a 120-byte `AffineNielsPoint` at `base` are `< bound`. -/
@[expose] def fe51AffineNielsBoundedAt (bs : List (BitVec 8)) (base bound : Nat) : Prop :=
  fe51LimbsBoundedAt bs base bound ∧
  fe51LimbsBoundedAt bs (base + 40) bound ∧
  fe51LimbsBoundedAt bs (base + 80) bound

/-- A 960-byte `LookupTable<AffineNielsPoint>` (8 entries × 120 bytes) has all limbs `< bound`. -/
@[expose] def fe51LookupTable8Bounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 960 ∧
  fe51AffineNielsBoundedAt bs 0 bound ∧ fe51AffineNielsBoundedAt bs 120 bound ∧
  fe51AffineNielsBoundedAt bs 240 bound ∧ fe51AffineNielsBoundedAt bs 360 bound ∧
  fe51AffineNielsBoundedAt bs 480 bound ∧ fe51AffineNielsBoundedAt bs 600 bound ∧
  fe51AffineNielsBoundedAt bs 720 bound ∧ fe51AffineNielsBoundedAt bs 840 bound

/-- The `j`-th `AffineNielsPoint` entry `(y_plus_x, y_minus_x, xy2d)` mod `p25519`. -/
@[expose] def edTableEntryAt (table_bs : List (BitVec 8)) (j : Nat) : Nat × Nat × Nat :=
  (fe51ValAt table_bs (120 * j) % p25519,
   fe51ValAt table_bs (120 * j + 40) % p25519,
   fe51ValAt table_bs (120 * j + 80) % p25519)

/-- Constant-time signed lookup `LookupTable<AffineNielsPoint>::select(table, x)`. -/
@[expose] def edSelectAffineNiels (table_bs : List (BitVec 8)) (x : BitVec 8) : Nat × Nat × Nat :=
  let (ypx, ymx, xy2d) :=
    if x == 8#8 || x == -8#8 then edTableEntryAt table_bs 7
    else if x == 7#8 || x == -7#8 then edTableEntryAt table_bs 6
    else if x == 6#8 || x == -6#8 then edTableEntryAt table_bs 5
    else if x == 5#8 || x == -5#8 then edTableEntryAt table_bs 4
    else if x == 4#8 || x == -4#8 then edTableEntryAt table_bs 3
    else if x == 3#8 || x == -3#8 then edTableEntryAt table_bs 2
    else if x == 2#8 || x == -2#8 then edTableEntryAt table_bs 1
    else if x == 1#8 || x == -1#8 then edTableEntryAt table_bs 0
    else (1, 1, 0)
  if x.msb then (ymx, ypx, fpNeg xy2d) else (ypx, ymx, xy2d)

/-- A 30,720-byte `EdwardsBasepointTable` (`[LookupTable<AffineNielsPoint>; 32]`) has all 32
    960-byte sub-tables limb-bounded by `< bound`. -/
@[expose] def fe51BasepointTable32Bounded (table_bs : List (BitVec 8)) (bound : Nat) : Prop :=
  table_bs.length = 30720 ∧
  ∀ i < 32, fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * i) 960) bound

theorem fe51AffineNielsBoundedAt_mono {bs : List (BitVec 8)} {base b1 b2 : Nat}
    (h : fe51AffineNielsBoundedAt bs base b1) (hle : b1 ≤ b2 := by decide) :
    fe51AffineNielsBoundedAt bs base b2 :=
  ⟨⟨Nat.lt_of_lt_of_le h.1.1 hle, Nat.lt_of_lt_of_le h.1.2.1 hle, Nat.lt_of_lt_of_le h.1.2.2.1 hle,
    Nat.lt_of_lt_of_le h.1.2.2.2.1 hle, Nat.lt_of_lt_of_le h.1.2.2.2.2 hle⟩,
   ⟨Nat.lt_of_lt_of_le h.2.1.1 hle, Nat.lt_of_lt_of_le h.2.1.2.1 hle, Nat.lt_of_lt_of_le h.2.1.2.2.1 hle,
    Nat.lt_of_lt_of_le h.2.1.2.2.2.1 hle, Nat.lt_of_lt_of_le h.2.1.2.2.2.2 hle⟩,
   ⟨Nat.lt_of_lt_of_le h.2.2.1 hle, Nat.lt_of_lt_of_le h.2.2.2.1 hle, Nat.lt_of_lt_of_le h.2.2.2.2.1 hle,
    Nat.lt_of_lt_of_le h.2.2.2.2.2.1 hle, Nat.lt_of_lt_of_le h.2.2.2.2.2.2 hle⟩⟩

theorem fe51LookupTable8Bounded_mono {bs : List (BitVec 8)} {b1 b2 : Nat}
    (h : fe51LookupTable8Bounded bs b1) (hle : b1 ≤ b2 := by decide) :
    fe51LookupTable8Bounded bs b2 :=
  ⟨h.1,
   fe51AffineNielsBoundedAt_mono h.2.1 hle,
   fe51AffineNielsBoundedAt_mono h.2.2.1 hle,
   fe51AffineNielsBoundedAt_mono h.2.2.2.1 hle,
   fe51AffineNielsBoundedAt_mono h.2.2.2.2.1 hle,
   fe51AffineNielsBoundedAt_mono h.2.2.2.2.2.1 hle,
   fe51AffineNielsBoundedAt_mono h.2.2.2.2.2.2.1 hle,
   fe51AffineNielsBoundedAt_mono h.2.2.2.2.2.2.2.1 hle,
   fe51AffineNielsBoundedAt_mono h.2.2.2.2.2.2.2.2 hle⟩

theorem fe51BasepointTable32Bounded_mono {table_bs : List (BitVec 8)} {b1 b2 : Nat}
    (h : fe51BasepointTable32Bounded table_bs b1) (hle : b1 ≤ b2 := by decide) :
    fe51BasepointTable32Bounded table_bs b2 :=
  ⟨h.1, fun i hi => fe51LookupTable8Bounded_mono (h.2 i hi) hle⟩

/-- Single radix-16 step of `EdwardsBasepointTable::mul_base`. -/
@[expose] def edMulBaseStep (table_bs : List (BitVec 8)) (i : Nat) (d : BitVec 8)
    (acc : EdExtPoint) : EdExtPoint :=
  let (ypx, ymx, xy2d) := edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960) d
  edAsExtended (edAddAffineNiels acc ypx ymx xy2d)

/-- Curried single-iteration step of `EdwardsBasepointTable::mul_base` at table index `i`. -/
@[expose] def edMulBaseStepAt (table_bs digits : List (BitVec 8)) (parity i : Nat)
    (acc : EdExtPoint) : EdExtPoint :=
  edMulBaseStep table_bs i (digits.getD (2 * i + parity) 0#8) acc

/-- Generic structural loop running `step` for `rem` iterations starting at index `i`. -/
@[expose] def edMulBaseLoopWith {α : Type} (step : Nat → α → α) (i rem : Nat) (acc : α) : α :=
  Nat.rec (motive := fun _ => Nat → α → α)
    (fun _ acc => acc) (fun _ ih i acc => ih (i + 1) (step i acc)) rem i acc

/-- Structural recursion for `rem` iterations of the odd (`parity = 1`) or even (`parity = 0`)
    loop of `EdwardsBasepointTable::mul_base`. -/
@[expose] def edMulBaseLoop (table_bs digits : List (BitVec 8)) (parity i rem : Nat)
    (acc : EdExtPoint) : EdExtPoint :=
  edMulBaseLoopWith (edMulBaseStepAt table_bs digits parity) i rem acc

/-- Pure projective model of `<EdwardsBasepointTable as BasepointTable>::mul_base`. -/
@[expose] def edMulBase (table_bs scalar_bs : List (BitVec 8)) : EdExtPoint :=
  let digits := scalarRadix16Digits scalar_bs
  edMulBaseLoop table_bs digits 0 0 32 (edDouble4 (edMulBaseLoop table_bs digits 1 0 32 edExtZero))

/-- All 5 limbs of a `FieldElement51` at byte offset `off` in `bs` are `< bound` (Montgomery alias). -/
abbrev montFe51LimbsBoundedAt := fe51LimbsBoundedAt

/-- Radix-`2^51` integer value at byte offset `off` in `bs` (Montgomery alias). -/
abbrev montFe51ValAt := fe51ValAt

/-- An 80-byte `montgomery::ProjectivePoint` buffer `(U, W)` has two limb-bounded `FieldElement51`
    coordinates at offsets `0` and `40`. -/
@[expose] def montProjBounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 80 ∧
  montFe51LimbsBoundedAt bs 0 bound ∧
  montFe51LimbsBoundedAt bs 40 bound

/-- Extract `(U mod p25519, W mod p25519)` from an 80-byte `montgomery::ProjectivePoint` buffer. -/
@[expose] def montProjOfBytes (bs : List (BitVec 8)) : MontProjPoint :=
  ⟨montFe51ValAt bs 0 % p25519, montFe51ValAt bs 40 % p25519⟩

/-! ## 3. Clamping & `.rodata` Constant Limb Bounds -/

theorem clampScalarBytes_length_of_eq32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    (clampScalarBytes bs).length = 32 := by
  simp [clampScalarBytes, h]

private theorem clamp_top_byte_le_127 (b : BitVec 8) :
    (((b &&& 0x7f#8) ||| 0x40#8)).toNat ≤ 127 := by
  revert b; decide

theorem clampScalarBytes_getD31_le_127 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ((clampScalarBytes bs).getD 31 0#8).toNat ≤ 127 := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (exfalso; simp at h; done)
  exact clamp_top_byte_le_127 b31

theorem fe51MontA24_bounded : fe51LimbsBounded fe51MontA24Bytes (2 ^ 54) := by
  unfold fe51LimbsBounded; decide +kernel

private def checkWordsBounded (bs : List (BitVec 8)) (bound : Nat) : Nat → Bool
  | 0 => true
  | rem + 1 => match bs with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      decide ((pack64 b0 b1 b2 b3 b4 b5 b6 b7).toNat < bound) && checkWordsBounded rest bound rem
    | _ => false

private theorem of_checkWordsBounded {bs : List (BitVec 8)} {bound rem k : Nat}
    (h : checkWordsBounded bs bound rem = true) (hk : k < rem) :
    (ByteSlice.readLE bs (8 * k) 8).toNat < bound := by
  induction rem generalizing bs k with
  | zero => omega
  | succ rem ih =>
    unfold checkWordsBounded at h
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try contradiction
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases k with _ | k
    · rw [Nat.mul_zero, ← ByteSlice.pack64_eq_readLE_8]; exact h.1
    · rw [show 8 * (k + 1) = 8 * k + 8 by omega, readLE_cons8]; exact ih h.2 (by omega)

private theorem checkWordsBounded_ed25519BasepointTable :
    checkWordsBounded ed25519BasepointTableBytes (2 ^ 52) 3840 = true := by decide +kernel

/-- All 3,840 limbs in `.rodata` `ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN` are `< 2 ^ 52`. -/
theorem ed25519BasepointTableBytes_bounded :
    fe51BasepointTable32Bounded ed25519BasepointTableBytes (2 ^ 52) := by
  refine ⟨ed25519BasepointTableBytes_length, fun i hi => ?_⟩
  have hlen : (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960).length = 960 := by
    change ((ed25519BasepointTableBytes.drop (960 * i)).take 960).length = 960
    simp only [List.length_take, List.length_drop, ed25519BasepointTableBytes_length]; omega
  have hlimb (j : Nat) (hj : j < 120) :
      (ByteSlice.readLE
        (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960) (8 * j) 8).toNat <
          2 ^ 52 := by
    rw [readLE_slice_eq ed25519BasepointTableBytes (960 * i) 960 (8 * j)
          (by rw [decide_eq_true_eq]; omega),
        show 960 * i + 8 * j = 8 * (120 * i + j) by omega]
    exact of_checkWordsBounded checkWordsBounded_ed25519BasepointTable (by omega)
  have hentry (e : Nat) (he : e < 8) :
      fe51AffineNielsBoundedAt
        (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960) (120 * e) (2 ^ 52) :=
    ⟨⟨by simpa [show 120 * e = 8 * (15 * e) by omega] using hlimb (15 * e) (by omega),
      by simpa [show 120 * e + 8 = 8 * (15 * e + 1) by omega] using hlimb (15 * e + 1) (by omega),
      by simpa [show 120 * e + 16 = 8 * (15 * e + 2) by omega] using hlimb (15 * e + 2) (by omega),
      by simpa [show 120 * e + 24 = 8 * (15 * e + 3) by omega] using hlimb (15 * e + 3) (by omega),
      by simpa [show 120 * e + 32 = 8 * (15 * e + 4) by omega] using hlimb (15 * e + 4) (by omega)⟩,
     ⟨by simpa [show 120 * e + 40 = 8 * (15 * e + 5) by omega] using hlimb (15 * e + 5) (by omega),
      by simpa [show 120 * e + 40 + 8 = 8 * (15 * e + 6) by omega] using hlimb (15 * e + 6) (by omega),
      by simpa [show 120 * e + 40 + 16 = 8 * (15 * e + 7) by omega] using hlimb (15 * e + 7) (by omega),
      by simpa [show 120 * e + 40 + 24 = 8 * (15 * e + 8) by omega] using hlimb (15 * e + 8) (by omega),
      by simpa [show 120 * e + 40 + 32 = 8 * (15 * e + 9) by omega] using hlimb (15 * e + 9) (by omega)⟩,
     ⟨by simpa [show 120 * e + 80 = 8 * (15 * e + 10) by omega] using hlimb (15 * e + 10) (by omega),
      by simpa [show 120 * e + 80 + 8 = 8 * (15 * e + 11) by omega] using hlimb (15 * e + 11) (by omega),
      by simpa [show 120 * e + 80 + 16 = 8 * (15 * e + 12) by omega] using hlimb (15 * e + 12) (by omega),
      by simpa [show 120 * e + 80 + 24 = 8 * (15 * e + 13) by omega] using hlimb (15 * e + 13) (by omega),
      by simpa [show 120 * e + 80 + 32 = 8 * (15 * e + 14) by omega] using hlimb (15 * e + 14) (by omega)⟩⟩
  exact ⟨hlen, hentry 0 (by omega), hentry 1 (by omega), hentry 2 (by omega), hentry 3 (by omega),
    hentry 4 (by omega), hentry 5 (by omega), hentry 6 (by omega), hentry 7 (by omega)⟩

/-! ## 4. Per-Block Subroutine Specifications (`x25519CliMultiLib` Blocks `00..18`) -/

/-- `subtle::black_box::<u8>` (`Blk00`, 5 insns, stack 16): returns `v` (`w0`) unchanged. -/
abbrev rust_spec blackBoxU8Spec (v : u8) : (ret : u8)
  stack   16
  ensures ⌜ret = v⌝

abbrev BlackBoxU8Ok : Prop := X25519BlockConstOk 0 blackBoxU8Spec

/-- `<&FieldElement51 as Mul>::mul` (`Blk01`, 166 insns, stack 224). -/
abbrev rust_spec fe51MulSpec (out : sret) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ₛ b_bs)
  requires      out ↦ₛ out_bs
  stack         224
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      (fe51ValOfBytes a_bs * fe51ValOfBytes b_bs) % p25519⌝

abbrev Fe51MulOk : Prop := X25519BlockConstOk 1 fe51MulSpec

/-- Read-only-rhs variant of `<&FieldElement51 as Mul>::mul` (`Blk01`, stack 224). -/
abbrev rust_spec fe51MulRoRightSpec (out : sret) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ᵣ b_bs)
  requires      out ↦ₛ out_bs
  stack         224
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      (fe51ValOfBytes a_bs * fe51ValOfBytes b_bs) % p25519⌝

abbrev Fe51MulRoRightOk : Prop := X25519BlockConstOk 1 fe51MulRoRightSpec

/-- Read-only-lhs variant of `<&FieldElement51 as Mul>::mul` (`Blk01`, stack 224), used when
    `differential_add_and_double` passes `.rodata` `fe51_mont_a24` in `x0`. -/
abbrev rust_spec fe51MulRoLeftSpec (out : sret) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)
  preserves     (a ↦ᵣ a_bs) ∗ (b ↦ₛ b_bs)
  requires      out ↦ₛ out_bs
  stack         224
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      (fe51ValOfBytes a_bs * fe51ValOfBytes b_bs) % p25519⌝

abbrev Fe51MulRoLeftOk : Prop := X25519BlockConstOk 1 fe51MulRoLeftSpec

/-- `FieldElement51::pow2k` (`Blk02`, 100 insns, stack 96). -/
abbrev rust_spec fe51Pow2kSpec (out : sret) (a : ptr) (k : u32)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ 0 < k.toNat ∧ k.toNat < 256
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  stack         96
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      fpPow (fe51ValOfBytes a_bs % p25519) (2 ^ k.toNat)⌝

abbrev Fe51Pow2kOk : Prop := X25519BlockConstOk 2 fe51Pow2kSpec

/-- `Scalar::as_radix_16` (`Blk03`, 173 insns, stack 0). -/
abbrev rust_spec scalarAsRadix16Spec (out : ptr) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 64 ∧ a_bs.length = 32 ∧ (a_bs.getD 31 0#8).toNat ≤ 127
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  ensures       out ↦ₛ scalarRadix16Digits a_bs

abbrev ScalarAsRadix16Ok : Prop := X25519BlockConstOk 3 scalarAsRadix16Spec

/-- `Rev::nth` (`Blk04`, 41 insns, stack 16) at `n = 1#64` on `[0, 256)`. -/
abbrev rust_spec revNthBit254Spec
    (iter : ptr) (n : u64) (ghost scalar_ptr : BitVec 64) (ghost scalar_bs : List (BitVec 8)) : (ret : u8)
  requires_cond n = 1#64 ∧ scalar_bs.length = 32
  preserves     (iter ↦₆₄ scalar_ptr) ∗ ((iter + 8#64) ↦₆₄ 0#64) ∗ (scalar_ptr ↦ₛ scalar_bs)
  requires      (iter + 16#64) ↦₆₄ 256#64
  stack         16
  ensures       ((iter + 16#64) ↦₆₄ 254#64) ∗
                ⌜ret = BitVec.ofNat 8 ((leBytesToNat scalar_bs / 2 ^ 254) % 2)⌝

abbrev RevNthBit254Ok : Prop := X25519BlockConstOk 4 revNthBit254Spec

/-- `FieldElement51::pow22501` (`Blk05`, 101 insns, stack 1040). -/
abbrev rust_spec fe51Pow22501Spec (out : ptr) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 80 ∧ fe51LimbsBounded a_bs (2 ^ 54)
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  stack         1040
  ensures       ∃∗ t19_bs : List (BitVec 8), ∃∗ t3_bs : List (BitVec 8),
                  (out ↦ₛ (t19_bs ++ t3_bs)) ∗
                  ⌜fe51LimbsBounded t19_bs (2 ^ 52) ∧
                    fe51LimbsBounded t3_bs (2 ^ 52) ∧
                    fe51ValOfBytes t19_bs % p25519 =
                      fpPow (fe51ValOfBytes a_bs % p25519) (2 ^ 250 - 1) ∧
                    fe51ValOfBytes t3_bs % p25519 =
                      fpPow (fe51ValOfBytes a_bs % p25519) 11⌝

abbrev Fe51Pow22501Ok : Prop := X25519BlockConstOk 5 fe51Pow22501Spec

/-- `<LookupTable<AffineNielsPoint>>::select` (`Blk06`, 191 insns, stack 192). -/
abbrev rust_spec lookupTableAffineNielsSelectSpec (out : ptr) (table : ptr) (x : u8)
    (ghost out_bs table_bs : List (BitVec 8))
  requires_cond out_bs.length = 120 ∧ fe51LookupTable8Bounded table_bs (2 ^ 53)
  preserves     table ↦ᵣ table_bs
  requires      out ↦ₛ out_bs
  stack         192
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜res_bs.length = 120 ∧
                    fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) ∧
                    (fe51ValAt res_bs 0 % p25519,
                     fe51ValAt res_bs 40 % p25519,
                     fe51ValAt res_bs 80 % p25519) = edSelectAffineNiels table_bs x⌝

abbrev LookupTableAffineNielsSelectOk : Prop :=
  X25519BlockConstOk 6 lookupTableAffineNielsSelectSpec

/-- `<ProjectivePoint>::double` (`Blk07`, 144 insns, stack 400). -/
abbrev rust_spec projectivePointDoubleSpec (out : sret) (self : ptr)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧
                self_bs.length = 120 ∧
                fe51LimbsBoundedAt self_bs 0 (2 ^ 53) ∧
                fe51LimbsBoundedAt self_bs 40 (2 ^ 53) ∧
                fe51LimbsBoundedAt self_bs 80 (2 ^ 54)
  preserves     self ↦ₛ self_bs
  requires      out ↦ₛ out_bs
  stack         400
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜res_bs.length = 160 ∧
                    fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
                    fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
                    edExtOfBytes res_bs =
                      edProjDouble (fe51ValAt self_bs 0) (fe51ValAt self_bs 40) (fe51ValAt self_bs 80)⌝

abbrev ProjectivePointDoubleOk : Prop := X25519BlockConstOk 7 projectivePointDoubleSpec

/-- `<&EdwardsPoint as Add<&AffineNielsPoint>>::add` (`Blk08`, 152 insns, stack 528). -/
abbrev rust_spec edwardsPointAddAffineNielsSpec (out : sret) (self : ptr) (other : ptr)
    (ghost out_bs self_bs other_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧
                self_bs.length = 160 ∧
                other_bs.length = 120 ∧
                fe51LimbsBoundedAt self_bs 0 (2 ^ 53) ∧
                fe51LimbsBoundedAt self_bs 40 (2 ^ 53) ∧
                fe51LimbsBoundedAt self_bs 80 (2 ^ 52) ∧
                fe51LimbsBoundedAt self_bs 120 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 0 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 40 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 80 (2 ^ 54)
  preserves     (self ↦ₛ self_bs) ∗ (other ↦ₛ other_bs)
  requires      out ↦ₛ out_bs
  stack         528
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜res_bs.length = 160 ∧
                    fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
                    fe51LimbsBoundedAt res_bs 80 (2 ^ 54) ∧
                    fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
                    edExtOfBytes res_bs =
                      edAddAffineNiels (edExtOfBytes self_bs)
                        (fe51ValAt other_bs 0 % p25519)
                        (fe51ValAt other_bs 40 % p25519)
                        (fe51ValAt other_bs 80 % p25519)⌝

abbrev EdwardsPointAddAffineNielsOk : Prop :=
  X25519BlockConstOk 8 edwardsPointAddAffineNielsSpec

/-- `<EdwardsPoint>::mul_by_pow_2` (`Blk09`, 79 insns, stack 912, `k = 4#32` specialization). -/
abbrev rust_spec edwardsPointMulByPow2_4Spec (out : sret) (self : ptr) (k : u32)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧ fe51Point4Bounded self_bs (2 ^ 53) ∧ k = 4#32
  preserves     self ↦ₛ self_bs
  requires      out ↦ₛ out_bs
  stack         912
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
                    edExtOfBytes res_bs = edDouble4 (edExtOfBytes self_bs)⌝

abbrev EdwardsPointMulByPow2_4Ok : Prop := X25519BlockConstOk 9 edwardsPointMulByPow2_4Spec

/-- `<EdwardsPoint>::to_montgomery` (`Blk10`, 171 insns, stack 1392). -/
abbrev rust_spec edwardsPointToMontgomerySpec (out : sret) (self : ptr)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ fe51Point4Bounded self_bs (2 ^ 53)
  preserves     self ↦ₛ self_bs
  requires      out ↦ₛ out_bs
  stack         1392
  ensures       out ↦ₛ natToLeBytes 32 (edExtToMontgomeryU (edExtOfBytes self_bs))

abbrev EdwardsPointToMontgomeryOk : Prop := X25519BlockConstOk 10 edwardsPointToMontgomerySpec

/-- `<montgomery::ProjectivePoint>::as_affine` (`Blk11`, 130 insns, stack 1312). -/
abbrev rust_spec montProjectiveAsAffineSpec
    (out : sret) (self : ptr) (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ montProjBounded self_bs (2 ^ 54)
  preserves     self ↦ₛ self_bs
  requires      out ↦ₛ out_bs
  stack         1312
  ensures       out ↦ₛ natToLeBytes 32
                  (fpMul (montProjOfBytes self_bs).U (fpInv (montProjOfBytes self_bs).W))

abbrev MontProjectiveAsAffineOk : Prop := X25519BlockConstOk 11 montProjectiveAsAffineSpec

/-- `montgomery::differential_add_and_double` (`Blk12`, 238 insns, stack 1056). -/
abbrev rust_spec montDiffAddAndDoubleSpec
    (ctx mpl : Obj.MultiPlacement)
    (P : ptr) (Q : ptr) (u1 : ptr)
    (ghost p_bs q_bs u1_bs : List (BitVec 8))
  requires_cond montProjBounded p_bs (2 ^ 53) ∧
                montProjBounded q_bs (2 ^ 53) ∧
                fe51LimbsBounded u1_bs (2 ^ 54)
  preserves     (u1 ↦ₛ u1_bs) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes)
  requires      (P ↦ₛ p_bs) ∗ (Q ↦ₛ q_bs)
  stack         1056
  ensures       ∃∗ p_out : List (BitVec 8), ∃∗ q_out : List (BitVec 8),
                  (P ↦ₛ p_out) ∗ (Q ↦ₛ q_out) ∗
                  ⌜montProjBounded p_out (2 ^ 52) ∧
                    montProjBounded q_out (2 ^ 52) ∧
                    montProjOfBytes p_out =
                      (montDiffAddAndDouble (fe51ValOfBytes u1_bs % p25519)
                        (montProjOfBytes p_bs) (montProjOfBytes q_bs)).1 ∧
                    montProjOfBytes q_out =
                      (montDiffAddAndDouble (fe51ValOfBytes u1_bs % p25519)
                        (montProjOfBytes p_bs) (montProjOfBytes q_bs)).2⌝

abbrev MontDiffAddAndDoubleOk : Prop := X25519BlockOk 12 montDiffAddAndDoubleSpec

/-- `<EdwardsBasepointTable as BasepointTable>::mul_base` (`Blk13`, 167 insns, stack 1680). -/
abbrev rust_spec edwardsBasepointTableMulBaseSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (table : ptr) (scalar : ptr)
    (ghost out_bs table_bs scalar_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧ fe51BasepointTable32Bounded table_bs (2 ^ 53) ∧
                scalar_bs.length = 32 ∧ (scalar_bs.getD 31 0#8).toNat ≤ 127
  preserves     (table ↦ᵣ table_bs) ∗ (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes)
  requires      out ↦ₛ out_bs
  stack         1680
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
                    edExtOfBytes res_bs = edMulBase table_bs scalar_bs⌝

abbrev EdwardsBasepointTableMulBaseOk : Prop := X25519BlockOk 13 edwardsBasepointTableMulBaseSpec

/-- `<EdwardsPoint>::mul_base_clamped` (`Blk14`, 11 insns, stack 1680). -/
abbrev rust_spec edwardsPointMulBaseClampedSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (bytes : ptr)
    (ghost out_bs bytes_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧ bytes_bs.length = 32
  preserves     (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes)
  requires      (out ↦ₛ out_bs) ∗ (bytes ↦ₛ bytes_bs)
  stack         1680
  ensures       ∃∗ res_bs : List (BitVec 8),
                  let clamped := clampScalarBytes bytes_bs
                  (out ↦ₛ res_bs) ∗ (bytes ↦ₛ clamped) ∗
                  ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
                    edExtOfBytes res_bs = edMulBase ed25519BasepointTableBytes clamped⌝

abbrev EdwardsPointMulBaseClampedOk : Prop := X25519BlockOk 14 edwardsPointMulBaseClampedSpec

/-- `<&MontgomeryPoint as Mul<&Scalar>>::mul` (`Blk15`, 211 insns, stack 1680). -/
abbrev rust_spec montgomeryPointMulSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (self : ptr) (scalar : ptr)
    (ghost out_bs self_bs scalar_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ self_bs.length = 32 ∧ scalar_bs.length = 32
  preserves     (self ↦ₛ self_bs) ∗ (scalar ↦ₛ scalar_bs) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes)
  requires      out ↦ₛ out_bs
  stack         1680
  ensures       out ↦ₛ natToLeBytes 32
                  (let u1 := decodeU255 self_bs % p25519
                   let res := montLadderLoop 255 (leBytesToNat scalar_bs) u1 ⟨1, 0⟩ ⟨u1, 1⟩
                   fpMul res.U (fpInv res.W))

abbrev MontgomeryPointMulOk : Prop := X25519BlockOk 15 montgomeryPointMulSpec

/-- `<MontgomeryPoint>::mul_clamped` (`Blk16`, 17 insns, stack 1728). -/
abbrev rust_spec montgomeryPointMulClampedSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (self : ptr) (bytes : ptr)
    (ghost out_bs self_bs bytes_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ self_bs.length = 32 ∧ bytes_bs.length = 32
  preserves     (self ↦ₛ self_bs) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes)
  requires      (out ↦ₛ out_bs) ∗ (bytes ↦ₛ bytes_bs)
  stack         1728
  ensures       (out ↦ₛ x25519 bytes_bs self_bs) ∗ (bytes ↦ₛ clampScalarBytes bytes_bs)

abbrev MontgomeryPointMulClampedOk : Prop := X25519BlockOk 16 montgomeryPointMulClampedSpec

/-- `<StaticSecret>::diffie_hellman` (`Blk17`, 13 insns, stack 1808). -/
abbrev rust_spec staticSecretDiffieHellmanSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (self : ptr) (theirPublic : ptr)
    (ghost out_bs self_bs pub_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ self_bs.length = 32 ∧ pub_bs.length = 32
  preserves     (self ↦ₛ self_bs) ∗ (theirPublic ↦ₛ pub_bs) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes)
  requires      out ↦ₛ out_bs
  stack         1808
  ensures       out ↦ₛ x25519 self_bs pub_bs

abbrev StaticSecretDiffieHellmanOk : Prop := X25519BlockOk 17 staticSecretDiffieHellmanSpec

/-- `<PublicKey as From<&StaticSecret>>::from` (`Blk18`, 17 insns, stack 1904). -/
abbrev rust_spec publicKeyFromSecretSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (secret : ptr)
    (ghost out_bs secret_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ secret_bs.length = 32
  preserves     (secret ↦ₛ secret_bs) ∗
                (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes)
  requires      out ↦ₛ out_bs
  stack         1904
  ensures       out ↦ₛ x25519Pubkey secret_bs

abbrev PublicKeyFromStaticSecretOk : Prop := X25519BlockOk 18 publicKeyFromSecretSpec

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs

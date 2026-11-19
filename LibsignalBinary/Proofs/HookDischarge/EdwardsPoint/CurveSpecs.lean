/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs

/-!
# Curve Models, Lookup Tables, NAF Models, and Subroutine Specifications

Pure curve, lookup-table, and NAF models together with `DalekBlockOk` / `DalekBlockConstOk`
contracts shared by `Math/` and the `EdwardsPoint` machine-code proofs, keeping `Math/`
independent of machine-code proof modules.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (
  p25519 edOrderL edD edD2 sqrtM1 fpAdd fpSub fpMul fpNeg fpSq fpInv fpPow modPow modPowLoop
  leBytesToNat natToLeBytes EdPoint EdExtPoint edZero edExtZero edOnCurve
  edExtToAffine edExtOfAffine edSmul encodeEd decodeEdDalek recoverXEven)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekBlockOk DalekBlockConstOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51Val fe51OneBytes fe51EdwardsDBytes fe51MinusOneBytes fe51SqrtM1Bytes
  fe51EdwardsD2Bytes oddMultiplesBasepointBytes ed25519BasepointTableBytes
  fe51_one fe51_edwards_d fe51_minus_one fe51_sqrt_m1 fe51_edwards_d2
  odd_multiples_basepoint)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  scalarRadix16Digits)

/-! ## 1. Montgomery Lift & Slice Read Helpers -/

/-- Montgomery curve constant $a_{24} = (486662 - 2) / 4 = 121665$ (RFC 7748 §5). -/
abbrev a24 : Nat := 121665

/-- Decode a 32-byte little-endian Montgomery $u$-coordinate by masking bit 255
    (RFC 7748 §5 `decodeUCoordinate(u, 255)`). -/
@[expose] def decodeU255 (bs : List (BitVec 8)) : Nat :=
  leBytesToNat (bs.take 32) % (2 ^ 255)

/-- Lift a 32-byte Montgomery $u$-coordinate and sign bit `sign ∈ {0, 1}` to an affine twisted
    Edwards point (`MontgomeryPoint::to_edwards`). -/
@[expose] def montToEdwards (bs : List (BitVec 8)) (sign : Nat) : Option EdPoint :=
  let u := decodeU255 bs % p25519
  if u == p25519 - 1 then none
  else
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    match recoverXEven y with
    | none => none
    | some xEven =>
      let x := if sign % 2 == 1 then fpNeg xEven else xEven
      some ⟨x, y⟩

/-- Exact `libsignal-core` `PublicKey::is_canonical` predicate (`curve.rs:165-190`). -/
@[expose] def isCanonicalX25519 (bs : List (BitVec 8)) : Bool :=
  bs.length == 32 &&
  leBytesToNat bs < p25519 &&
  match montToEdwards bs 0 with
  | none => false
  | some P => edSmul edOrderL P == edZero

/-- The 5 canonical low-order Montgomery $u$-coordinates in $\mathbb{F}_p$ (RFC 7748 §6.1). -/
@[expose] def lowOrderUs : List Nat :=
  [ 0,
    1,
    325606250916557431795983626356110631294008115727848805560023387167927233504,
    39382357235489614581723060781553021112529911719440698176882885853963445705823,
    p25519 - 1 ]

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

/-! ## 2. 5-Limb `FieldElement51` Point Encodings & Curve Models -/

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

/-- `CompletedPoint` result `(X', Y', Z', T')` of `&EdwardsPoint + &ProjectiveNielsPoint`. -/
@[expose] def edAddProjNiels (P N : EdExtPoint) : EdExtPoint :=
  let YpX := fpAdd P.X P.Y
  let YmX := fpSub P.Y P.X
  let PP := fpMul YpX N.X
  let MM := fpMul YmX N.Y
  let TT2d := fpMul P.T N.T
  let ZZ := fpMul P.Z N.Z
  let ZZ2 := fpAdd ZZ ZZ
  ⟨fpSub PP MM, fpAdd MM PP, fpAdd TT2d ZZ2, fpSub ZZ2 TT2d⟩

/-- `CompletedPoint` result `(X', Y', Z', T')` of `&EdwardsPoint - &ProjectiveNielsPoint`. -/
@[expose] def edSubProjNiels (P N : EdExtPoint) : EdExtPoint :=
  let PP := fpMul (fpAdd P.X P.Y) N.Y
  let MM := fpMul (fpSub P.Y P.X) N.X
  let TT2d := fpMul P.T N.T
  let ZZ := fpMul P.Z N.Z
  let ZZ2 := fpAdd ZZ ZZ
  ⟨fpSub PP MM, fpAdd MM PP, fpSub ZZ2 TT2d, fpAdd TT2d ZZ2⟩

/-- `CompletedPoint` result `(X', Y', Z', T')` of `&EdwardsPoint + &AffineNielsPoint`. -/
@[expose] def edAddAffineNiels (P : EdExtPoint) (y_plus_x y_minus_x xy2d : Nat) : EdExtPoint :=
  let PP := fpMul (fpAdd P.X P.Y) y_plus_x
  let MM := fpMul (fpSub P.Y P.X) y_minus_x
  let TT2d := fpMul P.T xy2d
  let ZZ2 := fpAdd P.Z P.Z
  ⟨fpSub PP MM, fpAdd MM PP, fpAdd TT2d ZZ2, fpSub ZZ2 TT2d⟩

/-- `CompletedPoint` result `(X', Y', Z', T')` of `&EdwardsPoint - &AffineNielsPoint`. -/
@[expose] def edSubAffineNiels (P : EdExtPoint) (y_plus_x y_minus_x xy2d : Nat) : EdExtPoint :=
  let PP := fpMul (fpAdd P.X P.Y) y_minus_x
  let MM := fpMul (fpSub P.Y P.X) y_plus_x
  let TT2d := fpMul P.T xy2d
  let ZZ2 := fpAdd P.Z P.Z
  ⟨fpSub PP MM, fpAdd MM PP, fpSub ZZ2 TT2d, fpAdd TT2d ZZ2⟩

/-- Convert a `CompletedPoint` to a `ProjectivePoint` (`X*T, Y*Z, Z*T`). -/
@[expose] def edAsProjective (C : EdExtPoint) : EdExtPoint :=
  ⟨fpMul C.X C.T, fpMul C.Y C.Z, fpMul C.Z C.T, 0⟩

/-- Convert a `CompletedPoint` to an `EdwardsPoint` (`X*T, Y*Z, Z*T, X*Y`). -/
@[expose] def edAsExtended (C : EdExtPoint) : EdExtPoint :=
  ⟨fpMul C.X C.T, fpMul C.Y C.Z, fpMul C.Z C.T, fpMul C.X C.Y⟩

/-- Triple point doubling (`[8]P`) computed by `mul_by_pow_2(P, 3)`. -/
@[expose] def edDouble3 (P : EdExtPoint) : EdExtPoint :=
  let P1 := edAsProjective (edProjDouble P.X P.Y P.Z)
  let P2 := edAsProjective (edProjDouble P1.X P1.Y P1.Z)
  edAsExtended (edProjDouble P2.X P2.Y P2.Z)

/-- Quadruple point doubling (`[16]P`) computed by `mul_by_pow_2(P, 4)`. -/
@[expose] def edDouble4 (P : EdExtPoint) : EdExtPoint :=
  let P1 := edAsProjective (edProjDouble P.X P.Y P.Z)
  let P2 := edAsProjective (edProjDouble P1.X P1.Y P1.Z)
  let P3 := edAsProjective (edProjDouble P2.X P2.Y P2.Z)
  edAsExtended (edProjDouble P3.X P3.Y P3.Z)

/-- Projective equality of two extended Edwards points over $\mathbb{F}_p$. -/
@[expose] def edPointEq (P Q : EdExtPoint) : Bool :=
  (fpMul P.X Q.Z == fpMul Q.X P.Z) && (fpMul P.Y Q.Z == fpMul Q.Y P.Z)

/-! ## 3. Basepoint, Variable-Base, & NAF Lookup Table Pure Models -/

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

/-- Convert an extended `EdwardsPoint` `(X, Y, Z, T)` to a `ProjectiveNielsPoint`
    `(Y + X, Y - X, Z, T * 2d)` over $\mathbb{F}_p$. -/
@[expose] def edExtToProjNiels (P : EdExtPoint) : EdExtPoint :=
  ⟨fpAdd P.X P.Y, fpSub P.Y P.X, P.Z % p25519, fpMul P.T edD2⟩

/-- Step of `LookupTable<ProjectiveNielsPoint>::from`: `[i + 1]A -> [i + 2]A`. -/
@[expose] def projNielsTableStep (A Ai : EdExtPoint) : EdExtPoint :=
  edExtToProjNiels (edAsExtended (edAddProjNiels A Ai))

/-- The `i`-th entry (`[i + 1]A`) of `LookupTable<ProjectiveNielsPoint>::from(A)`. -/
@[expose] def projNielsTablePoints (A : EdExtPoint) : Nat → EdExtPoint
  | 0 => edExtToProjNiels A
  | i + 1 => projNielsTableStep A (projNielsTablePoints A i)

/-- A 1,280-byte `LookupTable<ProjectiveNielsPoint>` has 8 160-byte entries `< bound`. -/
@[expose] def fe51ProjNielsTable8Bounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 1280 ∧
  ∀ i < 8, fe51Point4Bounded (ProofLib.ByteSlice.slice bs (160 * i) 160) bound

/-- The `j`-th `ProjectiveNielsPoint` entry from a 1,280-byte table. -/
@[expose] def edProjNielsEntryAt (table_bs : List (BitVec 8)) (j : Nat) : EdExtPoint :=
  ⟨fe51ValAt table_bs (160 * j) % p25519,
   fe51ValAt table_bs (160 * j + 40) % p25519,
   fe51ValAt table_bs (160 * j + 80) % p25519,
   fe51ValAt table_bs (160 * j + 120) % p25519⟩

theorem edProjNielsEntryAt_eq_slice (table_bs : List (BitVec 8)) (j : Nat) :
    edProjNielsEntryAt table_bs j =
      edExtOfBytes (ProofLib.ByteSlice.slice table_bs (160 * j) 160) := by
  unfold edProjNielsEntryAt edExtOfBytes fe51ValAt
  simp (disch := decide) only [readLE_slice_eq, Nat.add_zero, Nat.add_assoc]

/-- Constant-time signed lookup `LookupTable<ProjectiveNielsPoint>::select(table, x)`. -/
@[expose] def edSelectProjNiels (table_bs : List (BitVec 8)) (x : BitVec 8) : EdExtPoint :=
  let Q :=
    if x == 8#8 || x == -8#8 then edProjNielsEntryAt table_bs 7
    else if x == 7#8 || x == -7#8 then edProjNielsEntryAt table_bs 6
    else if x == 6#8 || x == -6#8 then edProjNielsEntryAt table_bs 5
    else if x == 5#8 || x == -5#8 then edProjNielsEntryAt table_bs 4
    else if x == 4#8 || x == -4#8 then edProjNielsEntryAt table_bs 3
    else if x == 3#8 || x == -3#8 then edProjNielsEntryAt table_bs 2
    else if x == 2#8 || x == -2#8 then edProjNielsEntryAt table_bs 1
    else if x == 1#8 || x == -1#8 then edProjNielsEntryAt table_bs 0
    else ⟨1, 1, 1, 0⟩
  if x.msb then ⟨Q.Y, Q.X, Q.Z, fpNeg Q.T⟩ else Q

/-- Point-level model of `LookupTable<ProjectiveNielsPoint>::select` over `T : Nat → EdExtPoint`. -/
@[expose] def edSelectProjNielsPoints (T : Nat → EdExtPoint) (x : BitVec 8) : EdExtPoint :=
  let Q :=
    if x == 8#8 || x == -8#8 then T 7
    else if x == 7#8 || x == -7#8 then T 6
    else if x == 6#8 || x == -6#8 then T 5
    else if x == 5#8 || x == -5#8 then T 4
    else if x == 4#8 || x == -4#8 then T 3
    else if x == 3#8 || x == -3#8 then T 2
    else if x == 2#8 || x == -2#8 then T 1
    else if x == 1#8 || x == -1#8 then T 0
    else ⟨1, 1, 1, 0⟩
  if x.msb then ⟨Q.Y, Q.X, Q.Z, fpNeg Q.T⟩ else Q

theorem edSelectProjNiels_eq_points {table_bs : List (BitVec 8)} {T : Nat → EdExtPoint}
    (x : BitVec 8)
    (htab : ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice table_bs (160 * i) 160) = T i) :
    edSelectProjNiels table_bs x = edSelectProjNielsPoints T x := by
  unfold edSelectProjNiels edSelectProjNielsPoints
  simp only [edProjNielsEntryAt_eq_slice,
    htab 0 (by decide), htab 1 (by decide), htab 2 (by decide), htab 3 (by decide),
    htab 4 (by decide), htab 5 (by decide), htab 6 (by decide), htab 7 (by decide)]

/-- One radix-16 Horner step of `<&EdwardsPoint as Mul<&Scalar>>::mul`. -/
@[expose] def edVarBaseStep (T : Nat → EdExtPoint) (d : BitVec 8) (C : EdExtPoint) : EdExtPoint :=
  edAddProjNiels (edDouble4 (edAsExtended C)) (edSelectProjNielsPoints T d)

/-- Generic downward structural loop (`k = m - 1` down to `0`). -/
@[expose] def edVarBaseLoopWith {α : Type} (step : Nat → α → α) : Nat → α → α
  | 0, acc => acc
  | m + 1, acc => edVarBaseLoopWith step m (step m acc)

/-- Downward 63-step Horner loop of `<&EdwardsPoint as Mul<&Scalar>>::mul`. -/
@[expose] def edVarBaseLoop (T : Nat → EdExtPoint) (digits : List (BitVec 8)) (m : Nat)
    (C : EdExtPoint) : EdExtPoint :=
  edVarBaseLoopWith (fun k acc => edVarBaseStep T (digits.getD k 0#8) acc) m C

/-- Pure projective model of `<&EdwardsPoint as Mul<&Scalar>>::mul(point_bs, s_bs)`. -/
@[expose] def edVarBaseMul (point_bs s_bs : List (BitVec 8)) : EdExtPoint :=
  let T := projNielsTablePoints (edExtOfBytes point_bs)
  let digits := scalarRadix16Digits s_bs
  edAsExtended (edVarBaseLoop T digits 63
    (edAddProjNiels edExtZero (edSelectProjNielsPoints T (digits.getD 63 0#8))))

/-- Convert an extended `EdwardsPoint` `(X, Y, Z, T)` to a `ProjectiveNielsPoint` (for NAF-5). -/
@[expose] def edAsProjNiels (P : EdExtPoint) : EdExtPoint :=
  ⟨fpAdd P.X P.Y, fpSub P.Y P.X, P.Z % p25519, fpMul P.T edD2⟩

/-- Step of `NafLookupTable5::from`: given `A2 = [2]A` and `Ai = [2i + 1]A`, computes `[2i + 3]A`. -/
@[expose] def nafTable5Step (A2 Ai : EdExtPoint) : EdExtPoint :=
  edAsProjNiels (edAsExtended (edAddProjNiels A2 Ai))

/-- The `i`-th entry (`[2i + 1]A`) of `NafLookupTable5<ProjectiveNielsPoint>::from(A)`. -/
@[expose] def nafTable5Points (A : EdExtPoint) : Nat → EdExtPoint
  | 0 => edAsProjNiels A
  | i + 1 => nafTable5Step (edAsExtended (edProjDouble A.X A.Y A.Z)) (nafTable5Points A i)

/-- A 1,280-byte `NafLookupTable5<ProjectiveNielsPoint>` buffer has 8 160-byte entries `< bound`. -/
@[expose] def fe51NafTable5Bounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 1280 ∧
  ∀ i < 8, fe51Point4Bounded (ProofLib.ByteSlice.slice bs (160 * i) 160) bound

/-- 5-bit window extracted at bit offset `pos` from the 40-byte padded scalar buffer `x_buf`. -/
@[expose] def naf5BitBuf (x_buf : List (BitVec 8)) (pos : Nat) : BitVec 64 :=
  let w0 := ByteSlice.readLE x_buf (8 * (pos / 64)) 8
  if 59 ≤ pos % 64 then
    let w1 := ByteSlice.readLE x_buf (8 * (pos / 64) + 8) 8
    (w1 <<< 1 <<< (63 - pos % 64) ||| w0 >>> (pos % 64)) &&& 31#64
  else
    (w0 >>> (pos % 64)) &&& 31#64

/-- Signed byte written by NAF width-5 recoding when `width` is odd. -/
@[expose] def naf5Digit (width : BitVec 64) : BitVec 8 :=
  (if (15#64).ult width then 224#8 else 0#8) + BitVec.zeroExtend 8 width

/-- Next carry (`0#64` or `1#64`) produced by NAF width-5 recoding when `width` is odd. -/
@[expose] def naf5NextCarry (width : BitVec 64) : BitVec 64 :=
  if width.ule 15#64 then 0#64 else 1#64

/-- Structural fuel-based model of the width-5 NAF recoding loop (`fuel = 256 - pos`). -/
@[expose] def naf5Loop (x_buf : List (BitVec 8)) :
    Nat → Nat → BitVec 64 → List (BitVec 8) → List (BitVec 8)
  | 0, _, _, naf => naf
  | fuel + 1, pos, carry, naf =>
    let width := naf5BitBuf x_buf pos + carry
    if width.getLsbD 0 then
      let naf' := ByteSlice.write8 naf pos (naf5Digit width)
      let carry' := naf5NextCarry width
      if pos + 5 < 256 then
        naf5Loop x_buf (fuel - 4) (pos + 5) carry' naf'
      else
        naf'
    else
      if pos + 1 < 256 then
        naf5Loop x_buf fuel (pos + 1) carry naf
      else
        naf

/-- Valid signed width-5 NAF byte: either `0 ≤ d < 16` or `-15 ≤ d < 0`. -/
@[expose] def naf5ByteValid (d : BitVec 8) : Bool :=
  d.ult 16#8 || (240#8).ult d

/-- 8-bit window extracted at bit offset `pos` from the 40-byte padded scalar buffer `x_buf`. -/
@[expose] def naf8BitBuf (x_buf : List (BitVec 8)) (pos : Nat) : BitVec 64 :=
  let w0 := ByteSlice.readLE x_buf (8 * (pos / 64)) 8
  if 56 ≤ pos % 64 then
    let w1 := ByteSlice.readLE x_buf (8 * (pos / 64) + 8) 8
    BitVec.setWidth 64 (BitVec.setWidth 8 (w1 <<< 1 <<< (63 - pos % 64) ||| w0 >>> (pos % 64)))
  else
    BitVec.setWidth 64 (BitVec.setWidth 8 (w0 >>> (pos % 64)))

/-- Next carry (`0#64` or `1#64`) produced by NAF width-8 recoding when `width` is odd. -/
@[expose] def naf8NextCarry (width : BitVec 64) : BitVec 64 :=
  if width.ule 127#64 then 0#64 else 1#64

/-- Structural fuel-based model of the width-8 NAF recoding loop (`fuel = 256 - pos`). -/
@[expose] def naf8Loop (x_buf : List (BitVec 8)) :
    Nat → Nat → BitVec 64 → List (BitVec 8) → List (BitVec 8)
  | 0, _, _, naf => naf
  | fuel + 1, pos, carry, naf =>
    let width := carry + naf8BitBuf x_buf pos
    if width.getLsbD 0 then
      let naf' := ByteSlice.write8 naf pos (BitVec.setWidth 8 width)
      let carry' := naf8NextCarry width
      if pos + 8 < 256 then
        naf8Loop x_buf (fuel - 7) (pos + 8) carry' naf'
      else
        naf'
    else
      if pos + 1 < 256 then
        naf8Loop x_buf fuel (pos + 1) carry naf
      else
        naf

/-- Scan downward from index `i` for the highest index where `naf_a` or `naf_b` is nonzero. -/
@[expose] def findMaxNafIdx (naf_a naf_b : List (BitVec 8)) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if naf_a.getD (k + 1) 0#8 == 0#8 then
      if naf_b.getD (k + 1) 0#8 == 0#8 then findMaxNafIdx naf_a naf_b k else k + 1
    else k + 1

/-- One signed width-5 NAF step for $A$ using the 8-entry `ProjectiveNielsPoint` table `table_A`. -/
@[expose] def edStrausStepA (C : EdExtPoint) (table_A : Nat → EdExtPoint)
    (da : BitVec 8) : EdExtPoint :=
  if da == 0#8 then C
  else if !da.msb then
    edAddProjNiels (edAsExtended C) (table_A (da.toNat / 2))
  else
    edSubProjNiels (edAsExtended C) (table_A ((256 - da.toNat) / 2))

/-- The `idx`-th 120-byte `AffineNielsPoint` entry `(y+x, y-x, 2dxy)` from `oddMultiplesBasepointBytes`. -/
@[expose] def edAffineBasepointEntry (idx : Nat) : Nat × Nat × Nat :=
  let sl := ProofLib.ByteSlice.slice oddMultiplesBasepointBytes (120 * idx) 120
  (fe51ValAt sl 0 % p25519, fe51ValAt sl 40 % p25519, fe51ValAt sl 80 % p25519)

/-- One signed width-8 NAF step for the basepoint $B$ using `oddMultiplesBasepointBytes`. -/
@[expose] def edStrausStepB (C : EdExtPoint) (db : BitVec 8) : EdExtPoint :=
  if db == 0#8 then C
  else if !db.msb then
    let e := edAffineBasepointEntry (db.toNat / 2)
    edAddAffineNiels (edAsExtended C) e.1 e.2.1 e.2.2
  else
    let e := edAffineBasepointEntry ((256 - db.toNat) / 2)
    edSubAffineNiels (edAsExtended C) e.1 e.2.1 e.2.2

/-- One full iteration of the Straus Horner loop at index `i`. -/
@[expose] def edStrausStep (P : EdExtPoint) (table_A : Nat → EdExtPoint)
    (da db : BitVec 8) : EdExtPoint :=
  let C0 := edProjDouble P.X P.Y P.Z
  let C1 := edStrausStepA C0 table_A da
  let C2 := edStrausStepB C1 db
  edAsProjective C2

/-- Downward Straus Horner loop from `i` down to `0` (inclusive). -/
@[expose] def edStrausLoop (naf_a naf_b : List (BitVec 8)) (table_A : Nat → EdExtPoint) :
    Nat → EdExtPoint → EdExtPoint
  | 0, P => edStrausStep P table_A (naf_a.getD 0 0#8) (naf_b.getD 0 0#8)
  | k + 1, P =>
    edStrausLoop naf_a naf_b table_A k
      (edStrausStep P table_A (naf_a.getD (k + 1) 0#8) (naf_b.getD (k + 1) 0#8))

/-- Final conversion `ProjectivePoint::to_extended`: `(X*Z, Y*Z, Z^2, X*Y)`. -/
@[expose] def edProjectiveToExtended (P : EdExtPoint) : EdExtPoint :=
  ⟨fpMul P.X P.Z, fpMul P.Y P.Z, fpPow P.Z 2, fpMul P.X P.Y⟩

/-- Pure functional model of `EdwardsPoint::vartime_double_scalar_mul_basepoint(a, A, b)`. -/
@[expose] def edDoubleScalarMulBasepoint (a_bs A_bs b_bs : List (BitVec 8)) : EdExtPoint :=
  let naf_a := naf5Loop (a_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
  let naf_b := naf8Loop (b_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
  let max_i := findMaxNafIdx naf_a naf_b 255
  let table_A := nafTable5Points (edExtOfBytes A_bs)
  let r_final := edStrausLoop naf_a naf_b table_A max_i ⟨0, 1, 1, 0⟩
  edProjectiveToExtended r_final

/-! ## 4. Curve, Lookup-Table, Codec, & Double-Scalar-Mul Subroutine Contracts -/

/-- `<ProjectivePoint>::double` (`B13`, 144 insns, stack 400). -/
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

abbrev ProjectivePointDoubleOk : Prop :=
  DalekBlockConstOk 13 projectivePointDoubleSpec

/-- `<&EdwardsPoint as Add<&ProjectiveNielsPoint>>::add` (`B28`, 156 insns, stack 576). -/
abbrev rust_spec edwardsPointAddProjNielsSpec (out : sret) (self : ptr) (other : ptr)
    (ghost out_bs self_bs other_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧
                self_bs.length = 160 ∧
                other_bs.length = 160 ∧
                fe51LimbsBoundedAt self_bs 0 (2 ^ 53) ∧
                fe51LimbsBoundedAt self_bs 40 (2 ^ 53) ∧
                fe51LimbsBoundedAt self_bs 80 (2 ^ 54) ∧
                fe51LimbsBoundedAt self_bs 120 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 0 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 40 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 80 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 120 (2 ^ 54)
  preserves     (self ↦ₛ self_bs) ∗ (other ↦ₛ other_bs)
  requires      out ↦ₛ out_bs
  stack         576
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜res_bs.length = 160 ∧
                    fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
                    fe51LimbsBoundedAt res_bs 80 (2 ^ 54) ∧
                    fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
                    edExtOfBytes res_bs =
                      edAddProjNiels (edExtOfBytes self_bs) (edExtOfBytes other_bs)⌝

abbrev EdwardsPointAddProjNielsOk : Prop :=
  DalekBlockConstOk 28 edwardsPointAddProjNielsSpec

/-- `<&EdwardsPoint as Sub<&ProjectiveNielsPoint>>::sub` (`B29`, 156 insns, stack 576). -/
abbrev rust_spec edwardsPointSubProjNielsSpec (out : sret) (self : ptr) (other : ptr)
    (ghost out_bs self_bs other_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧
                self_bs.length = 160 ∧
                other_bs.length = 160 ∧
                fe51LimbsBoundedAt self_bs 0 (2 ^ 53) ∧
                fe51LimbsBoundedAt self_bs 40 (2 ^ 53) ∧
                fe51LimbsBoundedAt self_bs 80 (2 ^ 54) ∧
                fe51LimbsBoundedAt self_bs 120 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 0 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 40 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 80 (2 ^ 54) ∧
                fe51LimbsBoundedAt other_bs 120 (2 ^ 54)
  preserves     (self ↦ₛ self_bs) ∗ (other ↦ₛ other_bs)
  requires      out ↦ₛ out_bs
  stack         576
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜res_bs.length = 160 ∧
                    fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
                    fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 120 (2 ^ 54) ∧
                    edExtOfBytes res_bs =
                      edSubProjNiels (edExtOfBytes self_bs) (edExtOfBytes other_bs)⌝

abbrev EdwardsPointSubProjNielsOk : Prop :=
  DalekBlockConstOk 29 edwardsPointSubProjNielsSpec

/-- `<&EdwardsPoint as Add<&AffineNielsPoint>>::add` (`B31`, 152 insns, stack 528). -/
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
  DalekBlockConstOk 31 edwardsPointAddAffineNielsSpec

/-- Read-only-rhs variant of `<&EdwardsPoint as Add<&AffineNielsPoint>>::add` (`B31`, stack 528),
    used when adding `.rodata` `ODD_MULTIPLES_OF_BASEPOINT` entries (`other ↦ᵣ`). -/
abbrev rust_spec edwardsPointAddAffineNielsRoSpec (out : sret) (self : ptr) (other : ptr)
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
  preserves     (self ↦ₛ self_bs) ∗ (other ↦ᵣ other_bs)
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

abbrev EdwardsPointAddAffineNielsRoOk : Prop :=
  DalekBlockConstOk 31 edwardsPointAddAffineNielsRoSpec

/-- `<&EdwardsPoint as Sub<&AffineNielsPoint>>::sub` (`B32`, 152 insns, stack 528). -/
abbrev rust_spec edwardsPointSubAffineNielsSpec (out : sret) (self : ptr) (other : ptr)
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
                    fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 120 (2 ^ 54) ∧
                    edExtOfBytes res_bs =
                      edSubAffineNiels (edExtOfBytes self_bs)
                        (fe51ValAt other_bs 0 % p25519)
                        (fe51ValAt other_bs 40 % p25519)
                        (fe51ValAt other_bs 80 % p25519)⌝

abbrev EdwardsPointSubAffineNielsOk : Prop :=
  DalekBlockConstOk 32 edwardsPointSubAffineNielsSpec

/-- Read-only-rhs variant of `<&EdwardsPoint as Sub<&AffineNielsPoint>>::sub` (`B32`, stack 528),
    used when subtracting `.rodata` `ODD_MULTIPLES_OF_BASEPOINT` entries (`other ↦ᵣ`). -/
abbrev rust_spec edwardsPointSubAffineNielsRoSpec (out : sret) (self : ptr) (other : ptr)
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
  preserves     (self ↦ₛ self_bs) ∗ (other ↦ᵣ other_bs)
  requires      out ↦ₛ out_bs
  stack         528
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜res_bs.length = 160 ∧
                    fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
                    fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 120 (2 ^ 54) ∧
                    edExtOfBytes res_bs =
                      edSubAffineNiels (edExtOfBytes self_bs)
                        (fe51ValAt other_bs 0 % p25519)
                        (fe51ValAt other_bs 40 % p25519)
                        (fe51ValAt other_bs 80 % p25519)⌝

abbrev EdwardsPointSubAffineNielsRoOk : Prop :=
  DalekBlockConstOk 32 edwardsPointSubAffineNielsRoSpec

/-- `<EdwardsPoint>::mul_by_pow_2` (`B18`, 79 insns, stack 912, `k = 3#32` specialization). -/
abbrev rust_spec edwardsPointMulByPow2Spec (out : sret) (self : ptr) (k : u32)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧ fe51Point4Bounded self_bs (2 ^ 53) ∧ k = 3#32
  preserves     self ↦ₛ self_bs
  requires      out ↦ₛ out_bs
  stack         912
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
                    edExtOfBytes res_bs = edDouble3 (edExtOfBytes self_bs)⌝

abbrev EdwardsPointMulByPow2Ok : Prop :=
  DalekBlockConstOk 18 edwardsPointMulByPow2Spec

/-- `<EdwardsPoint>::mul_by_pow_2` (`B18`, 79 insns, stack 912, `k = 4#32` specialization). -/
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

abbrev EdwardsPointMulByPow2_4Ok : Prop :=
  DalekBlockConstOk 18 edwardsPointMulByPow2_4Spec

/-- `<LookupTable<AffineNielsPoint>>::select` (`B09`, 191 insns, stack 192). -/
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
  DalekBlockConstOk 9 lookupTableAffineNielsSelectSpec

/-- `<EdwardsBasepointTable as BasepointTable>::mul_base` (`B26`, 167 insns, stack 1680). -/
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

abbrev EdwardsBasepointTableMulBaseOk : Prop :=
  DalekBlockOk 26 edwardsBasepointTableMulBaseSpec

/-- `<&Scalar as Mul<&EdwardsBasepointTable>>::mul` (`B27`, 4 insns, stack 1680). -/
abbrev rust_spec scalarMulBasepointTableSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (scalar : ptr) (table : ptr)
    (ghost out_bs scalar_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧ scalar_bs.length = 32 ∧ (scalar_bs.getD 31 0#8).toNat ≤ 127
  preserves     (scalar ↦ₛ scalar_bs) ∗
                (table ↦ᵣ ed25519BasepointTableBytes) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes)
  requires      out ↦ₛ out_bs
  stack         1680
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
                    edExtOfBytes res_bs = edMulBase ed25519BasepointTableBytes scalar_bs⌝

abbrev ScalarMulBasepointTableOk : Prop :=
  DalekBlockOk 27 scalarMulBasepointTableSpec

/-- `<LookupTable<ProjectiveNielsPoint> as From<&EdwardsPoint>>::from` (`B25`, 323 insns, stack 2480). -/
abbrev rust_spec lookupTableProjNielsFromSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 1280 ∧ fe51Point4Bounded a_bs (2 ^ 53)
  preserves     (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes)
  requires      out ↦ₛ out_bs
  stack         2480
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51ProjNielsTable8Bounded res_bs (2 ^ 54) ∧
                    ∀ i < 8,
                      edExtOfBytes (ProofLib.ByteSlice.slice res_bs (160 * i) 160) =
                        projNielsTablePoints (edExtOfBytes a_bs) i⌝

abbrev LookupTableProjNielsFromOk : Prop :=
  DalekBlockOk 25 lookupTableProjNielsFromSpec

/-- `<LookupTable<ProjectiveNielsPoint>>::select` (`B10`, 229 insns, stack 240). -/
abbrev rust_spec lookupTableProjNielsSelectSpec (out : ptr) (table : ptr) (x : u8)
    (ghost out_bs table_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧ fe51ProjNielsTable8Bounded table_bs (2 ^ 54)
  preserves     table ↦ₛ table_bs
  requires      out ↦ₛ out_bs
  stack         240
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51Point4Bounded res_bs (2 ^ 54) ∧
                    edExtOfBytes res_bs = edSelectProjNiels table_bs x⌝

abbrev LookupTableProjNielsSelectOk : Prop :=
  DalekBlockConstOk 10 lookupTableProjNielsSelectSpec

/-- `<NafLookupTable5<ProjectiveNielsPoint> as From<&EdwardsPoint>>::from` (`B20`, 317 insns, stack 2640). -/
abbrev rust_spec nafLookupTable5FromSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 1280 ∧ fe51Point4Bounded a_bs (2 ^ 52)
  preserves     (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes)
  requires      out ↦ₛ out_bs
  stack         2640
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51NafTable5Bounded res_bs (2 ^ 53) ∧
                    ∀ i < 8,
                      edExtOfBytes (ProofLib.ByteSlice.slice res_bs (160 * i) 160) =
                        nafTable5Points (edExtOfBytes a_bs) i⌝

abbrev NafLookupTable5FromOk : Prop :=
  DalekBlockOk 20 nafLookupTable5FromSpec

/-- `<EdwardsPoint>::vartime_double_scalar_mul_basepoint` (`B17`, 316 insns, stack 5008). -/
abbrev rust_spec vartimeDoubleScalarMulBasepointSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (a : ptr) (A : ptr) (b_sc : ptr)
    (ghost out_bs a_bs A_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 160 ∧ a_bs.length = 32 ∧
                fe51Point4Bounded A_bs (2 ^ 52) ∧ b_bs.length = 32
  preserves     (a ↦ₛ a_bs) ∗ (A ↦ₛ A_bs) ∗ (b_sc ↦ₛ b_bs) ∗
                (odd_multiples_basepoint mpl ↦ᵣ oddMultiplesBasepointBytes) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
                (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes)
  requires      out ↦ₛ out_bs
  stack         5008
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
                    edExtOfBytes res_bs = edDoubleScalarMulBasepoint a_bs A_bs b_bs⌝

abbrev VartimeDoubleScalarMulBasepointOk : Prop :=
  DalekBlockOk 17 vartimeDoubleScalarMulBasepointSpec

/-- `<EdwardsPoint as ConstantTimeEq>::ct_eq` (`B30`, 408 insns, stack 512). -/
abbrev rust_spec edwardsPointCtEqSpec (self : ptr) (other : ptr)
    (ghost self_bs other_bs : List (BitVec 8)) : (ret : u8)
  requires_cond fe51Point4Bounded self_bs (2 ^ 54) ∧ fe51Point4Bounded other_bs (2 ^ 54)
  preserves     (self ↦ₛ self_bs) ∗ (other ↦ₛ other_bs)
  stack         512
  ensures       ⌜ret = if edPointEq (edExtOfBytes self_bs) (edExtOfBytes other_bs) then 1#8 else 0#8⌝

abbrev EdwardsPointCtEqOk : Prop :=
  DalekBlockConstOk 30 edwardsPointCtEqSpec

/-- `<EdwardsPoint>::compress` (`B14`, 204 insns, stack 1552). -/
abbrev rust_spec edwardsPointCompressSpec (out : sret) (self : ptr)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ fe51Point4Bounded self_bs (2 ^ 54)
  preserves     self ↦ₛ self_bs
  requires      out ↦ₛ out_bs
  stack         1552
  ensures       out ↦ₛ encodeEd (edExtToAffine (edExtOfBytes self_bs))

abbrev EdwardsPointCompressOk : Prop :=
  DalekBlockConstOk 14 edwardsPointCompressSpec

/-- `<CompressedEdwardsY>::decompress` (`B05`, 176 insns, stack 2176). -/
abbrev rust_spec compressedEdwardsYDecompressSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (self : ptr)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 168 ∧ self_bs.length = 32
  preserves     self ↦ₛ self_bs ∗
                (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗
                (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes)
  requires      out ↦ₛ out_bs
  stack         2176
  ensures       match decodeEdDalek self_bs with
                | none =>
                  ∃∗ pad_bs,
                    ⌜pad_bs.length = 160⌝ ∗
                    (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦ₛ pad_bs)
                | some P =>
                  ∃∗ pt_bs,
                    ⌜fe51Point4Bounded pt_bs (2 ^ 52) ∧
                     edExtOfBytes pt_bs = edExtOfAffine P⌝ ∗
                    (out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦ₛ pt_bs)

abbrev CompressedEdwardsYDecompressOk : Prop :=
  DalekBlockOk 5 compressedEdwardsYDecompressSpec

/-- `<MontgomeryPoint>::to_edwards` (`B08`, 267 insns, stack 2576). -/
abbrev rust_spec montgomeryPointToEdwardsSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (self : ptr) (sign : u8)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 168 ∧ self_bs.length = 32
  preserves     self ↦ₛ self_bs ∗
                (fe51_minus_one mpl ↦ᵣ fe51MinusOneBytes) ∗
                (fe51_edwards_d mpl ↦ᵣ fe51EdwardsDBytes) ∗
                (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes)
  requires      out ↦ₛ out_bs
  stack         2576
  ensures       match montToEdwards self_bs (sign.toNat % 2) with
                | none =>
                  ∃∗ pad_bs,
                    ⌜pad_bs.length = 160⌝ ∗
                    (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦ₛ pad_bs)
                | some P =>
                  ∃∗ pt_bs,
                    ⌜fe51Point4Bounded pt_bs (2 ^ 52) ∧
                     edExtOfBytes pt_bs = edExtOfAffine P⌝ ∗
                    (out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦ₛ pt_bs)

abbrev MontgomeryPointToEdwardsOk : Prop :=
  DalekBlockOk 8 montgomeryPointToEdwardsSpec

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs

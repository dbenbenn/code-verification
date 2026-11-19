/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec -- proof-setup: allow-public-import

/-!
# Curve Coordinate Models & Basepoint Table Checker, Part 1 (`LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1`)

Pure `0-sorry` mathematical bridge proofs for `.rodata` `AffineNiels` extraction, `ProjectivePoint`,
`CompletedPoint`, `edDouble3`, `edDouble4`, `edPointEq`, `AffineNiels`, and `ProjectiveNiels`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib
open VerifiedLibraries.Common (
  p25519 fpAdd fpSub fpNeg fpMul fpPow fpInv edD edD2 EdPoint EdExtPoint edZero edExtZero
  edExtOfAffine edExtToAffine edBasepoint edOnCurve edExtAdd edAdd edNeg edSub
  recoverXEven)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  ed25519BasepointTableBytes fe51Val)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  readLE_cons8)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  readLE_slice_eq fpPow_two_eq_fpSq fe51ValAt edExtNeg edProjDouble edAddProjNiels
  edSubProjNiels edAddAffineNiels edSubAffineNiels edAsProjective edAsExtended edDouble3
  edDouble4 edPointEq)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field (
  p25519_pos fpAdd_lt fpSub_lt fpNeg_lt fpMul_lt)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  Fp edOnCurve_fp_eq edOnCurve_edZero edOnCurve_edNeg edAdd_x_lt edAdd_y_lt edAdd_fp_x
  edAdd_fp_y edAdd_fp_denom_add_ne_zero edAdd_fp_denom_sub_ne_zero edOnCurve_edAdd EdExtValid
  edExtToAffine_x_lt edExtToAffine_y_lt edExtToAffine_fp_x edExtToAffine_fp_y
  edExtToAffine_edExtZero edExtValid_edExtZero edExtToAffine_edExtOfAffine
  edExtValid_edExtOfAffine edNatSmul edOnCurve_edNatSmul edNatSmul_two edNatSmul_mul)
/-! ## 1. Linear `.rodata` `AffineNiels` Table Extraction & Basepoint Table Checker -/

/-- Extract `rem` consecutive little-endian `u64` words from `bs`. -/
@[expose] def readWords64 : List (BitVec 8) → Nat → List (BitVec 64)
  | _, 0 => []
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, rem + 1 =>
    pack64 b0 b1 b2 b3 b4 b5 b6 b7 :: readWords64 rest rem
  | _, _ + 1 => []

/-- Group `rem` 5-word `FieldElement51` chunks into canonical residues modulo `p25519`. -/
@[expose] def fe51ValsFromWords : List (BitVec 64) → Nat → List Nat
  | _, 0 => []
  | w0 :: w1 :: w2 :: w3 :: w4 :: rest, rem + 1 =>
    (fe51Val w0 w1 w2 w3 w4 % p25519) :: fe51ValsFromWords rest rem
  | _, _ + 1 => []

/-- Group `rem` triples of `FieldElement51` values into `(y_plus_x, y_minus_x, xy2d)` tuples. -/
@[expose] def nielsFromVals : List Nat → Nat → List (Nat × Nat × Nat)
  | _, 0 => []
  | v0 :: v1 :: v2 :: rest, rem + 1 =>
    (v0, v1, v2) :: nielsFromVals rest rem
  | _, _ + 1 => []

/-- Extract `m` consecutive 120-byte `AffineNielsPoint` tuples modulo `p25519` from `bs`. -/
@[expose] def nielsFromBytes (bs : List (BitVec 8)) (m : Nat) : List (Nat × Nat × Nat) :=
  nielsFromVals (fe51ValsFromWords (readWords64 bs (15 * m)) (3 * m)) m

/-- Projective check (without `fpInv`) that `(ypx, ymx, xy2d)` are the canonical `AffineNiels`
    coordinates modulo `p25519` of extended point `P` with `P.Z % p25519 ≠ 0`. -/
@[expose] def checkNielsEntry (e : Nat × Nat × Nat) (P : EdExtPoint) : Bool :=
  let (ypx, ymx, xy2d) := e
  (P.Z % p25519 != 0) &&
  (fpMul ypx P.Z == fpAdd P.Y P.X) &&
  (fpMul ymx P.Z == fpSub P.Y P.X) &&
  (fpMul xy2d P.Z == fpMul edD2 P.T)

/-- Check `rem` consecutive entries of an 8-entry `LookupTable<AffineNielsPoint>` starting from
    accumulator `acc` (`[j] Bi`), advancing by `Bi` at each step. -/
@[expose] def checkTable8 : List (Nat × Nat × Nat) → EdExtPoint → EdExtPoint → Nat → Bool
  | _, _, _, 0 => true
  | e :: rest, Bi, acc, rem + 1 =>
    let acc' := edExtAdd acc Bi
    checkNielsEntry e acc' && checkTable8 rest Bi acc' rem
  | [], _, _, _ + 1 => false

/-- Check `rem` consecutive 8-entry basepoint tables starting at `Bi = [256^i] B`, advancing
    `Bi ↦ [256] Bi = edDouble4 (edDouble4 Bi)`. -/
@[expose] def checkBasepointTable32 : List (Nat × Nat × Nat) → EdExtPoint → Nat → Bool
  | _, _, 0 => true
  | entries, Bi, rem + 1 =>
    (entries.take 8).length == 8 &&
    checkTable8 (entries.take 8) Bi edExtZero 8 &&
    checkBasepointTable32 (entries.drop 8) (edDouble4 (edDouble4 Bi)) rem

theorem nielsFromBytes_ed25519BasepointTable_length :
    (nielsFromBytes ed25519BasepointTableBytes 256).length = 256 := by decide +kernel

theorem checkBasepointTable32_ed25519 :
    checkBasepointTable32 (nielsFromBytes ed25519BasepointTableBytes 256)
      (edExtOfAffine edBasepoint) 32 = true := by decide +kernel

attribute [local irreducible] fpInv fpPow recoverXEven

theorem getD_readWords64 {bs : List (BitVec 8)} {n k : Nat}
    (hlen : (readWords64 bs n).length = n) (hk : k < n) :
    (readWords64 bs n).getD k 0#64 = ByteSlice.readLE bs (8 * k) 8 := by
  induction n generalizing bs k with
  | zero => omega
  | succ n ih =>
    unfold readWords64 at hlen ⊢
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen
    rcases k with _ | k
    · simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.zero_add,
        ← ByteSlice.pack64_eq_readLE_8]
    · change (readWords64 rest n).getD k 0#64 = _
      rw [@ih rest k (by omega) (by omega), show 8 * (k + 1) = 8 * k + 8 by omega, readLE_cons8]

theorem fe51ValsFromWords_length_imp {ws : List (BitVec 64)} {n : Nat}
    (hlen : (fe51ValsFromWords ws n).length = n) :
    5 * n ≤ ws.length := by
  induction n generalizing ws with
  | zero => omega
  | succ n ih =>
    unfold fe51ValsFromWords at hlen
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, rest⟩⟩⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen ⊢
    have := @ih rest (by omega)
    omega

theorem getD_fe51ValsFromWords {ws : List (BitVec 64)} {n k : Nat}
    (hlen : (fe51ValsFromWords ws n).length = n) (hk : k < n) :
    (fe51ValsFromWords ws n).getD k 0 =
      fe51Val (ws.getD (5 * k) 0#64) (ws.getD (5 * k + 1) 0#64)
        (ws.getD (5 * k + 2) 0#64) (ws.getD (5 * k + 3) 0#64)
        (ws.getD (5 * k + 4) 0#64) % p25519 := by
  induction n generalizing ws k with
  | zero => omega
  | succ n ih =>
    unfold fe51ValsFromWords at hlen ⊢
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, rest⟩⟩⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen
    rcases k with _ | k
    · simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.zero_add]
    · change (fe51ValsFromWords rest n).getD k 0 = _
      rw [@ih rest k (by omega) (by omega), show 5 * (k + 1) = 5 * k + 5 by omega]
      simp only [List.getD_cons_succ]

theorem nielsFromVals_length_imp {vs : List Nat} {m : Nat}
    (hlen : (nielsFromVals vs m).length = m) :
    3 * m ≤ vs.length := by
  induction m generalizing vs with
  | zero => omega
  | succ m ih =>
    unfold nielsFromVals at hlen
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, rest⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen ⊢
    have := @ih rest (by omega)
    omega

theorem getD_nielsFromVals {vs : List Nat} {m k : Nat}
    (hlen : (nielsFromVals vs m).length = m) (hk : k < m) :
    (nielsFromVals vs m).getD k (0, 0, 0) =
      (vs.getD (3 * k) 0, vs.getD (3 * k + 1) 0, vs.getD (3 * k + 2) 0) := by
  induction m generalizing vs k with
  | zero => omega
  | succ m ih =>
    unfold nielsFromVals at hlen ⊢
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, rest⟩⟩⟩ <;>
      try (simp at hlen; done)
    simp only [List.length_cons] at hlen
    rcases k with _ | k
    · simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.zero_add]
    · change (nielsFromVals rest m).getD k (0, 0, 0) = _
      rw [@ih rest k (by omega) (by omega), show 3 * (k + 1) = 3 * k + 3 by omega]
      simp only [List.getD_cons_succ]

theorem readWords64_length_le (bs : List (BitVec 8)) (n : Nat) :
    (readWords64 bs n).length ≤ n := by
  induction n generalizing bs with
  | zero => simp [readWords64]
  | succ n ih =>
    unfold readWords64
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [List.length_nil, List.length_cons, Nat.zero_le]
    have := ih rest
    omega

theorem fe51ValsFromWords_length_le (ws : List (BitVec 64)) (n : Nat) :
    (fe51ValsFromWords ws n).length ≤ n := by
  induction n generalizing ws with
  | zero => simp [fe51ValsFromWords]
  | succ n ih =>
    unfold fe51ValsFromWords
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, rest⟩⟩⟩⟩⟩ <;>
      simp only [List.length_nil, List.length_cons, Nat.zero_le]
    have := ih rest
    omega

theorem getD_nielsFromBytes {bs : List (BitVec 8)} {m idx : Nat}
    (hlen : (nielsFromBytes bs m).length = m) (hidx : idx < m) :
    (nielsFromBytes bs m).getD idx (0, 0, 0) =
      (fe51ValAt bs (120 * idx) % p25519,
       fe51ValAt bs (120 * idx + 40) % p25519,
       fe51ValAt bs (120 * idx + 80) % p25519) := by
  unfold nielsFromBytes at hlen ⊢
  let ws := readWords64 bs (15 * m)
  let vs := fe51ValsFromWords ws (3 * m)
  have hvs_le : vs.length ≤ 3 * m := fe51ValsFromWords_length_le ws (3 * m)
  have hvs_ge : 3 * m ≤ vs.length := nielsFromVals_length_imp hlen
  have hvs_len : vs.length = 3 * m := by omega
  have hws_le : ws.length ≤ 15 * m := readWords64_length_le bs (15 * m)
  have hws_ge : 5 * (3 * m) ≤ ws.length := fe51ValsFromWords_length_imp hvs_len
  have hws_len : ws.length = 15 * m := by omega
  rw [getD_nielsFromVals hlen hidx]
  have hval (r : Nat) (hr : r < 3 * m) :
      vs.getD r 0 = fe51ValAt bs (40 * r) % p25519 := by
    rw [getD_fe51ValsFromWords hvs_len hr,
        getD_readWords64 hws_len (by omega),
        getD_readWords64 hws_len (by omega),
        getD_readWords64 hws_len (by omega),
        getD_readWords64 hws_len (by omega),
        getD_readWords64 hws_len (by omega)]
    unfold fe51ValAt
    rw [show 8 * (5 * r) = 40 * r by omega,
        show 8 * (5 * r + 1) = 40 * r + 8 by omega,
        show 8 * (5 * r + 2) = 40 * r + 16 by omega,
        show 8 * (5 * r + 3) = 40 * r + 24 by omega,
        show 8 * (5 * r + 4) = 40 * r + 32 by omega]
  rw [hval (3 * idx) (by omega), hval (3 * idx + 1) (by omega), hval (3 * idx + 2) (by omega),
      show 40 * (3 * idx) = 120 * idx by omega,
      show 40 * (3 * idx + 1) = 120 * idx + 40 by omega,
      show 40 * (3 * idx + 2) = 120 * idx + 80 by omega]

theorem fe51ValAt_slice_eq (bs : List (BitVec 8)) (base len off : Nat)
    (h : off + 40 ≤ len) :
    fe51ValAt (ProofLib.ByteSlice.slice bs base len) off = fe51ValAt bs (base + off) := by
  unfold fe51ValAt
  rw [readLE_slice_eq bs base len off (by rw [decide_eq_true_eq]; omega),
      readLE_slice_eq bs base len (off + 8) (by rw [decide_eq_true_eq]; omega),
      readLE_slice_eq bs base len (off + 16) (by rw [decide_eq_true_eq]; omega),
      readLE_slice_eq bs base len (off + 24) (by rw [decide_eq_true_eq]; omega),
      readLE_slice_eq bs base len (off + 32) (by rw [decide_eq_true_eq]; omega)]
  simp only [Nat.add_assoc]

/-! ## 2. Coordinate Models (`edExtNeg`, `EdProjValid`, `EdCompValid`, `edProjDouble`, `Niels`) -/

theorem edExtNeg_toAffine {P : EdExtPoint} (hP : EdExtValid P) :
    edExtToAffine (edExtNeg P) = edNeg (edExtToAffine P) := by
  have _ := hP
  ext
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_x_lt _) (fpNeg_lt _)
    rw [edExtToAffine_fp_x]
    unfold edExtNeg
    simp only [Fp.ofNat_fpNeg, Fp.ofNat_mod, edExtToAffine_fp_x]
    grind
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_y_lt _) (Nat.mod_lt _ p25519_pos)
    rw [edExtToAffine_fp_y]
    unfold edExtNeg
    simp only [Fp.ofNat_mod, edExtToAffine_fp_y]

theorem edExtValid_edExtNeg {P : EdExtPoint} (hP : EdExtValid P) :
    EdExtValid (edExtNeg P) where
  z_ne_zero := by
    unfold edExtNeg
    simp only [Fp.ofNat_mod]
    exact hP.z_ne_zero
  tz_eq_xy := by
    have htz := hP.tz_eq_xy
    unfold edExtNeg
    simp only [Fp.ofNat_fpNeg, Fp.ofNat_mod]
    grind
  on_curve := by
    rw [edExtNeg_toAffine hP]
    exact edOnCurve_edNeg hP.on_curve

/-- Projective point validity `(X : Y : Z)` (`T` ignored): `Z ≢ 0 (mod p)` and `(X/Z, Y/Z)` lies
    on the twisted Edwards curve. -/
structure EdProjValid (P : EdExtPoint) : Prop where
  z_ne_zero : Fp.ofNat P.Z ≠ 0
  on_curve : edOnCurve (edExtToAffine P) = true

theorem edProjValid_of_edExtValid {P : EdExtPoint} (hP : EdExtValid P) : EdProjValid P :=
  ⟨hP.z_ne_zero, hP.on_curve⟩

/-- Affine projection $(X Z^{-1} \bmod p, Y T^{-1} \bmod p)$ of a `CompletedPoint`
    $((X : Z), (Y : T)) \in \mathbb{P}^1 \times \mathbb{P}^1$. -/
@[expose] def edCompToAffine (C : EdExtPoint) : EdPoint :=
  ⟨fpMul C.X (fpInv C.Z), fpMul C.Y (fpInv C.T)⟩

/-- Validity invariant for a `CompletedPoint` $((X : Z), (Y : T))$: $Z \not\equiv 0$,
    $T \not\equiv 0$, and $(X Z^{-1}, Y T^{-1})$ lies on the curve. -/
structure EdCompValid (C : EdExtPoint) : Prop where
  z_ne_zero : Fp.ofNat C.Z ≠ 0
  t_ne_zero : Fp.ofNat C.T ≠ 0
  on_curve : edOnCurve (edCompToAffine C) = true

theorem edCompToAffine_x_lt (C : EdExtPoint) : (edCompToAffine C).x < p25519 := fpMul_lt _ _
theorem edCompToAffine_y_lt (C : EdExtPoint) : (edCompToAffine C).y < p25519 := fpMul_lt _ _

theorem edCompToAffine_fp_x (C : EdExtPoint) :
    Fp.ofNat (edCompToAffine C).x = Fp.ofNat C.X * (Fp.ofNat C.Z)⁻¹ := by
  unfold edCompToAffine; simp

theorem edCompToAffine_fp_y (C : EdExtPoint) :
    Fp.ofNat (edCompToAffine C).y = Fp.ofNat C.Y * (Fp.ofNat C.T)⁻¹ := by
  unfold edCompToAffine; simp

theorem edAsExtended_toAffine {C : EdExtPoint} (hC : EdCompValid C) :
    edExtToAffine (edAsExtended C) = edCompToAffine C := by
  have hZ := hC.z_ne_zero
  have hT := hC.t_ne_zero
  ext
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_x_lt _) (edCompToAffine_x_lt _)
    rw [edExtToAffine_fp_x, edCompToAffine_fp_x]
    unfold edAsExtended
    simp only [Fp.ofNat_fpMul]
    grind
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_y_lt _) (edCompToAffine_y_lt _)
    rw [edExtToAffine_fp_y, edCompToAffine_fp_y]
    unfold edAsExtended
    simp only [Fp.ofNat_fpMul]
    grind

theorem edExtValid_edAsExtended {C : EdExtPoint} (hC : EdCompValid C) :
    EdExtValid (edAsExtended C) where
  z_ne_zero := by
    unfold edAsExtended
    simp only [Fp.ofNat_fpMul]
    exact Fp.mul_ne_zero hC.z_ne_zero hC.t_ne_zero
  tz_eq_xy := by
    unfold edAsExtended
    simp only [Fp.ofNat_fpMul]
    grind
  on_curve := by
    rw [edAsExtended_toAffine hC]
    exact hC.on_curve

theorem edAsProjective_toAffine (C : EdExtPoint) :
    edExtToAffine (edAsProjective C) = edExtToAffine (edAsExtended C) := rfl

theorem edProjValid_edAsProjective {C : EdExtPoint} (hC : EdCompValid C) :
    EdProjValid (edAsProjective C) where
  z_ne_zero := (edExtValid_edAsExtended hC).z_ne_zero
  on_curve := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC]
    exact hC.on_curve

/-- Algebraic correctness of converting projective `(X, Y, Z)` into extended
    `(X*Z, Y*Z, Z^2, X*Y)` (`ProjectivePoint::as_extended`). -/
theorem edProjSqToExt_spec {P : EdExtPoint} (hP : EdProjValid P) :
    let E : EdExtPoint := ⟨fpMul P.X P.Z, fpMul P.Y P.Z, fpPow P.Z 2, fpMul P.X P.Y⟩
    EdExtValid E ∧ edExtToAffine E = edExtToAffine P := by
  intro E
  have hZ := hP.z_ne_zero
  have hpow : Fp.ofNat (fpPow P.Z 2) = Fp.ofNat P.Z * Fp.ofNat P.Z := by
    rw [fpPow_two_eq_fpSq, Fp.ofNat_fpSq]
  have haff : edExtToAffine E = edExtToAffine P := by
    ext
    · apply Fp.eq_of_ofNat_eq (edExtToAffine_x_lt _) (edExtToAffine_x_lt _)
      rw [edExtToAffine_fp_x, edExtToAffine_fp_x]
      dsimp only [E]
      rw [Fp.ofNat_fpMul, hpow]
      grind
    · apply Fp.eq_of_ofNat_eq (edExtToAffine_y_lt _) (edExtToAffine_y_lt _)
      rw [edExtToAffine_fp_y, edExtToAffine_fp_y]
      dsimp only [E]
      rw [Fp.ofNat_fpMul, hpow]
      grind
  refine ⟨⟨?_, ?_, ?_⟩, haff⟩
  · dsimp only [E]
    rw [hpow]
    exact Fp.mul_ne_zero hZ hZ
  · dsimp only [E]
    rw [Fp.ofNat_fpMul, Fp.ofNat_fpMul, Fp.ofNat_fpMul, hpow]
    grind
  · rw [haff]
    exact hP.on_curve

private theorem edProjDouble_zt_ring (d X Y Z x y : Fp)
    (hZ : Z ≠ 0) (hx : x = X * Z⁻¹) (hy : y = Y * Z⁻¹)
    (hcurve : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hdp : 1 + d * ((x * x) * (y * y)) ≠ 0)
    (hdm : 1 - d * ((x * x) * (y * y)) ≠ 0) :
    (Y * Y - X * X ≠ 0) ∧
    ((Z * Z + Z * Z) - (Y * Y - X * X) ≠ 0) ∧
    (((X + Y) * (X + Y) - (X * X + Y * Y)) * (Y * Y - X * X)⁻¹ =
      (x * y + y * x) * (1 + d * ((x * x) * (y * y)))⁻¹) ∧
    ((X * X + Y * Y) * ((Z * Z + Z * Z) - (Y * Y - X * X))⁻¹ =
      (y * y + x * x) * (1 - d * ((x * x) * (y * y)))⁻¹) := by
  have hZZ : Y * Y - X * X = Z * Z * (1 + d * ((x * x) * (y * y))) := by grind
  have hTT : (Z * Z + Z * Z) - (Y * Y - X * X) = Z * Z * (1 - d * ((x * x) * (y * y))) := by grind
  have hZ_ne : Y * Y - X * X ≠ 0 := by
    rw [hZZ]; exact Fp.mul_ne_zero (Fp.mul_ne_zero hZ hZ) hdp
  have hT_ne : (Z * Z + Z * Z) - (Y * Y - X * X) ≠ 0 := by
    rw [hTT]; exact Fp.mul_ne_zero (Fp.mul_ne_zero hZ hZ) hdm
  refine ⟨hZ_ne, hT_ne, ?_, ?_⟩ <;> grind

theorem edProjDouble_toAffine {P : EdExtPoint} (hP : EdProjValid P) :
    edCompToAffine (edProjDouble P.X P.Y P.Z) = edAdd (edExtToAffine P) (edExtToAffine P) := by
  have hcurve := edOnCurve_fp_eq hP.on_curve
  have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hP.on_curve
  have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hP.on_curve
  obtain ⟨_, _, hx_eq, hy_eq⟩ := edProjDouble_zt_ring
    (Fp.ofNat edD) (Fp.ofNat P.X) (Fp.ofNat P.Y) (Fp.ofNat P.Z)
    (Fp.ofNat (edExtToAffine P).x) (Fp.ofNat (edExtToAffine P).y)
    hP.z_ne_zero (edExtToAffine_fp_x P) (edExtToAffine_fp_y P) hcurve hdp hdm
  ext
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_x_lt _) (edAdd_x_lt _ _)
    rw [edCompToAffine_fp_x, edAdd_fp_x]
    unfold edProjDouble
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpSq, Fp.ofNat_mod]
    exact hx_eq
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_y_lt _) (edAdd_y_lt _ _)
    rw [edCompToAffine_fp_y, edAdd_fp_y]
    unfold edProjDouble
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpSq, Fp.ofNat_mod]
    exact hy_eq

theorem edCompValid_edProjDouble {P : EdExtPoint} (hP : EdProjValid P) :
    EdCompValid (edProjDouble P.X P.Y P.Z) where
  z_ne_zero := by
    have hcurve := edOnCurve_fp_eq hP.on_curve
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hP.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hP.on_curve
    unfold edProjDouble
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpSq, Fp.ofNat_mod]
    exact (edProjDouble_zt_ring _ _ _ _ _ _
      hP.z_ne_zero (edExtToAffine_fp_x P) (edExtToAffine_fp_y P) hcurve hdp hdm).1
  t_ne_zero := by
    have hcurve := edOnCurve_fp_eq hP.on_curve
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hP.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hP.on_curve
    unfold edProjDouble
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpSq, Fp.ofNat_mod]
    exact (edProjDouble_zt_ring _ _ _ _ _ _
      hP.z_ne_zero (edExtToAffine_fp_x P) (edExtToAffine_fp_y P) hcurve hdp hdm).2.1
  on_curve := by
    rw [edProjDouble_toAffine hP]
    exact edOnCurve_edAdd hP.on_curve hP.on_curve

theorem edDouble3_spec {P : EdExtPoint} (hP : EdExtValid P) :
    EdExtValid (edDouble3 P) ∧
    edExtToAffine (edDouble3 P) = edNatSmul 8 (edExtToAffine P) := by
  unfold edDouble3
  let C1 := edProjDouble P.X P.Y P.Z
  have hC1 : EdCompValid C1 := edCompValid_edProjDouble (edProjValid_of_edExtValid hP)
  let P1 := edAsProjective C1
  have hP1 : EdProjValid P1 := edProjValid_edAsProjective hC1
  let C2 := edProjDouble P1.X P1.Y P1.Z
  have hC2 : EdCompValid C2 := edCompValid_edProjDouble hP1
  let P2 := edAsProjective C2
  have hP2 : EdProjValid P2 := edProjValid_edAsProjective hC2
  let C3 := edProjDouble P2.X P2.Y P2.Z
  have hC3 : EdCompValid C3 := edCompValid_edProjDouble hP2
  refine ⟨edExtValid_edAsExtended hC3, ?_⟩
  have h1 : edExtToAffine P1 = edNatSmul 2 (edExtToAffine P) := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC1, edProjDouble_toAffine (edProjValid_of_edExtValid hP),
        edNatSmul_two hP.on_curve]
  have h2 : edExtToAffine P2 = edNatSmul 4 (edExtToAffine P) := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC2, edProjDouble_toAffine hP1, h1,
        ← edNatSmul_two (edOnCurve_edNatSmul 2 hP.on_curve),
        ← edNatSmul_mul 2 2 hP.on_curve]
  rw [edAsExtended_toAffine hC3, edProjDouble_toAffine hP2, h2,
      ← edNatSmul_two (edOnCurve_edNatSmul 4 hP.on_curve),
      ← edNatSmul_mul 2 4 hP.on_curve]

theorem edDouble4_spec {P : EdExtPoint} (hP : EdExtValid P) :
    EdExtValid (edDouble4 P) ∧
    edExtToAffine (edDouble4 P) = edNatSmul 16 (edExtToAffine P) := by
  unfold edDouble4
  let C1 := edProjDouble P.X P.Y P.Z
  have hC1 : EdCompValid C1 := edCompValid_edProjDouble (edProjValid_of_edExtValid hP)
  let P1 := edAsProjective C1
  have hP1 : EdProjValid P1 := edProjValid_edAsProjective hC1
  let C2 := edProjDouble P1.X P1.Y P1.Z
  have hC2 : EdCompValid C2 := edCompValid_edProjDouble hP1
  let P2 := edAsProjective C2
  have hP2 : EdProjValid P2 := edProjValid_edAsProjective hC2
  let C3 := edProjDouble P2.X P2.Y P2.Z
  have hC3 : EdCompValid C3 := edCompValid_edProjDouble hP2
  let P3 := edAsProjective C3
  have hP3 : EdProjValid P3 := edProjValid_edAsProjective hC3
  let C4 := edProjDouble P3.X P3.Y P3.Z
  have hC4 : EdCompValid C4 := edCompValid_edProjDouble hP3
  refine ⟨edExtValid_edAsExtended hC4, ?_⟩
  have h1 : edExtToAffine P1 = edNatSmul 2 (edExtToAffine P) := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC1, edProjDouble_toAffine (edProjValid_of_edExtValid hP),
        edNatSmul_two hP.on_curve]
  have h2 : edExtToAffine P2 = edNatSmul 4 (edExtToAffine P) := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC2, edProjDouble_toAffine hP1, h1,
        ← edNatSmul_two (edOnCurve_edNatSmul 2 hP.on_curve),
        ← edNatSmul_mul 2 2 hP.on_curve]
  have h3 : edExtToAffine P3 = edNatSmul 8 (edExtToAffine P) := by
    rw [edAsProjective_toAffine, edAsExtended_toAffine hC3, edProjDouble_toAffine hP2, h2,
        ← edNatSmul_two (edOnCurve_edNatSmul 4 hP.on_curve),
        ← edNatSmul_mul 2 4 hP.on_curve]
  rw [edAsExtended_toAffine hC4, edProjDouble_toAffine hP3, h3,
      ← edNatSmul_two (edOnCurve_edNatSmul 8 hP.on_curve),
      ← edNatSmul_mul 2 8 hP.on_curve]

theorem edPointEq_eq_beq_toAffine {P Q : EdExtPoint}
    (hP : EdExtValid P) (hQ : EdExtValid Q) :
    edPointEq P Q = (edExtToAffine P == edExtToAffine Q) := by
  have hPZ := hP.z_ne_zero
  have hQZ := hQ.z_ne_zero
  have hx_iff : fpMul P.X Q.Z = fpMul Q.X P.Z ↔ (edExtToAffine P).x = (edExtToAffine Q).x := by
    constructor
    · intro h
      apply Fp.eq_of_ofNat_eq (edExtToAffine_x_lt _) (edExtToAffine_x_lt _)
      have hfp := congrArg Fp.ofNat h
      simp only [Fp.ofNat_fpMul] at hfp
      rw [edExtToAffine_fp_x, edExtToAffine_fp_x]
      grind
    · intro h
      apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) (fpMul_lt _ _)
      have hfp := congrArg Fp.ofNat h
      rw [edExtToAffine_fp_x, edExtToAffine_fp_x] at hfp
      simp only [Fp.ofNat_fpMul]
      grind
  have hy_iff : fpMul P.Y Q.Z = fpMul Q.Y P.Z ↔ (edExtToAffine P).y = (edExtToAffine Q).y := by
    constructor
    · intro h
      apply Fp.eq_of_ofNat_eq (edExtToAffine_y_lt _) (edExtToAffine_y_lt _)
      have hfp := congrArg Fp.ofNat h
      simp only [Fp.ofNat_fpMul] at hfp
      rw [edExtToAffine_fp_y, edExtToAffine_fp_y]
      grind
    · intro h
      apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) (fpMul_lt _ _)
      have hfp := congrArg Fp.ofNat h
      rw [edExtToAffine_fp_y, edExtToAffine_fp_y] at hfp
      simp only [Fp.ofNat_fpMul]
      grind
  unfold edPointEq
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, hx_iff, hy_iff]
  exact ⟨fun ⟨hx, hy⟩ => by ext <;> assumption, fun h => ⟨congrArg EdPoint.x h, congrArg EdPoint.y h⟩⟩

/-! ## 3. `AffineNiels` & `ProjectiveNiels` Point Addition and Subtraction -/

/-- `AffineNielsPoint` `(ypx, ymx, xy2d)` represents curve point `Q = (x, y)` over `Fp`. -/
structure EdAffineNielsValid (ypx ymx xy2d : Nat) (Q : EdPoint) : Prop where
  on_curve : edOnCurve Q = true
  ypx_eq : Fp.ofNat ypx = Fp.ofNat Q.y + Fp.ofNat Q.x
  ymx_eq : Fp.ofNat ymx = Fp.ofNat Q.y - Fp.ofNat Q.x
  xy2d_eq : Fp.ofNat xy2d = 2 * Fp.ofNat edD * Fp.ofNat Q.x * Fp.ofNat Q.y

theorem edAffineNielsValid_edZero : EdAffineNielsValid 1 1 0 edZero where
  on_curve := edOnCurve_edZero
  ypx_eq := by simp [edZero]; grind
  ymx_eq := by simp [edZero]; grind
  xy2d_eq := by simp [edZero]; grind

theorem edAffineNielsValid_neg {ypx ymx xy2d : Nat} {Q : EdPoint}
    (h : EdAffineNielsValid ypx ymx xy2d Q) :
    EdAffineNielsValid ymx ypx (fpNeg xy2d) (edNeg Q) where
  on_curve := edOnCurve_edNeg h.on_curve
  ypx_eq := by rw [h.ymx_eq]; simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]; grind
  ymx_eq := by rw [h.ypx_eq]; simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]; grind
  xy2d_eq := by rw [Fp.ofNat_fpNeg, h.xy2d_eq]; simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]; grind

private theorem edAddAffineNiels_ring (d X1 Y1 Z1 T1 x1 y1 x2 y2 ypx ymx xy2d : Fp)
    (h2 : (2 : Fp) ≠ 0) (hZ1 : Z1 ≠ 0) (hT1 : T1 * Z1 = X1 * Y1)
    (hx1 : x1 = X1 * Z1⁻¹) (hy1 : y1 = Y1 * Z1⁻¹)
    (hypx : ypx = y2 + x2) (hymx : ymx = y2 - x2) (hxy2d : xy2d = 2 * d * x2 * y2)
    (hdp : 1 + d * ((x1 * x2) * (y1 * y2)) ≠ 0)
    (hdm : 1 - d * ((x1 * x2) * (y1 * y2)) ≠ 0) :
    let PP := (X1 + Y1) * ypx
    let MM := (Y1 - X1) * ymx
    let TT2d := T1 * xy2d
    let ZZ2 := Z1 + Z1
    (TT2d + ZZ2 ≠ 0) ∧
    (ZZ2 - TT2d ≠ 0) ∧
    ((PP - MM) * (TT2d + ZZ2)⁻¹ = (x1 * y2 + y1 * x2) * (1 + d * ((x1 * x2) * (y1 * y2)))⁻¹) ∧
    ((MM + PP) * (ZZ2 - TT2d)⁻¹ = (y1 * y2 + x1 * x2) * (1 - d * ((x1 * x2) * (y1 * y2)))⁻¹) := by
  have hZ : T1 * xy2d + (Z1 + Z1) = 2 * Z1 * (1 + d * ((x1 * x2) * (y1 * y2))) := by grind
  have hT : (Z1 + Z1) - T1 * xy2d = 2 * Z1 * (1 - d * ((x1 * x2) * (y1 * y2))) := by grind
  have hZ_ne : T1 * xy2d + (Z1 + Z1) ≠ 0 := by
    rw [hZ]; exact Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hdp
  have hT_ne : (Z1 + Z1) - T1 * xy2d ≠ 0 := by
    rw [hT]; exact Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hdm
  refine ⟨hZ_ne, hT_ne, ?_, ?_⟩ <;> grind

theorem edAddAffineNiels_toAffine {P : EdExtPoint} {ypx ymx xy2d : Nat} {Q : EdPoint}
    (hP : EdExtValid P) (hQ : EdAffineNielsValid ypx ymx xy2d Q) :
    edCompToAffine (edAddAffineNiels P ypx ymx xy2d) = edAdd (edExtToAffine P) Q := by
  have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
  have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
  obtain ⟨_, _, hx_eq, hy_eq⟩ := edAddAffineNiels_ring
    (Fp.ofNat edD) (Fp.ofNat P.X) (Fp.ofNat P.Y) (Fp.ofNat P.Z) (Fp.ofNat P.T)
    (Fp.ofNat (edExtToAffine P).x) (Fp.ofNat (edExtToAffine P).y)
    (Fp.ofNat Q.x) (Fp.ofNat Q.y) (Fp.ofNat ypx) (Fp.ofNat ymx) (Fp.ofNat xy2d)
    Fp.two_ne_zero hP.z_ne_zero hP.tz_eq_xy
    (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
    hQ.ypx_eq hQ.ymx_eq hQ.xy2d_eq hdp hdm
  ext
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_x_lt _) (edAdd_x_lt _ _)
    rw [edCompToAffine_fp_x, edAdd_fp_x]
    unfold edAddAffineNiels
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact hx_eq
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_y_lt _) (edAdd_y_lt _ _)
    rw [edCompToAffine_fp_y, edAdd_fp_y]
    unfold edAddAffineNiels
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact hy_eq

theorem edCompValid_edAddAffineNiels {P : EdExtPoint} {ypx ymx xy2d : Nat} {Q : EdPoint}
    (hP : EdExtValid P) (hQ : EdAffineNielsValid ypx ymx xy2d Q) :
    EdCompValid (edAddAffineNiels P ypx ymx xy2d) where
  z_ne_zero := by
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
    unfold edAddAffineNiels
    simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact (edAddAffineNiels_ring _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hP.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      hQ.ypx_eq hQ.ymx_eq hQ.xy2d_eq hdp hdm).1
  t_ne_zero := by
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
    unfold edAddAffineNiels
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact (edAddAffineNiels_ring _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hP.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      hQ.ypx_eq hQ.ymx_eq hQ.xy2d_eq hdp hdm).2.1
  on_curve := by
    rw [edAddAffineNiels_toAffine hP hQ]
    exact edOnCurve_edAdd hP.on_curve hQ.on_curve

theorem edSubAffineNiels_eq_edAddAffineNiels_neg (P : EdExtPoint) (ypx ymx xy2d : Nat) :
    edSubAffineNiels P ypx ymx xy2d = edAddAffineNiels P ymx ypx (fpNeg xy2d) := by
  dsimp only [edSubAffineNiels, edAddAffineNiels]
  congr 1
  · apply Fp.eq_of_ofNat_eq (fpSub_lt _ _) (fpAdd_lt _ _)
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpNeg]
    grind
  · apply Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (fpSub_lt _ _)
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpNeg]
    grind

theorem edSubAffineNiels_toAffine {P : EdExtPoint} {ypx ymx xy2d : Nat} {Q : EdPoint}
    (hP : EdExtValid P) (hQ : EdAffineNielsValid ypx ymx xy2d Q) :
    edCompToAffine (edSubAffineNiels P ypx ymx xy2d) = edSub (edExtToAffine P) Q := by
  rw [edSubAffineNiels_eq_edAddAffineNiels_neg, edAddAffineNiels_toAffine hP (edAffineNielsValid_neg hQ)]
  rfl

theorem edCompValid_edSubAffineNiels {P : EdExtPoint} {ypx ymx xy2d : Nat} {Q : EdPoint}
    (hP : EdExtValid P) (hQ : EdAffineNielsValid ypx ymx xy2d Q) :
    EdCompValid (edSubAffineNiels P ypx ymx xy2d) := by
  rw [edSubAffineNiels_eq_edAddAffineNiels_neg]
  exact edCompValid_edAddAffineNiels hP (edAffineNielsValid_neg hQ)

/-- `ProjectiveNielsPoint` `N = (Y_plus_X, Y_minus_X, Z, T2d)` represents curve point `Q` over `Fp`. -/
structure EdProjNielsValid (N : EdExtPoint) (Q : EdPoint) : Prop where
  on_curve : edOnCurve Q = true
  z_ne_zero : Fp.ofNat N.Z ≠ 0
  ypx_eq : Fp.ofNat N.X = Fp.ofNat N.Z * (Fp.ofNat Q.y + Fp.ofNat Q.x)
  ymx_eq : Fp.ofNat N.Y = Fp.ofNat N.Z * (Fp.ofNat Q.y - Fp.ofNat Q.x)
  t2d_eq : Fp.ofNat N.T = 2 * Fp.ofNat edD * Fp.ofNat N.Z * Fp.ofNat Q.x * Fp.ofNat Q.y

theorem edProjNielsValid_neg {N : EdExtPoint} {Q : EdPoint} (h : EdProjNielsValid N Q) :
    EdProjNielsValid ⟨N.Y, N.X, N.Z, fpNeg N.T⟩ (edNeg Q) where
  on_curve := edOnCurve_edNeg h.on_curve
  z_ne_zero := h.z_ne_zero
  ypx_eq := by dsimp only; rw [h.ymx_eq]; simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]; grind
  ymx_eq := by dsimp only; rw [h.ypx_eq]; simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]; grind
  t2d_eq := by dsimp only; rw [Fp.ofNat_fpNeg, h.t2d_eq]; simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]; grind

private theorem edAddProjNiels_ring (d X1 Y1 Z1 T1 x1 y1 x2 y2 NX NY NZ NT : Fp)
    (h2 : (2 : Fp) ≠ 0) (hZ1 : Z1 ≠ 0) (hNZ : NZ ≠ 0) (hT1 : T1 * Z1 = X1 * Y1)
    (hx1 : x1 = X1 * Z1⁻¹) (hy1 : y1 = Y1 * Z1⁻¹)
    (hypx : NX = NZ * (y2 + x2)) (hymx : NY = NZ * (y2 - x2))
    (ht2d : NT = 2 * d * NZ * x2 * y2)
    (hdp : 1 + d * ((x1 * x2) * (y1 * y2)) ≠ 0)
    (hdm : 1 - d * ((x1 * x2) * (y1 * y2)) ≠ 0) :
    let PP := (X1 + Y1) * NX
    let MM := (Y1 - X1) * NY
    let TT2d := T1 * NT
    let ZZ2 := Z1 * NZ + Z1 * NZ
    (TT2d + ZZ2 ≠ 0) ∧
    (ZZ2 - TT2d ≠ 0) ∧
    ((PP - MM) * (TT2d + ZZ2)⁻¹ = (x1 * y2 + y1 * x2) * (1 + d * ((x1 * x2) * (y1 * y2)))⁻¹) ∧
    ((MM + PP) * (ZZ2 - TT2d)⁻¹ = (y1 * y2 + x1 * x2) * (1 - d * ((x1 * x2) * (y1 * y2)))⁻¹) := by
  have hZ : T1 * NT + (Z1 * NZ + Z1 * NZ) = 2 * Z1 * NZ * (1 + d * ((x1 * x2) * (y1 * y2))) := by grind
  have hT : (Z1 * NZ + Z1 * NZ) - T1 * NT = 2 * Z1 * NZ * (1 - d * ((x1 * x2) * (y1 * y2))) := by grind
  have hZ_ne : T1 * NT + (Z1 * NZ + Z1 * NZ) ≠ 0 := by
    rw [hZ]; exact Fp.mul_ne_zero (Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hNZ) hdp
  have hT_ne : (Z1 * NZ + Z1 * NZ) - T1 * NT ≠ 0 := by
    rw [hT]; exact Fp.mul_ne_zero (Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hNZ) hdm
  refine ⟨hZ_ne, hT_ne, ?_, ?_⟩ <;> grind

theorem edAddProjNiels_toAffine {P N : EdExtPoint} {Q : EdPoint}
    (hP : EdExtValid P) (hN : EdProjNielsValid N Q) :
    edCompToAffine (edAddProjNiels P N) = edAdd (edExtToAffine P) Q := by
  have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hN.on_curve
  have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hN.on_curve
  obtain ⟨_, _, hx_eq, hy_eq⟩ := edAddProjNiels_ring
    (Fp.ofNat edD) (Fp.ofNat P.X) (Fp.ofNat P.Y) (Fp.ofNat P.Z) (Fp.ofNat P.T)
    (Fp.ofNat (edExtToAffine P).x) (Fp.ofNat (edExtToAffine P).y)
    (Fp.ofNat Q.x) (Fp.ofNat Q.y)
    (Fp.ofNat N.X) (Fp.ofNat N.Y) (Fp.ofNat N.Z) (Fp.ofNat N.T)
    Fp.two_ne_zero hP.z_ne_zero hN.z_ne_zero hP.tz_eq_xy
    (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
    hN.ypx_eq hN.ymx_eq hN.t2d_eq hdp hdm
  ext
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_x_lt _) (edAdd_x_lt _ _)
    rw [edCompToAffine_fp_x, edAdd_fp_x]
    unfold edAddProjNiels
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact hx_eq
  · apply Fp.eq_of_ofNat_eq (edCompToAffine_y_lt _) (edAdd_y_lt _ _)
    rw [edCompToAffine_fp_y, edAdd_fp_y]
    unfold edAddProjNiels
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact hy_eq

theorem edCompValid_edAddProjNiels {P N : EdExtPoint} {Q : EdPoint}
    (hP : EdExtValid P) (hN : EdProjNielsValid N Q) :
    EdCompValid (edAddProjNiels P N) where
  z_ne_zero := by
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hN.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hN.on_curve
    unfold edAddProjNiels
    simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact (edAddProjNiels_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hN.z_ne_zero hP.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      hN.ypx_eq hN.ymx_eq hN.t2d_eq hdp hdm).1
  t_ne_zero := by
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hN.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hN.on_curve
    unfold edAddProjNiels
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul]
    exact (edAddProjNiels_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hN.z_ne_zero hP.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      hN.ypx_eq hN.ymx_eq hN.t2d_eq hdp hdm).2.1
  on_curve := by
    rw [edAddProjNiels_toAffine hP hN]
    exact edOnCurve_edAdd hP.on_curve hN.on_curve

theorem edSubProjNiels_eq_edAddProjNiels_neg (P N : EdExtPoint) :
    edSubProjNiels P N = edAddProjNiels P ⟨N.Y, N.X, N.Z, fpNeg N.T⟩ := by
  dsimp only [edSubProjNiels, edAddProjNiels]
  congr 1
  · apply Fp.eq_of_ofNat_eq (fpSub_lt _ _) (fpAdd_lt _ _)
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpNeg]
    grind
  · apply Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (fpSub_lt _ _)
    simp only [Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpNeg]
    grind

theorem edSubProjNiels_toAffine {P N : EdExtPoint} {Q : EdPoint}
    (hP : EdExtValid P) (hN : EdProjNielsValid N Q) :
    edCompToAffine (edSubProjNiels P N) = edSub (edExtToAffine P) Q := by
  rw [edSubProjNiels_eq_edAddProjNiels_neg, edAddProjNiels_toAffine hP (edProjNielsValid_neg hN)]
  rfl

theorem edCompValid_edSubProjNiels {P N : EdExtPoint} {Q : EdPoint}
    (hP : EdExtValid P) (hN : EdProjNielsValid N Q) :
    EdCompValid (edSubProjNiels P N) := by
  rw [edSubProjNiels_eq_edAddProjNiels_neg]
  exact edCompValid_edAddProjNiels hP (edProjNielsValid_neg hN)

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1

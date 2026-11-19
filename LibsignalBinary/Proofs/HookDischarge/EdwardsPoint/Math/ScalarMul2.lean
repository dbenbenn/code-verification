/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1 -- proof-setup: allow-public-import

/-!
# Signed Scalar Multiplication & Radix-16 Basepoint Bridge, Part 2 (`LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul2`)

Pure `0-sorry` mathematical bridge proofs for `edIntSmul`, `ed25519BasepointTableBytes` soundness,
`scalarRadix16Digits`, and `edMulBase` equivalence to `edSmul`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul2

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib
open VerifiedLibraries.Common (
  p25519 fpNeg fpPow fpInv EdPoint EdExtPoint edZero edExtZero edExtToAffine edBasepoint
  edOnCurve edExtAdd edAdd edNeg edSub edSmul leBytesToNat encodeEd recoverXEven
  clampScalarBytes clampScalar)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  ed25519BasepointTableBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  scalarRadix16Digits scalarRadix16Digits_length)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51ValAt edAddAffineNiels edAsExtended edDouble4 edTableEntryAt edSelectAffineNiels
  edMulBaseStep edMulBaseStepAt edMulBaseLoopWith edMulBaseLoop edMulBase)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  Fp edOnCurve_edBasepoint edOnCurve_edNeg edAdd_comm edAdd_edZero edZero_edAdd edNeg_edNeg
  edNeg_edAdd edAdd_assoc edAdd_edSub_cancel EdExtValid edExtToAffine_fp_x edExtToAffine_fp_y
  edExtToAffine_edExtZero edExtValid_edExtZero edExtToAffine_edExtOfAffine
  edExtValid_edExtOfAffine edExtAdd_toAffine edExtValid_edExtAdd edNatSmul edNatSmul_succ
  edOnCurve_edNatSmul edNatSmul_one edNatSmul_add edNatSmul_mul edSmul_eq_edNatSmul)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  leBytesToNat_cons leBytesToNat_lt)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1 (
  checkNielsEntry checkTable8 checkBasepointTable32 nielsFromBytes_ed25519BasepointTable_length
  checkBasepointTable32_ed25519 getD_nielsFromBytes fe51ValAt_slice_eq edCompToAffine
  EdCompValid edAsExtended_toAffine edExtValid_edAsExtended edDouble4_spec EdAffineNielsValid
  edAffineNielsValid_edZero edAffineNielsValid_neg edAddAffineNiels_toAffine
  edCompValid_edAddAffineNiels)
attribute [local irreducible] fpInv fpPow recoverXEven

/-! ## 4. Signed Integer Scalar Multiplication (`edIntSmul`) & Table Selection -/

/-- Signed integer scalar multiplication $[z]P$ on affine twisted Edwards points. -/
@[expose] def edIntSmul (z : Int) (P : EdPoint) : EdPoint :=
  if z ≥ 0 then edNatSmul z.toNat P
  else edNeg (edNatSmul (-z).toNat P)

theorem edOnCurve_edIntSmul (z : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edOnCurve (edIntSmul z P) = true := by
  unfold edIntSmul
  split
  · exact edOnCurve_edNatSmul _ hP
  · exact edOnCurve_edNeg (edOnCurve_edNatSmul _ hP)

@[simp] theorem edIntSmul_zero (P : EdPoint) : edIntSmul 0 P = edZero := rfl

@[simp] theorem edIntSmul_ofNat (n : Nat) (P : EdPoint) :
    edIntSmul (Int.ofNat n) P = edNatSmul n P := by
  unfold edIntSmul
  have h : Int.ofNat n ≥ 0 := by change (n : Int) ≥ 0; omega
  have ht : (Int.ofNat n).toNat = n := rfl
  simp only [h, ↓reduceIte, ht]

@[simp] private theorem edIntSmul_natCast (n : Nat) (P : EdPoint) :
    edIntSmul (n : Int) P = edNatSmul n P :=
  edIntSmul_ofNat n P

theorem edNatSmul_edNeg (n : Nat) (P : EdPoint) :
    edNatSmul n (edNeg P) = edNeg (edNatSmul n P) := by
  induction n with
  | zero => simp
  | succ k ih => rw [edNatSmul_succ, edNatSmul_succ, ih, edNeg_edAdd]

theorem edIntSmul_neg (z : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edIntSmul (-z) P = edNeg (edIntSmul z P) := by
  unfold edIntSmul
  rcases Int.lt_trichotomy z 0 with hlt | rfl | hgt
  · have h1 : -z ≥ 0 := by omega
    have h2 : ¬(z ≥ 0) := by omega
    simp only [h1, h2, ↓reduceIte]
    rw [edNeg_edNeg (edOnCurve_edNatSmul _ hP)]
  · simp
  · have h1 : ¬(-z ≥ 0) := by omega
    have h2 : z ≥ 0 := by omega
    simp only [h1, h2, ↓reduceIte, Int.neg_neg]

theorem edIntSmul_edNeg (z : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edIntSmul z (edNeg P) = edNeg (edIntSmul z P) := by
  unfold edIntSmul
  split
  · exact edNatSmul_edNeg _ P
  · rw [edNatSmul_edNeg, edNeg_edNeg (edOnCurve_edNatSmul _ hP)]

theorem edNatSmul_sub {m n : Nat} (h : n ≤ m) {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul (m - n) P = edAdd (edNatSmul m P) (edNeg (edNatSmul n P)) := by
  have hm : m = (m - n) + n := by omega
  conv => rhs; arg 1; rw [hm]
  rw [edNatSmul_add (m - n) n hP]
  exact (edAdd_edSub_cancel (edOnCurve_edNatSmul (m - n) hP) (edOnCurve_edNatSmul n hP)).symm

theorem edIntSmul_add (a b : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edIntSmul (a + b) P = edAdd (edIntSmul a P) (edIntSmul b P) := by
  by_cases ha : a ≥ 0
  · by_cases hb : b ≥ 0
    · have hab : a + b ≥ 0 := by omega
      unfold edIntSmul
      simp only [ha, hb, hab, ↓reduceIte]
      rw [show (a + b).toNat = a.toNat + b.toNat by omega, edNatSmul_add _ _ hP]
    · by_cases hab : a + b ≥ 0
      · unfold edIntSmul
        simp only [ha, hb, hab, ↓reduceIte]
        have hle : (-b).toNat ≤ a.toNat := by omega
        rw [show (a + b).toNat = a.toNat - (-b).toNat by omega]
        exact edNatSmul_sub hle hP
      · unfold edIntSmul
        simp only [ha, hb, hab, ↓reduceIte]
        have hle : a.toNat ≤ (-b).toNat := by omega
        rw [show (-(a + b)).toNat = (-b).toNat - a.toNat by omega,
            edNatSmul_sub hle hP, edNeg_edAdd,
            edNeg_edNeg (edOnCurve_edNatSmul _ hP), edAdd_comm]
  · by_cases hb : b ≥ 0
    · by_cases hab : a + b ≥ 0
      · unfold edIntSmul
        simp only [ha, hb, hab, ↓reduceIte]
        have hle : (-a).toNat ≤ b.toNat := by omega
        rw [show (a + b).toNat = b.toNat - (-a).toNat by omega,
            edNatSmul_sub hle hP, edAdd_comm]
      · unfold edIntSmul
        simp only [ha, hb, hab, ↓reduceIte]
        have hle : b.toNat ≤ (-a).toNat := by omega
        rw [show (-(a + b)).toNat = (-a).toNat - b.toNat by omega,
            edNatSmul_sub hle hP, edNeg_edAdd,
            edNeg_edNeg (edOnCurve_edNatSmul _ hP)]
    · have hab : ¬(a + b ≥ 0) := by omega
      unfold edIntSmul
      simp only [ha, hb, hab, ↓reduceIte]
      rw [show (-(a + b)).toNat = (-a).toNat + (-b).toNat by omega,
          edNatSmul_add _ _ hP, edNeg_edAdd]

theorem edIntSmul_sub (a b : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edIntSmul (a - b) P = edSub (edIntSmul a P) (edIntSmul b P) := by
  rw [Int.sub_eq_add_neg, edIntSmul_add a (-b) hP, edIntSmul_neg b hP]
  rfl

theorem edIntSmul_mul (a b : Int) {P : EdPoint} (hP : edOnCurve P = true) :
    edIntSmul (a * b) P = edIntSmul a (edIntSmul b P) := by
  by_cases ha : a ≥ 0
  · obtain ⟨m, rfl⟩ : ∃ m : Nat, a = (m : Int) := ⟨a.toNat, by omega⟩
    by_cases hb : b ≥ 0
    · obtain ⟨n, rfl⟩ : ∃ n : Nat, b = (n : Int) := ⟨b.toNat, by omega⟩
      rw [← Int.natCast_mul, edIntSmul_natCast, edIntSmul_natCast, edIntSmul_natCast,
          edNatSmul_mul _ _ hP]
    · obtain ⟨n, hn⟩ : ∃ n : Nat, b = -(n : Int) := ⟨(-b).toNat, by omega⟩
      rw [hn, Int.mul_neg, edIntSmul_neg _ hP, edIntSmul_neg _ hP,
          edIntSmul_edNeg _ (edOnCurve_edIntSmul _ hP),
          ← Int.natCast_mul, edIntSmul_natCast, edIntSmul_natCast, edIntSmul_natCast,
          edNatSmul_mul _ _ hP]
  · obtain ⟨m, hm⟩ : ∃ m : Nat, a = -(m : Int) := ⟨(-a).toNat, by omega⟩
    rw [hm, Int.neg_mul, edIntSmul_neg _ hP, edIntSmul_neg _ (edOnCurve_edIntSmul _ hP)]
    by_cases hb : b ≥ 0
    · obtain ⟨n, rfl⟩ : ∃ n : Nat, b = (n : Int) := ⟨b.toNat, by omega⟩
      rw [← Int.natCast_mul, edIntSmul_natCast, edIntSmul_natCast, edIntSmul_natCast,
          edNatSmul_mul _ _ hP]
    · obtain ⟨n, hn⟩ : ∃ n : Nat, b = -(n : Int) := ⟨(-b).toNat, by omega⟩
      rw [hn, Int.mul_neg, edIntSmul_neg _ hP, edIntSmul_neg _ hP,
          edIntSmul_edNeg _ (edOnCurve_edIntSmul _ hP),
          ← Int.natCast_mul, edIntSmul_natCast, edIntSmul_natCast, edIntSmul_natCast,
          edNatSmul_mul _ _ hP]

private theorem bv8_signed_radix16_cases :
    ∀ x : BitVec 8, (-8 ≤ x.toInt ∧ x.toInt ≤ 8) →
      (x = 0#8 ∨
       x = 1#8 ∨ x = 2#8 ∨ x = 3#8 ∨ x = 4#8 ∨ x = 5#8 ∨ x = 6#8 ∨ x = 7#8 ∨ x = 8#8 ∨
       x = -1#8 ∨ x = -2#8 ∨ x = -3#8 ∨ x = -4#8 ∨ x = -5#8 ∨ x = -6#8 ∨ x = -7#8 ∨ x = -8#8) := by
  decide

private def selectRaw {α : Type} (f : Nat → α) (zero : α) (x : BitVec 8) : α :=
  if x == 8#8 || x == -8#8 then f 7 else if x == 7#8 || x == -7#8 then f 6
  else if x == 6#8 || x == -6#8 then f 5 else if x == 5#8 || x == -5#8 then f 4
  else if x == 4#8 || x == -4#8 then f 3 else if x == 3#8 || x == -3#8 then f 2
  else if x == 2#8 || x == -2#8 then f 1 else if x == 1#8 || x == -1#8 then f 0
  else zero

private theorem edSelectAffineNiels_eq_selectRaw (slice : List (BitVec 8)) (d : BitVec 8) :
    edSelectAffineNiels slice d =
      let e := selectRaw (edTableEntryAt slice) (1, 1, 0) d
      if d.msb then (e.2.1, e.1, fpNeg e.2.2) else e := by
  change (let (ypx, ymx, xy2d) := selectRaw (edTableEntryAt slice) (1, 1, 0) d
          if d.msb then (ymx, ypx, fpNeg xy2d) else (ypx, ymx, xy2d)) = _
  rcases selectRaw (edTableEntryAt slice) (1, 1, 0) d with ⟨ypx, ymx, xy2d⟩
  rfl

private theorem edSelect_pos_case {slice : List (BitVec 8)} {Q : EdPoint}
    (x : BitVec 8) (j : Nat)
    (hmsb : x.msb = false) (hto : x.toInt = Int.ofNat (j + 1))
    (hraw : ∀ {α : Type} (f : Nat → α) (z : α), selectRaw f z x = f j)
    (hj : let e := edTableEntryAt slice j; EdAffineNielsValid e.1 e.2.1 e.2.2 (edNatSmul (j + 1) Q)) :
    let e := edSelectAffineNiels slice x
    EdAffineNielsValid e.1 e.2.1 e.2.2 (edIntSmul x.toInt Q) := by
  dsimp only
  rw [edSelectAffineNiels_eq_selectRaw]
  dsimp only
  rw [hmsb, hraw, hto, edIntSmul_ofNat]
  simpa only [Bool.false_eq_true, ↓reduceIte] using hj

private theorem edSelect_neg_case {slice : List (BitVec 8)} {Q : EdPoint}
    (x : BitVec 8) (j : Nat)
    (hmsb : x.msb = true) (hneg : ¬(x.toInt ≥ 0)) (habs : (-x.toInt).toNat = j + 1)
    (hraw : ∀ {α : Type} (f : Nat → α) (z : α), selectRaw f z x = f j)
    (hj : let e := edTableEntryAt slice j; EdAffineNielsValid e.1 e.2.1 e.2.2 (edNatSmul (j + 1) Q)) :
    let e := edSelectAffineNiels slice x
    EdAffineNielsValid e.1 e.2.1 e.2.2 (edIntSmul x.toInt Q) := by
  dsimp only
  rw [edSelectAffineNiels_eq_selectRaw]
  dsimp only
  rw [hmsb, hraw]
  have hint : edIntSmul x.toInt Q = edNeg (edNatSmul (j + 1) Q) := by
    unfold edIntSmul; simp only [hneg, ↓reduceIte, habs]
  rw [hint]
  simpa only [↓reduceIte] using edAffineNielsValid_neg hj

private theorem edSelectAffineNiels_valid_proj {slice : List (BitVec 8)} {Q : EdPoint} {d : BitVec 8}
    (htab : ∀ j < 8,
      let (ypx, ymx, xy2d) := edTableEntryAt slice j
      EdAffineNielsValid ypx ymx xy2d (edNatSmul (j + 1) Q))
    (hd : -8 ≤ d.toInt ∧ d.toInt ≤ 8) :
    let e := edSelectAffineNiels slice d
    EdAffineNielsValid e.1 e.2.1 e.2.2 (edIntSmul d.toInt Q) := by
  have htab' : ∀ j < 8,
      let e := edTableEntryAt slice j
      EdAffineNielsValid e.1 e.2.1 e.2.2 (edNatSmul (j + 1) Q) := by
    intro j hj
    have h := htab j hj
    dsimp only
    generalize edTableEntryAt slice j = e at h ⊢
    rcases e with ⟨ypx, ymx, xy2d⟩
    exact h
  have h0 := htab' 0 (by decide)
  have h1 := htab' 1 (by decide)
  have h2 := htab' 2 (by decide)
  have h3 := htab' 3 (by decide)
  have h4 := htab' 4 (by decide)
  have h5 := htab' 5 (by decide)
  have h6 := htab' 6 (by decide)
  have h7 := htab' 7 (by decide)
  rcases bv8_signed_radix16_cases d hd with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only
    rw [edSelectAffineNiels_eq_selectRaw]
    dsimp only
    have hraw0 : ∀ {α : Type} (f : Nat → α) (z : α), selectRaw f z 0#8 = z := fun _ _ => rfl
    rw [show (0#8).msb = false by decide, hraw0,
        show (0#8).toInt = 0 by decide, edIntSmul_zero]
    simpa only [Bool.false_eq_true, ↓reduceIte] using edAffineNielsValid_edZero
  · exact edSelect_pos_case 1#8 0 (by decide) (by decide) (fun _ _ => rfl) h0
  · exact edSelect_pos_case 2#8 1 (by decide) (by decide) (fun _ _ => rfl) h1
  · exact edSelect_pos_case 3#8 2 (by decide) (by decide) (fun _ _ => rfl) h2
  · exact edSelect_pos_case 4#8 3 (by decide) (by decide) (fun _ _ => rfl) h3
  · exact edSelect_pos_case 5#8 4 (by decide) (by decide) (fun _ _ => rfl) h4
  · exact edSelect_pos_case 6#8 5 (by decide) (by decide) (fun _ _ => rfl) h5
  · exact edSelect_pos_case 7#8 6 (by decide) (by decide) (fun _ _ => rfl) h6
  · exact edSelect_pos_case 8#8 7 (by decide) (by decide) (fun _ _ => rfl) h7
  · exact edSelect_neg_case (-1#8) 0 (by decide) (by decide) (by decide) (fun _ _ => rfl) h0
  · exact edSelect_neg_case (-2#8) 1 (by decide) (by decide) (by decide) (fun _ _ => rfl) h1
  · exact edSelect_neg_case (-3#8) 2 (by decide) (by decide) (by decide) (fun _ _ => rfl) h2
  · exact edSelect_neg_case (-4#8) 3 (by decide) (by decide) (by decide) (fun _ _ => rfl) h3
  · exact edSelect_neg_case (-5#8) 4 (by decide) (by decide) (by decide) (fun _ _ => rfl) h4
  · exact edSelect_neg_case (-6#8) 5 (by decide) (by decide) (by decide) (fun _ _ => rfl) h5
  · exact edSelect_neg_case (-7#8) 6 (by decide) (by decide) (by decide) (fun _ _ => rfl) h6
  · exact edSelect_neg_case (-8#8) 7 (by decide) (by decide) (by decide) (fun _ _ => rfl) h7

theorem edSelectAffineNiels_valid {slice : List (BitVec 8)} {Q : EdPoint} {d : BitVec 8}
    (htab : ∀ j < 8,
      let (ypx, ymx, xy2d) := edTableEntryAt slice j
      EdAffineNielsValid ypx ymx xy2d (edNatSmul (j + 1) Q))
    (hd : -8 ≤ d.toInt ∧ d.toInt ≤ 8) :
    let (ypx, ymx, xy2d) := edSelectAffineNiels slice d
    EdAffineNielsValid ypx ymx xy2d (edIntSmul d.toInt Q) := by
  have h := edSelectAffineNiels_valid_proj htab hd
  dsimp only at h
  generalize edSelectAffineNiels slice d = e at h ⊢
  rcases e with ⟨ypx, ymx, xy2d⟩
  exact h

/-! ## 5. Soundness of `checkNielsEntry` & `ed25519BasepointTableBytes` Entries -/

theorem edAffineNielsValid_of_checkNielsEntry {e : Nat × Nat × Nat} {P : EdExtPoint}
    (hP : EdExtValid P) (hchk : checkNielsEntry e P = true) :
    EdAffineNielsValid e.1 e.2.1 e.2.2 (edExtToAffine P) := by
  rcases e with ⟨ypx, ymx, xy2d⟩
  unfold checkNielsEntry at hchk
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨_, hypx⟩, hymx⟩, hxy2d⟩
  have hZ := hP.z_ne_zero
  have hTZ := hP.tz_eq_xy
  have h1 := congrArg Fp.ofNat hypx
  have h2 := congrArg Fp.ofNat hymx
  have h3 := congrArg Fp.ofNat hxy2d
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_edD2] at h1 h2 h3
  refine ⟨hP.on_curve, ?_, ?_, ?_⟩
  · rw [edExtToAffine_fp_x, edExtToAffine_fp_y]; grind
  · rw [edExtToAffine_fp_x, edExtToAffine_fp_y]; grind
  · rw [edExtToAffine_fp_x, edExtToAffine_fp_y]; grind

theorem of_checkTable8 {entries : List (Nat × Nat × Nat)} {Bi acc : EdExtPoint} {rem j : Nat}
    (hBi : EdExtValid Bi) (hacc : EdExtValid acc)
    (hchk : checkTable8 entries Bi acc rem = true)
    (hlen : entries.length = rem) (hj : j < rem) :
    let e := entries.getD j (0, 0, 0)
    EdAffineNielsValid e.1 e.2.1 e.2.2
      (edAdd (edExtToAffine acc) (edNatSmul (j + 1) (edExtToAffine Bi))) := by
  induction rem generalizing entries acc j with
  | zero => omega
  | succ rem ih =>
    rcases entries with _ | ⟨e0, rest⟩
    · simp at hlen
    unfold checkTable8 at hchk
    simp only [Bool.and_eq_true] at hchk
    have hacc' : EdExtValid (edExtAdd acc Bi) := edExtValid_edExtAdd hacc hBi
    rcases j with _ | j
    · simp only [List.getD_cons_zero, Nat.zero_add, edNatSmul_one hBi.on_curve,
        ← edExtAdd_toAffine hacc hBi]
      exact edAffineNielsValid_of_checkNielsEntry hacc' hchk.1
    · simp only [List.getD_cons_succ]
      have hsub := @ih rest (edExtAdd acc Bi) j hacc' hchk.2 (by simp at hlen; omega) (by omega)
      rw [edExtAdd_toAffine hacc hBi,
          edAdd_assoc hacc.on_curve hBi.on_curve (edOnCurve_edNatSmul (j + 1) hBi.on_curve),
          ← edNatSmul_succ] at hsub
      exact hsub

theorem of_checkBasepointTable32 {entries : List (Nat × Nat × Nat)} {Bi : EdExtPoint}
    {rem t j : Nat}
    (hBi : EdExtValid Bi)
    (hchk : checkBasepointTable32 entries Bi rem = true)
    (hlen : entries.length = 8 * rem)
    (ht : t < rem) (hj : j < 8) :
    let e := entries.getD (8 * t + j) (0, 0, 0)
    EdAffineNielsValid e.1 e.2.1 e.2.2
      (edNatSmul (j + 1) (edNatSmul (256 ^ t) (edExtToAffine Bi))) := by
  induction rem generalizing entries Bi t with
  | zero => omega
  | succ rem ih =>
    unfold checkBasepointTable32 at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    rcases hchk with ⟨⟨htake_len, htab8⟩, hrest⟩
    rcases t with _ | t
    · have hget : entries.getD j (0, 0, 0) = (entries.take 8).getD j (0, 0, 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
      simp only [Nat.mul_zero, Nat.zero_add, Nat.pow_zero, edNatSmul_one hBi.on_curve]
      rw [hget]
      have h0 := of_checkTable8 hBi edExtValid_edExtZero htab8 htake_len hj
      rwa [edExtToAffine_edExtZero, edZero_edAdd (edOnCurve_edNatSmul (j + 1) hBi.on_curve)] at h0
    · obtain ⟨hD4_1_valid, hD4_1_aff⟩ := edDouble4_spec hBi
      obtain ⟨hD4_2_valid, hD4_2_aff⟩ := edDouble4_spec hD4_1_valid
      have hdrop_len : (entries.drop 8).length = 8 * rem := by
        rw [List.length_drop]; omega
      have hget : entries.getD (8 * (t + 1) + j) (0, 0, 0) =
          (entries.drop 8).getD (8 * t + j) (0, 0, 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
            show 8 + (8 * t + j) = 8 * (t + 1) + j by omega]
      rw [hget]
      have hsub := @ih (entries.drop 8) (edDouble4 (edDouble4 Bi)) t hD4_2_valid hrest hdrop_len (by omega)
      rw [hD4_2_aff, hD4_1_aff, ← edNatSmul_mul 16 16 hBi.on_curve,
          show 16 * 16 = 256 by decide,
          ← edNatSmul_mul (256 ^ t) 256 hBi.on_curve,
          ← Nat.pow_succ] at hsub
      exact hsub

theorem ed25519BasepointTable_entry_valid {i j : Nat} (hi : i < 32) (hj : j < 8) :
    let (ypx, ymx, xy2d) := edTableEntryAt
      (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960) j
    EdAffineNielsValid ypx ymx xy2d
      (edNatSmul (j + 1) (edNatSmul (256 ^ i) edBasepoint)) := by
  have hchk := of_checkBasepointTable32
    (edExtValid_edExtOfAffine edOnCurve_edBasepoint)
    checkBasepointTable32_ed25519
    nielsFromBytes_ed25519BasepointTable_length hi hj
  rw [edExtToAffine_edExtOfAffine edOnCurve_edBasepoint] at hchk
  rw [getD_nielsFromBytes nielsFromBytes_ed25519BasepointTable_length (by omega)] at hchk
  have hentry :
      edTableEntryAt (ProofLib.ByteSlice.slice ed25519BasepointTableBytes (960 * i) 960) j =
      (fe51ValAt ed25519BasepointTableBytes (120 * (8 * i + j)) % p25519,
       fe51ValAt ed25519BasepointTableBytes (120 * (8 * i + j) + 40) % p25519,
       fe51ValAt ed25519BasepointTableBytes (120 * (8 * i + j) + 80) % p25519) := by
    unfold edTableEntryAt
    rw [fe51ValAt_slice_eq _ _ _ _ (by omega),
        fe51ValAt_slice_eq _ _ _ _ (by omega),
        fe51ValAt_slice_eq _ _ _ _ (by omega),
        show 960 * i + 120 * j = 120 * (8 * i + j) by omega,
        show 960 * i + (120 * j + 40) = 120 * (8 * i + j) + 40 by omega,
        show 960 * i + (120 * j + 80) = 120 * (8 * i + j) + 80 by omega]
  rw [hentry]
  exact hchk

/-! ## 6. Signed Radix-16 Recoding (`scalarRadix16Digits`) Value & Digit Bounds -/

/-- Unsigned nibble at index `i` (`0 ≤ i < 64`) of a little-endian byte list `a_bs`. -/
@[expose] def radix16NibbleAt (a_bs : List (BitVec 8)) (i : Nat) : BitVec 8 :=
  if i % 2 == 0 then a_bs.getD (i / 2) 0#8 &&& 15#8 else a_bs.getD (i / 2) 0#8 >>> 4

/-- Nibbles `[63 - k, ..., 63]` of `a_bs`. -/
@[expose] def radix16NibblesFrom (a_bs : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => []
  | k + 1 => radix16NibbleAt a_bs (63 - k) :: radix16NibblesFrom a_bs k

/-- Recentering pass turning `(d, bs)` into signed radix-16 digits in `[-8, 8]`. -/
@[expose] def recenterRadix16 (d : Nat) : List (BitVec 8) → List (BitVec 8)
  | [] => [BitVec.ofNat 8 d]
  | b :: bs =>
    BitVec.ofInt 8 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16) ::
      recenterRadix16 (b.toNat + (d + 8) / 16) bs

/-- Unsigned radix-16 value $d + 16 \sum_j b_j 16^j$ of `(d, bs)`. -/
@[expose] def nibbleListVal (d : Nat) : List (BitVec 8) → Nat
  | [] => d
  | b :: bs => d + 16 * nibbleListVal b.toNat bs

/-- Signed radix-16 polynomial value $\sum_j d_j 16^j$ of `digits`. -/
@[expose] def signedRadix16Val : List (BitVec 8) → Int
  | [] => 0
  | x :: xs => x.toInt + 16 * signedRadix16Val xs

/-- All nibbles in `bs` are `< 16`, and if `bs` is non-empty its last nibble is `≤ 7`
    (otherwise `d ≤ 8`). -/
@[expose] def ValidNibbleTail : Nat → List (BitVec 8) → Prop
  | d, [] => d ≤ 8
  | d, b :: [] => d ≤ 16 ∧ b.toNat ≤ 7
  | d, b :: b2 :: bs => d ≤ 16 ∧ b.toNat < 16 ∧ ValidNibbleTail b.toNat (b2 :: bs)

private theorem radix16NibbleAt_lt (a_bs : List (BitVec 8)) (i : Nat) :
    (radix16NibbleAt a_bs i).toNat < 16 := by
  have h := (by decide : ∀ b : BitVec 8, (b &&& 15#8).toNat < 16 ∧ (b >>> 4).toNat < 16)
    (a_bs.getD (i / 2) 0#8)
  unfold radix16NibbleAt
  split <;> simp only [h.1, h.2]

private theorem radix16NibbleAt_63_le_7 {a_bs : List (BitVec 8)}
    (hb31 : (a_bs.getD 31 0#8).toNat ≤ 127) :
    (radix16NibbleAt a_bs 63).toNat ≤ 7 := by
  unfold radix16NibbleAt
  simp only [show (63 % 2 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte,
    show 63 / 2 = 31 by decide, BitVec.toNat_ushiftRight]
  have : (a_bs.getD 31 0#8).toNat >>> 4 = (a_bs.getD 31 0#8).toNat / 16 :=
    Nat.shiftRight_eq_div_pow _ 4
  omega

private theorem radix16NibbleAt_int_eq (a_bs : List (BitVec 8)) (i : Nat) :
    (if i % 2 == 0 then Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat &&& 0x0f)
     else Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat >>> 4)) =
    Int.ofNat (radix16NibbleAt a_bs i).toNat := by
  unfold radix16NibbleAt
  split <;> simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat] <;> rfl

private theorem scalarRadix16Digits_go_eq_recenter (a_bs : List (BitVec 8)) :
    ∀ (k : Nat) (_hk : k ≤ 63) (carry : Nat) (acc : List (BitVec 8)),
      scalarRadix16Digits.go a_bs (k + 1) (Int.ofNat carry) acc =
        acc.reverse ++ recenterRadix16 ((radix16NibbleAt a_bs (63 - k)).toNat + carry)
          (radix16NibblesFrom a_bs k) := by
  intro k
  induction k with
  | zero =>
    intro _ carry acc
    rw [scalarRadix16Digits.go, radix16NibbleAt_int_eq]
    change scalarRadix16Digits.go a_bs 0 0
      (BitVec.ofNat 8 ((radix16NibbleAt a_bs 63).toNat + carry) :: acc) = _
    rw [scalarRadix16Digits.go]
    simp [radix16NibblesFrom, recenterRadix16]
  | succ m ih =>
    intro hk carry acc
    rw [scalarRadix16Digits.go, radix16NibbleAt_int_eq]
    have hm : 63 - (m + 1) < 63 := by omega
    let dNat := (radix16NibbleAt a_bs (63 - (m + 1))).toNat + carry
    change (if 63 - (m + 1) < 63 then
        scalarRadix16Digits.go a_bs (m + 1) (Int.ofNat ((dNat + 8) / 16))
          (BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16) :: acc)
      else
        scalarRadix16Digits.go a_bs (m + 1) 0 (BitVec.ofInt 8 (Int.ofNat dNat) :: acc)) = _
    simp only [hm, ↓reduceIte]
    rw [ih (by omega) ((dNat + 8) / 16)]
    simp [radix16NibblesFrom, recenterRadix16, dNat]

theorem scalarRadix16Digits_eq_recenter (a_bs : List (BitVec 8)) :
    scalarRadix16Digits a_bs =
      recenterRadix16 (radix16NibbleAt a_bs 0).toNat (radix16NibblesFrom a_bs 63) := by
  unfold scalarRadix16Digits
  simpa using scalarRadix16Digits_go_eq_recenter a_bs 63 (by omega) 0 []

private theorem ofInt8_recenter_props {d : Nat} (hd : d ≤ 16) :
    let r : Int := Int.ofNat d - (Int.ofNat d + 8) / 16 * 16
    (BitVec.ofInt 8 r).toInt = r ∧ -8 ≤ r ∧ r ≤ 8 ∧ (d + 8) / 16 ≤ 1 ∧
    r + 16 * Int.ofNat ((d + 8) / 16) = Int.ofNat d := by
  have hfin : ∀ k : Fin 17,
      let d := k.val
      let r : Int := Int.ofNat d - (Int.ofNat d + 8) / 16 * 16
      (BitVec.ofInt 8 r).toInt = r ∧ -8 ≤ r ∧ r ≤ 8 ∧ (d + 8) / 16 ≤ 1 ∧
      r + 16 * Int.ofNat ((d + 8) / 16) = Int.ofNat d := by decide
  exact hfin ⟨d, by omega⟩

private theorem ofNat8_le8_props {d : Nat} (hd : d ≤ 8) :
    (BitVec.ofNat 8 d).toInt = Int.ofNat d ∧
    -8 ≤ (BitVec.ofNat 8 d).toInt ∧ (BitVec.ofNat 8 d).toInt ≤ 8 := by
  have hfin : ∀ k : Fin 9,
      (BitVec.ofNat 8 k.val).toInt = Int.ofNat k.val ∧
      -8 ≤ (BitVec.ofNat 8 k.val).toInt ∧ (BitVec.ofNat 8 k.val).toInt ≤ 8 := by decide
  exact hfin ⟨d, by omega⟩

theorem recenterRadix16_spec (d : Nat) (bs : List (BitVec 8))
    (hv : ValidNibbleTail d bs) :
    (∀ x ∈ recenterRadix16 d bs, -8 ≤ x.toInt ∧ x.toInt ≤ 8) ∧
    signedRadix16Val (recenterRadix16 d bs) = Int.ofNat (nibbleListVal d bs) := by
  induction bs generalizing d with
  | nil =>
    have hd : d ≤ 8 := hv
    obtain ⟨hto, hlo, hhi⟩ := ofNat8_le8_props hd
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [recenterRadix16, List.mem_singleton] at hx
      subst hx
      exact ⟨hlo, hhi⟩
    · simp only [recenterRadix16, signedRadix16Val, nibbleListVal, hto, Int.mul_zero, Int.add_zero]
  | cons b rest ih =>
    have hv' : d ≤ 16 ∧ ValidNibbleTail (b.toNat + (d + 8) / 16) rest := by
      rcases rest with _ | ⟨b2, rest'⟩
      · rcases hv with ⟨hd, hb⟩
        have hc : (d + 8) / 16 ≤ 1 := by omega
        exact ⟨hd, by unfold ValidNibbleTail; omega⟩
      · rcases hv with ⟨hd, hb, htail⟩
        have hc : (d + 8) / 16 ≤ 1 := by omega
        rcases rest' with _ | ⟨b3, rest''⟩
        · exact ⟨hd, by omega, htail.2⟩
        · exact ⟨hd, by omega, htail.2.1, htail.2.2⟩
    obtain ⟨hto, hlo, hhi, _, heq_d⟩ := ofInt8_recenter_props hv'.1
    obtain ⟨hmem_ih, hval_ih⟩ := ih (b.toNat + (d + 8) / 16) hv'.2
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [recenterRadix16, List.mem_cons] at hx
      rcases hx with rfl | hx_tl
      · rw [hto]; exact ⟨hlo, hhi⟩
      · exact hmem_ih x hx_tl
    · simp only [recenterRadix16, signedRadix16Val, nibbleListVal, hto, hval_ih]
      rcases rest with _ | ⟨b2, rest'⟩ <;>
        simp only [nibbleListVal, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul] at heq_d ⊢ <;>
        omega

private theorem validNibbleTail_nibblesFrom {a_bs : List (BitVec 8)}
    (hb31 : (a_bs.getD 31 0#8).toNat ≤ 127) :
    ∀ (k : Nat) (_hk : 1 ≤ k) (_hle : k ≤ 63) (d : Nat) (_hd : d ≤ 16),
      ValidNibbleTail d (radix16NibblesFrom a_bs k) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ m ih =>
    intro _ hle d hd
    rcases m with _ | m'
    · exact ⟨hd, radix16NibbleAt_63_le_7 hb31⟩
    · simp only [radix16NibblesFrom]
      exact ⟨hd, radix16NibbleAt_lt a_bs _, ih (by omega) (by omega) _ (Nat.le_of_lt (radix16NibbleAt_lt a_bs _))⟩

private theorem byte_split_nibbles (b : BitVec 8) :
    (b &&& 15#8).toNat + 16 * (b >>> 4).toNat = b.toNat := by
  revert b; decide

private theorem nibblePair_val (a_bs : List (BitVec 8)) :
    ∀ k : Nat, k ≤ 31 →
      nibbleListVal (radix16NibbleAt a_bs (62 - 2 * k)).toNat
        (radix16NibblesFrom a_bs (2 * k + 1)) =
      (List.range (k + 1)).foldr (fun idx acc => acc * 256 + (a_bs.getD (31 - k + idx) 0#8).toNat) 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.zero_add, Nat.add_zero, Nat.zero_mul,
      radix16NibblesFrom, nibbleListVal, List.range_one, List.foldr_cons, List.foldr_nil]
    unfold radix16NibbleAt
    simp only [show (62 % 2 == 0) = true by decide, show (63 % 2 == 0) = false by decide,
      Bool.false_eq_true, ↓reduceIte, show 62 / 2 = 31 by decide]
    exact byte_split_nibbles (a_bs.getD 31 0#8)
  | succ m ih =>
    intro hm
    have hstep : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [hstep, radix16NibblesFrom, radix16NibblesFrom, nibbleListVal, nibbleListVal]
    have hi2 : 63 - (2 * m + 1) = 62 - 2 * m := by omega
    rw [hi2, ih (by omega)]
    have heven : ((62 - 2 * (m + 1)) % 2 == 0) = true := by simp only [beq_iff_eq]; omega
    have hodd : ¬((63 - ((2 * m + 1) + 1)) % 2 == 0) := by simp only [beq_iff_eq]; omega
    have hdiv1 : (62 - 2 * (m + 1)) / 2 = 31 - (m + 1) := by omega
    have hdiv2 : (63 - ((2 * m + 1) + 1)) / 2 = 31 - (m + 1) := by omega
    have hlo : (radix16NibbleAt a_bs (62 - 2 * (m + 1))).toNat =
        (a_bs.getD (31 - (m + 1)) 0#8 &&& 15#8).toNat := by
      unfold radix16NibbleAt; simp only [heven, ↓reduceIte, hdiv1]
    have hhi : (radix16NibbleAt a_bs (63 - ((2 * m + 1) + 1))).toNat =
        (a_bs.getD (31 - (m + 1)) 0#8 >>> 4).toNat := by
      unfold radix16NibbleAt; simp only [hodd, hdiv2]; rfl
    rw [hlo, hhi]
    have hpair := byte_split_nibbles (a_bs.getD (31 - (m + 1)) 0#8)
    have hrange : List.range (m + 1 + 1) = 0 :: (List.range (m + 1)).map Nat.succ :=
      List.range_succ_eq_map
    rw [hrange, List.foldr_cons, List.foldr_map]
    simp only [Nat.add_zero]
    have hshift :
        (List.range (m + 1)).foldr (fun x acc => acc * 256 + (a_bs.getD (31 - (m + 1) + x.succ) 0#8).toNat) 0 =
        (List.range (m + 1)).foldr (fun idx acc => acc * 256 + (a_bs.getD (31 - m + idx) 0#8).toNat) 0 := by
      congr 1; funext idx acc; rw [show 31 - (m + 1) + idx.succ = 31 - m + idx by omega]
    rw [hshift]
    omega

private theorem foldr_range_getD_eq_leBytesToNat :
    ∀ (bs : List (BitVec 8)) (n : Nat), bs.length = n →
      (List.range n).foldr (fun idx acc => acc * 256 + (bs.getD idx 0#8).toNat) 0 =
        leBytesToNat bs := by
  intro bs
  induction bs with
  | nil =>
    intro n hn; subst hn; rfl
  | cons b rest ih =>
    intro n hn; subst hn
    simp only [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map,
      List.getD_cons_zero, List.getD_cons_succ, leBytesToNat_cons]
    rw [ih rest.length rfl]

theorem scalarRadix16Digits_spec {scalar_bs : List (BitVec 8)}
    (hlen : scalar_bs.length = 32)
    (hb31 : (scalar_bs.getD 31 0#8).toNat ≤ 127) :
    (∀ k < 64,
      let d := (scalarRadix16Digits scalar_bs).getD k 0#8;
      -8 ≤ d.toInt ∧ d.toInt ≤ 8) ∧
    signedRadix16Val (scalarRadix16Digits scalar_bs) = Int.ofNat (leBytesToNat scalar_bs) := by
  have hv : ValidNibbleTail (radix16NibbleAt scalar_bs 0).toNat (radix16NibblesFrom scalar_bs 63) :=
    validNibbleTail_nibblesFrom hb31 63 (by decide) (by decide) _
      (Nat.le_of_lt (radix16NibbleAt_lt scalar_bs 0))
  obtain ⟨hmem, hval⟩ := recenterRadix16_spec _ _ hv
  rw [← scalarRadix16Digits_eq_recenter] at hmem hval
  have hlen64 : (scalarRadix16Digits scalar_bs).length = 64 := scalarRadix16Digits_length scalar_bs
  refine ⟨?_, ?_⟩
  · intro k hk
    have hk_lt : k < (scalarRadix16Digits scalar_bs).length := by omega
    have hget : (scalarRadix16Digits scalar_bs).getD k 0#8 = (scalarRadix16Digits scalar_bs)[k]'hk_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]; rfl
    rw [hget]
    exact hmem _ (List.getElem_mem hk_lt)
  · rw [hval]
    have hp := nibblePair_val scalar_bs 31 (by decide)
    simp only [show 62 - 2 * 31 = 0 by decide, show 2 * 31 + 1 = 63 by decide,
      show 31 + 1 = 32 by decide, Nat.zero_add] at hp
    rw [hp, foldr_range_getD_eq_leBytesToNat scalar_bs 32 hlen]

/-! ## 7. `edMulBase` Equivalence to `edSmul` & Point Compression Corollary -/

/-- Weighted digit sum $\sum_{r=0}^{\text{rem}-1} d_{2(i+r)+\text{parity}} \cdot 256^{i+r}$. -/
@[expose] def radix256DigitSum (digits : List (BitVec 8)) (parity : Nat) : Nat → Nat → Int
  | _, 0 => 0
  | i, rem + 1 =>
    (digits.getD (2 * i + parity) 0#8).toInt * (256 : Int) ^ i +
      radix256DigitSum digits parity (i + 1) rem

private theorem edMulBaseStepAt_eq (table_bs digits : List (BitVec 8)) (parity i : Nat) (acc : EdExtPoint) :
    edMulBaseStepAt table_bs digits parity i acc =
      let sel := edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960)
        (digits.getD (2 * i + parity) 0#8)
      edAsExtended (edAddAffineNiels acc sel.1 sel.2.1 sel.2.2) := by
  unfold edMulBaseStepAt edMulBaseStep
  rcases edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960)
    (digits.getD (2 * i + parity) 0#8) with ⟨ypx, ymx, xy2d⟩
  rfl
attribute [local irreducible] edAdd edSub edBasepoint edSmul encodeEd
  edExtToAffine edCompToAffine edSelectAffineNiels edAddAffineNiels edAsExtended edDouble4

private theorem int_pow_256_eq_ofNat (i : Nat) :
    ((256 : Int) ^ i) = Int.ofNat (256 ^ i) := by
  rw [Int.ofNat_eq_natCast, Int.natCast_pow]; rfl

private theorem edMulBaseStepAt_spec (table_bs digits : List (BitVec 8)) (parity i : Nat)
    (acc : EdExtPoint) {Q : EdPoint} (hQ : edOnCurve Q = true)
    (htab : ∀ j < 8,
      let (ypx, ymx, xy2d) := edTableEntryAt
        (ProofLib.ByteSlice.slice table_bs (960 * i) 960) j
      EdAffineNielsValid ypx ymx xy2d
        (edNatSmul (j + 1) (edNatSmul (256 ^ i) Q)))
    (hd : -8 ≤ (digits.getD (2 * i + parity) 0#8).toInt ∧
          (digits.getD (2 * i + parity) 0#8).toInt ≤ 8)
    (hacc : EdExtValid acc) :
    EdExtValid (edMulBaseStepAt table_bs digits parity i acc) ∧
    edExtToAffine (edMulBaseStepAt table_bs digits parity i acc) =
      edAdd (edExtToAffine acc)
        (edIntSmul ((digits.getD (2 * i + parity) 0#8).toInt * (256 : Int) ^ i) Q) := by
  have hsel := edSelectAffineNiels_valid_proj htab hd
  rw [edMulBaseStepAt_eq]
  dsimp only
  generalize edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960)
    (digits.getD (2 * i + parity) 0#8) = sel at hsel ⊢
  have hcomp_valid : EdCompValid (edAddAffineNiels acc sel.1 sel.2.1 sel.2.2) :=
    edCompValid_edAddAffineNiels hacc hsel
  refine ⟨edExtValid_edAsExtended hcomp_valid, ?_⟩
  rw [edAsExtended_toAffine hcomp_valid, edAddAffineNiels_toAffine hacc hsel,
      edIntSmul_mul _ ((256 : Int) ^ i) hQ,
      int_pow_256_eq_ofNat i, edIntSmul_ofNat]

private theorem edMulBase_aff_step {P Q : EdPoint} (a b : Int)
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    edAdd (edAdd P (edIntSmul a Q)) (edIntSmul b Q) =
      edAdd P (edIntSmul (a + b) Q) := by
  rw [edIntSmul_add a b hQ,
      edAdd_assoc hP (edOnCurve_edIntSmul a hQ)
        (edOnCurve_edIntSmul b hQ)]

private theorem edMulBaseLoopWith_zero_fast {α : Type} (step : Nat → α → α) (i : Nat) (acc : α) :
    edMulBaseLoopWith step i 0 acc = acc := rfl

private theorem edMulBaseLoopWith_step_fast {α : Type} (step : Nat → α → α) (i rem : Nat) (acc : α) :
    edMulBaseLoopWith step i (rem + 1) acc = edMulBaseLoopWith step (i + 1) rem (step i acc) := rfl

private theorem edMulBaseLoop_zero_fast (table_bs digits : List (BitVec 8)) (parity i : Nat) (acc : EdExtPoint) :
    edMulBaseLoop table_bs digits parity i 0 acc = acc :=
  edMulBaseLoopWith_zero_fast (edMulBaseStepAt table_bs digits parity) i acc

private theorem edMulBaseLoop_step_fast (table_bs digits : List (BitVec 8)) (parity i rem : Nat) (acc : EdExtPoint) :
    edMulBaseLoop table_bs digits parity i (rem + 1) acc =
      edMulBaseLoop table_bs digits parity (i + 1) rem (edMulBaseStepAt table_bs digits parity i acc) :=
  edMulBaseLoopWith_step_fast (edMulBaseStepAt table_bs digits parity) i rem acc

attribute [local irreducible] edMulBaseLoop edMulBaseStepAt

private theorem edMulBaseLoop_spec_gen (table_bs : List (BitVec 8))
    {Q : EdPoint} (hQ : edOnCurve Q = true)
    (htable : ∀ i < 32, ∀ j < 8,
      let (ypx, ymx, xy2d) := edTableEntryAt
        (ProofLib.ByteSlice.slice table_bs (960 * i) 960) j
      EdAffineNielsValid ypx ymx xy2d
        (edNatSmul (j + 1) (edNatSmul (256 ^ i) Q)))
    {digits : List (BitVec 8)} (parity : Nat)
    (hdigits : ∀ k < 64, -8 ≤ (digits.getD k 0#8).toInt ∧ (digits.getD k 0#8).toInt ≤ 8)
    (hparity : parity ≤ 1) :
    ∀ (rem i : Nat) (acc : EdExtPoint),
      i + rem ≤ 32 →
      EdExtValid acc →
      EdExtValid (edMulBaseLoop table_bs digits parity i rem acc) ∧
      edExtToAffine (edMulBaseLoop table_bs digits parity i rem acc) =
        edAdd (edExtToAffine acc)
          (edIntSmul (radix256DigitSum digits parity i rem) Q)
  | 0, i, acc, _, hacc => by
    rw [edMulBaseLoop_zero_fast, radix256DigitSum, edIntSmul_zero, edAdd_edZero hacc.on_curve]
    exact ⟨hacc, rfl⟩
  | rem + 1, i, acc, hrem, hacc => by
    have hi : i < 32 := by omega
    have hk : 2 * i + parity < 64 := by omega
    obtain ⟨hacc'_valid, hacc'_aff⟩ := edMulBaseStepAt_spec table_bs digits parity i acc hQ
      (fun j hj => htable i hi j hj) (hdigits (2 * i + parity) hk) hacc
    obtain ⟨hres_valid, hres_aff⟩ :=
      edMulBaseLoop_spec_gen table_bs hQ htable parity hdigits hparity
        rem (i + 1) (edMulBaseStepAt table_bs digits parity i acc) (by omega) hacc'_valid
    rw [edMulBaseLoop_step_fast]
    refine ⟨hres_valid, ?_⟩
    rw [hres_aff, hacc'_aff, radix256DigitSum]
    exact edMulBase_aff_step _ _ hacc.on_curve hQ

theorem edMulBaseLoop_spec {digits : List (BitVec 8)} (parity i rem : Nat) (acc : EdExtPoint)
    (hrem : i + rem ≤ 32)
    (hdigits : ∀ k < 64, -8 ≤ (digits.getD k 0#8).toInt ∧ (digits.getD k 0#8).toInt ≤ 8)
    (hparity : parity ≤ 1)
    (hacc : EdExtValid acc) :
    let res := edMulBaseLoop ed25519BasepointTableBytes digits parity i rem acc
    EdExtValid res ∧
    edExtToAffine res =
      edAdd (edExtToAffine acc)
        (edIntSmul (radix256DigitSum digits parity i rem) edBasepoint) :=
  edMulBaseLoop_spec_gen ed25519BasepointTableBytes edOnCurve_edBasepoint
    (fun _ hi _ hj => ed25519BasepointTable_entry_valid hi hj)
    parity hdigits hparity rem i acc hrem hacc

private theorem list_drop_two_eq {α : Type} :
    ∀ (xs : List α) (n : Nat) (hn0 : n < xs.length) (hn1 : n + 1 < xs.length),
      xs.drop n = (xs[n]'hn0) :: (xs[n + 1]'hn1) :: xs.drop (n + 2)
  | _ :: _ :: _, 0, _, _ => rfl
  | _ :: xs, n + 1, hn0, hn1 =>
    list_drop_two_eq xs n (by simp at hn0; omega) (by simp at hn1; omega)
  | [], _, hn0, _ => by simp at hn0
  | [_], 0, _, hn1 => by simp at hn1

private theorem signedRadix16Val_drop_pair (digits : List (BitVec 8)) (hlen : digits.length = 64) :
    ∀ rem : Nat, rem ≤ 32 →
      let i := 32 - rem
      16 * radix256DigitSum digits 1 i rem + radix256DigitSum digits 0 i rem =
        (256 : Int) ^ i * signedRadix16Val (digits.drop (2 * i)) := by
  intro rem
  induction rem with
  | zero =>
    intro _
    have hdrop : digits.drop 64 = [] := List.drop_of_length_le (by omega)
    simp [radix256DigitSum, hdrop, signedRadix16Val]
  | succ r ih =>
    intro hr
    have ih_r := ih (by omega)
    dsimp only at ih_r
    let i := 32 - (r + 1)
    have hi_succ : 32 - r = i + 1 := by omega
    change 16 * radix256DigitSum digits 1 i (r + 1) + radix256DigitSum digits 0 i (r + 1) =
      (256 : Int) ^ i * signedRadix16Val (digits.drop (2 * i))
    rw [radix256DigitSum, radix256DigitSum, ← hi_succ]
    have h2i_lt : 2 * i < digits.length := by omega
    have h2i1_lt : 2 * i + 1 < digits.length := by omega
    have hdrop_step :
        digits.drop (2 * i) =
        (digits[2 * i]'h2i_lt) :: (digits[2 * i + 1]'h2i1_lt) :: digits.drop (2 * (32 - r)) := by
      rw [list_drop_two_eq digits (2 * i) h2i_lt h2i1_lt,
          show 2 * i + 2 = 2 * (32 - r) by omega]
    have hd0 : digits.getD (2 * i + 0) 0#8 = digits[2 * i]'h2i_lt := by
      rw [Nat.add_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2i_lt]; rfl
    have hd1 : digits.getD (2 * i + 1) 0#8 = digits[2 * i + 1]'h2i1_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2i1_lt]; rfl
    rw [hdrop_step, signedRadix16Val, signedRadix16Val, hd0, hd1]
    have hpow : (256 : Int) ^ (32 - r) = (256 : Int) ^ i * 256 := by
      rw [hi_succ, Int.pow_succ]
    rw [hpow] at ih_r
    grind

/-- Parametric basepoint-table scalar multiplication soundness (`edMulBase_spec_gen`):
    for any valid curve point `Q` whose 32-subtable `EdwardsBasepointTable` `table_bs` holds
    `[j + 1]([256^i]Q)` at entry `(i, j)`, `edMulBase table_bs scalar_bs` produces a valid
    extended point with affine projection `edSmul (leBytesToNat scalar_bs) Q`. -/
theorem edMulBase_spec_gen (table_bs : List (BitVec 8))
    {Q : EdPoint} (hQ : edOnCurve Q = true)
    (htable : ∀ i < 32, ∀ j < 8,
      let (ypx, ymx, xy2d) := edTableEntryAt
        (ProofLib.ByteSlice.slice table_bs (960 * i) 960) j
      EdAffineNielsValid ypx ymx xy2d
        (edNatSmul (j + 1) (edNatSmul (256 ^ i) Q)))
    {scalar_bs : List (BitVec 8)}
    (hlen : scalar_bs.length = 32)
    (hb31 : (scalar_bs.getD 31 0#8).toNat ≤ 127) :
    EdExtValid (edMulBase table_bs scalar_bs) ∧
    edExtToAffine (edMulBase table_bs scalar_bs) =
      edSmul (leBytesToNat scalar_bs) Q := by
  dsimp only [edMulBase]
  let digits := scalarRadix16Digits scalar_bs
  obtain ⟨hdigits, hval⟩ := scalarRadix16Digits_spec hlen hb31
  obtain ⟨hodd_valid, hodd_aff⟩ :=
    edMulBaseLoop_spec_gen table_bs hQ htable 1 hdigits (by decide) 32 0 edExtZero (by decide) edExtValid_edExtZero
  rw [edExtToAffine_edExtZero, edZero_edAdd (edOnCurve_edIntSmul _ hQ)] at hodd_aff
  obtain ⟨hd4_valid, hd4_aff⟩ := edDouble4_spec hodd_valid
  obtain ⟨heven_valid, heven_aff⟩ :=
    edMulBaseLoop_spec_gen table_bs hQ htable 0 hdigits (by decide) 32 0
      (edDouble4 (edMulBaseLoop table_bs digits 1 0 32 edExtZero))
      (by decide) hd4_valid
  refine ⟨heven_valid, ?_⟩
  have hd4_int :
      edExtToAffine (edDouble4 (edMulBaseLoop table_bs digits 1 0 32 edExtZero)) =
      edIntSmul (16 * radix256DigitSum digits 1 0 32) Q := by
    rw [hd4_aff, hodd_aff, ← edIntSmul_ofNat 16,
        ← edIntSmul_mul (Int.ofNat 16) _ hQ]
    rfl
  rw [heven_aff, hd4_int, ← edIntSmul_add _ _ hQ]
  have hsum := signedRadix16Val_drop_pair digits (scalarRadix16Digits_length scalar_bs) 32 (by decide)
  simp only [Nat.sub_self, Nat.mul_zero, List.drop_zero, Int.pow_zero, Int.one_mul] at hsum
  have hlt : leBytesToNat scalar_bs < 2 ^ 256 := by
    have h1 := leBytesToNat_lt scalar_bs
    rwa [hlen, show 256 ^ 32 = 2 ^ 256 by decide] at h1
  rw [hsum, hval, edIntSmul_ofNat, ← edSmul_eq_edNatSmul hlt hQ]

/-- **Main Basepoint Scalar Multiplication Bridge (`edMulBase_spec`)**:
    for any 32-byte scalar `scalar_bs` with `scalar_bs[31] ≤ 127`, `edMulBase` produces a valid
    extended point whose affine projection equals `edSmul (leBytesToNat scalar_bs) edBasepoint`. -/
theorem edMulBase_spec {scalar_bs : List (BitVec 8)}
    (hlen : scalar_bs.length = 32)
    (hb31 : (scalar_bs.getD 31 0#8).toNat ≤ 127) :
    EdExtValid (edMulBase ed25519BasepointTableBytes scalar_bs) ∧
    edExtToAffine (edMulBase ed25519BasepointTableBytes scalar_bs) =
      edSmul (leBytesToNat scalar_bs) edBasepoint :=
  edMulBase_spec_gen ed25519BasepointTableBytes edOnCurve_edBasepoint
    (fun _ hi _ hj => ed25519BasepointTable_entry_valid hi hj) hlen hb31

theorem edMulBase_valid {scalar_bs : List (BitVec 8)}
    (hlen : scalar_bs.length = 32)
    (hb31 : (scalar_bs.getD 31 0#8).toNat ≤ 127) :
    EdExtValid (edMulBase ed25519BasepointTableBytes scalar_bs) :=
  (edMulBase_spec hlen hb31).1

theorem edMulBase_toAffine {scalar_bs : List (BitVec 8)}
    (hlen : scalar_bs.length = 32)
    (hb31 : (scalar_bs.getD 31 0#8).toNat ≤ 127) :
    edExtToAffine (edMulBase ed25519BasepointTableBytes scalar_bs) =
      edSmul (leBytesToNat scalar_bs) edBasepoint :=
  (edMulBase_spec hlen hb31).2

theorem encodeEd_edMulBase {scalar_bs : List (BitVec 8)}
    (hlen : scalar_bs.length = 32)
    (hb31 : (scalar_bs.getD 31 0#8).toNat ≤ 127) :
    encodeEd (edExtToAffine (edMulBase ed25519BasepointTableBytes scalar_bs)) =
      encodeEd (edSmul (leBytesToNat scalar_bs) edBasepoint) := by
  rw [edMulBase_toAffine hlen hb31]


theorem clampScalarBytes_length_of_eq32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    (clampScalarBytes bs).length = 32 := by
  unfold clampScalarBytes
  simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop, h]
  omega

private theorem b31_clamped_le_127_aux : ∀ b31 : BitVec 8, ((b31 &&& 0x7f#8) ||| 0x40#8).toNat ≤ 127 := by decide

theorem clampScalarBytes_getD31_le_127 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ((clampScalarBytes bs).getD 31 0#8).toNat ≤ 127 := by
  unfold clampScalarBytes
  have hd : ((bs.drop 1).take 30).length = 30 := by simp [h]
  rw [List.append_assoc, List.singleton_append, List.getD_cons_succ,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp only [hd, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  exact b31_clamped_le_127_aux _

theorem leBytesToNat_clampScalarBytes_eq_clampScalar {bs : List (BitVec 8)} (h : bs.length = 32) :
    leBytesToNat (clampScalarBytes bs) = clampScalar bs := by
  unfold clampScalar
  rw [List.take_of_length_le (by omega)]

theorem edMulBase_clampScalarBytes_spec {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    EdExtValid (edMulBase ed25519BasepointTableBytes (clampScalarBytes bs)) ∧
    edExtToAffine (edMulBase ed25519BasepointTableBytes (clampScalarBytes bs)) =
      edSmul (clampScalar bs) edBasepoint := by
  have ⟨hv, ha⟩ := edMulBase_spec (clampScalarBytes_length_of_eq32 hlen) (clampScalarBytes_getD31_le_127 hlen)
  rw [leBytesToNat_clampScalarBytes_eq_clampScalar hlen] at ha
  exact ⟨hv, ha⟩

theorem edMulBase_clampScalarBytes_valid {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    EdExtValid (edMulBase ed25519BasepointTableBytes (clampScalarBytes bs)) :=
  (edMulBase_clampScalarBytes_spec hlen).1

theorem edMulBase_clampScalarBytes_toAffine {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    edExtToAffine (edMulBase ed25519BasepointTableBytes (clampScalarBytes bs)) =
      edSmul (clampScalar bs) edBasepoint :=
  (edMulBase_clampScalarBytes_spec hlen).2

theorem encodeEd_edMulBase_clampScalarBytes {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    encodeEd (edExtToAffine (edMulBase ed25519BasepointTableBytes (clampScalarBytes bs))) =
      encodeEd (edSmul (clampScalar bs) edBasepoint) := by
  rw [edMulBase_clampScalarBytes_toAffine hlen]

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul2

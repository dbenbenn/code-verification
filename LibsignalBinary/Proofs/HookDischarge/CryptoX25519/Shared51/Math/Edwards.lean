/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field -- proof-setup: allow-public-import

/-!
# Twisted Edwards Curve Completeness, Group Laws, & Extended Coordinates (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards`)

Pure `0-sorry` mathematical proofs for the Ed25519 twisted Edwards curve
$-x^2 + y^2 \equiv 1 + d x^2 y^2 \pmod{p_{25519}}$ (`VerifiedLibraries.Common.Spec.Curve25519`):
1. Prime field type `Fp` ($\mathbb{F}_{p_{25519}}$) equipped with `Lean.Grind.CommRing` and
   `Lean.Grind.Field` instances.
2. Completeness of twisted Edwards addition (`edAdd_denom_add_ne_zero` and `edAdd_denom_sub_ne_zero`)
   for all curve points `edOnCurve P = true`, `edOnCurve Q = true`, deduced from `edD_nonsquare`.
3. Curve closure and abelian group laws (`edOnCurve_edZero`, `edOnCurve_edBasepoint`,
   `edOnCurve_edNeg`, `edOnCurve_edAdd`, `edAdd_comm`, `edAdd_edZero`, `edZero_edAdd`,
   `edAdd_edNeg_self`, `edNeg_edAdd_self`, `edAdd_assoc`, `edSub_eq_iff_eq_edAdd`).
4. Homogeneous extended coordinate validity (`EdExtValid`), equivalence of `edExtAdd` with
   `edAdd` (`edExtAdd_toAffine`, `edExtValid_edExtAdd`), and `edSmul` homomorphism laws
   (`edSmul_eq_edNatSmul`, `edNatSmul_add`, `edNatSmul_mul`, `edSmul_edOrderL_edBasepoint`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards

open VerifiedLibraries.Common (
  p25519 edOrderL fpAdd fpSub fpNeg fpMul fpSq fpInv sqrtM1 edD edD2 EdPoint EdExtPoint edZero
  edExtZero edExtOfAffine edExtToAffine edBasepoint edOnCurve edExtAdd edAdd edNeg edSub
  edExtSmulLoop edSmul)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  p25519_pos fpAdd_lt fpSub_lt fpNeg_lt fpMul_lt edD_mod_p fpAdd_mod_left fpAdd_comm fpAdd_assoc
  fpNeg_fpNeg fpSub_eq_fpAdd_fpNeg fpNeg_fpAdd_self fpMul_comm fpMul_assoc zero_fpMul fpMul_one
  fpMul_fpAdd fpAdd_fpMul fpNeg_fpMul fpInv_lt fpInv_zero fpInv_one fpMul_fpInv_cancel
  fpInv_eq_of_fpMul_eq_one edD_nonsquare fpSq_sqrtM1_eq_fpNeg_one)
attribute [local irreducible] fpInv

/-! ## 1. Prime Field Type `Fp` ($\mathbb{F}_{p_{25519}}$) with `Lean.Grind.Field` Instance -/

structure Fp where
  val : Nat
  isLt : val < p25519
  deriving DecidableEq

@[ext] theorem Fp.ext {a b : Fp} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

@[expose] def Fp.ofNat (n : Nat) : Fp := ⟨n % p25519, Nat.mod_lt n p25519_pos⟩

@[simp] theorem Fp.val_ofNat (n : Nat) : (Fp.ofNat n).val = n % p25519 := rfl

@[simp] theorem Fp.ofNat_val (a : Fp) : Fp.ofNat a.val = a := by
  ext; exact Nat.mod_eq_of_lt a.isLt

@[simp] theorem Fp.val_mod (a : Fp) : a.val % p25519 = a.val :=
  Nat.mod_eq_of_lt a.isLt

@[simp] theorem Fp.ofNat_mod (n : Nat) : Fp.ofNat (n % p25519) = Fp.ofNat n := by
  ext; exact Nat.mod_mod n p25519

theorem Fp.ofNat_eq_iff (a b : Nat) : Fp.ofNat a = Fp.ofNat b ↔ a % p25519 = b % p25519 :=
  ⟨fun h => congrArg Fp.val h, fun h => Fp.ext h⟩

theorem Fp.eq_of_ofNat_eq {a b : Nat} (ha : a < p25519) (hb : b < p25519)
    (h : Fp.ofNat a = Fp.ofNat b) : a = b := by
  have h1 := congrArg Fp.val h
  dsimp only [Fp.val_ofNat] at h1
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1

instance : Add Fp where
  add a b := ⟨fpAdd a.val b.val, fpAdd_lt a.val b.val⟩

instance : Sub Fp where
  sub a b := ⟨fpSub a.val b.val, fpSub_lt a.val b.val⟩

instance : Neg Fp where
  neg a := ⟨fpNeg a.val, fpNeg_lt a.val⟩

instance : Mul Fp where
  mul a b := ⟨fpMul a.val b.val, fpMul_lt a.val b.val⟩

instance : Inv Fp where
  inv a := ⟨fpInv a.val, fpInv_lt a.val⟩

instance : Div Fp where
  div a b := a * b⁻¹

instance (n : Nat) : OfNat Fp n where
  ofNat := Fp.ofNat n

instance : NatCast Fp where
  natCast := Fp.ofNat

instance : IntCast Fp where
  intCast i := if i ≥ 0 then Fp.ofNat i.toNat else -Fp.ofNat (-i).toNat

instance : SMul Nat Fp where
  smul n a := Fp.ofNat n * a

instance : SMul Int Fp where
  smul i a := (Int.cast i : Fp) * a

@[expose] def Fp.npow (a : Fp) : Nat → Fp
  | 0 => 1
  | n + 1 => Fp.npow a n * a

instance : HPow Fp Nat Fp where
  hPow := Fp.npow

@[expose] def Fp.zpow (a : Fp) : Int → Fp
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ (n + 1))⁻¹

instance : HPow Fp Int Fp where
  hPow := Fp.zpow

@[simp] theorem Fp.val_zero : (0 : Fp).val = 0 := rfl
@[simp] theorem Fp.val_one : (1 : Fp).val = 1 := by change 1 % p25519 = 1; unfold p25519; decide
@[simp] theorem Fp.val_add (a b : Fp) : (a + b).val = fpAdd a.val b.val := rfl
@[simp] theorem Fp.val_sub (a b : Fp) : (a - b).val = fpSub a.val b.val := rfl
@[simp] theorem Fp.val_neg (a : Fp) : (-a).val = fpNeg a.val := rfl
@[simp] theorem Fp.val_mul (a b : Fp) : (a * b).val = fpMul a.val b.val := rfl
@[simp] theorem Fp.val_inv (a : Fp) : (a⁻¹).val = fpInv a.val := rfl

@[simp] theorem Fp.ofNat_zero : Fp.ofNat 0 = 0 := rfl
@[simp] theorem Fp.ofNat_one : Fp.ofNat 1 = 1 := rfl
@[simp] theorem Fp.ofNat_fpAdd (a b : Nat) : Fp.ofNat (fpAdd a b) = Fp.ofNat a + Fp.ofNat b := by
  ext; simp
@[simp] theorem Fp.ofNat_fpSub (a b : Nat) : Fp.ofNat (fpSub a b) = Fp.ofNat a - Fp.ofNat b := by
  ext; simp
@[simp] theorem Fp.ofNat_fpNeg (a : Nat) : Fp.ofNat (fpNeg a) = -Fp.ofNat a := by
  ext; simp
@[simp] theorem Fp.ofNat_fpMul (a b : Nat) : Fp.ofNat (fpMul a b) = Fp.ofNat a * Fp.ofNat b := by
  ext; simp
@[simp] theorem Fp.ofNat_fpSq (a : Nat) : Fp.ofNat (fpSq a) = Fp.ofNat a * Fp.ofNat a := by
  ext; simp [fpSq]
@[simp] theorem Fp.ofNat_fpInv (a : Nat) : Fp.ofNat (fpInv a) = (Fp.ofNat a)⁻¹ := by
  ext; simp

theorem Fp.ofNat_ne_zero_iff (a : Nat) : Fp.ofNat a ≠ 0 ↔ a % p25519 ≠ 0 := by
  rw [ne_eq, ← Fp.ofNat_zero, Fp.ofNat_eq_iff, Nat.zero_mod]

instance : Lean.Grind.Semiring Fp where
  add_zero a := by ext; simp
  add_comm a b := by ext; exact fpAdd_comm a.val b.val
  add_assoc a b c := by ext; exact fpAdd_assoc a.val b.val c.val
  mul_assoc a b c := by ext; exact fpMul_assoc a.val b.val c.val
  mul_one a := by ext; simp
  one_mul a := by ext; simp
  left_distrib a b c := by ext; exact fpMul_fpAdd a.val b.val c.val
  right_distrib a b c := by ext; exact fpAdd_fpMul a.val b.val c.val
  zero_mul a := by ext; simp
  mul_zero a := by ext; simp
  pow_zero a := rfl
  pow_succ a n := rfl
  ofNat_succ a := by
    ext
    change (a + 1) % p25519 = fpAdd (a % p25519) 1
    rw [fpAdd_mod_left]; rfl
  ofNat_eq_natCast n := rfl
  nsmul_eq_natCast_mul n a := rfl

theorem Fp.intCast_neg_lemma (i : Int) : (Int.cast (-i) : Fp) = -(Int.cast i : Fp) := by
  change (if -i ≥ 0 then Fp.ofNat (-i).toNat else -Fp.ofNat (- -i).toNat) =
    -(if i ≥ 0 then Fp.ofNat i.toNat else -Fp.ofNat (-i).toNat)
  rcases Int.lt_trichotomy i 0 with hlt | rfl | hgt
  · have h1 : -i ≥ 0 := by omega
    have h2 : ¬(i ≥ 0) := by omega
    simp only [h1, h2, ↓reduceIte]
    ext; simp
  · ext; simp
  · have h1 : ¬(-i ≥ 0) := by omega
    have h2 : i ≥ 0 := by omega
    simp only [h1, h2, ↓reduceIte, Int.neg_neg]

instance : Lean.Grind.Ring Fp where
  neg_add_cancel a := by ext; exact fpNeg_fpAdd_self a.val
  sub_eq_add_neg a b := by ext; exact fpSub_eq_fpAdd_fpNeg a.val b.val
  neg_zsmul i a := by
    change (Int.cast (-i) : Fp) * a = -((Int.cast i : Fp) * a)
    rw [Fp.intCast_neg_lemma]
    ext; exact fpNeg_fpMul _ _
  zsmul_natCast_eq_nsmul n a := rfl
  intCast_ofNat n := rfl
  intCast_neg := Fp.intCast_neg_lemma

instance : Lean.Grind.CommRing Fp where
  mul_comm a b := by ext; exact fpMul_comm a.val b.val

theorem Fp.inv_inv (a : Fp) : (a⁻¹)⁻¹ = a := by
  by_cases ha : a = 0
  · subst ha; ext; simp [fpInv_zero]
  · have ha_mod : a.val % p25519 ≠ 0 := by
      rw [Fp.val_mod]; intro h0; exact ha (Fp.ext h0)
    ext
    rw [Fp.val_inv, Fp.val_inv]
    have h1 := fpInv_eq_of_fpMul_eq_one (a := fpInv a.val) (b := a.val)
      (by rw [fpMul_comm, fpMul_fpInv_cancel ha_mod])
    rw [Fp.val_mod] at h1
    exact h1

instance : Lean.Grind.Field Fp where
  div_eq_mul_inv a b := rfl
  zero_ne_one := by intro h; have := congrArg Fp.val h; revert this; decide
  inv_zero := by ext; simp [fpInv_zero]
  mul_inv_cancel {a} ha := by
    have ha_mod : a.val % p25519 ≠ 0 := by
      rw [Fp.val_mod]; intro h0; exact ha (Fp.ext h0)
    ext; simp [fpMul_fpInv_cancel ha_mod]
  zpow_zero a := rfl
  zpow_succ a n := rfl
  zpow_neg a i := by
    cases i with
    | ofNat n =>
      cases n with
      | zero =>
        change (1 : Fp) = (1 : Fp)⁻¹
        ext; simp [fpInv_one]
      | succ k => rfl
    | negSucc k =>
      change a ^ (k + 1) = ((a ^ (k + 1))⁻¹)⁻¹
      exact (Fp.inv_inv (a ^ (k + 1))).symm

theorem Fp.edD_nonsquare : ¬ ∃ r : Fp, r * r = Fp.ofNat edD := by
  rintro ⟨r, hr⟩
  have h1 := congrArg Fp.val hr
  rw [Fp.val_mul, Fp.val_ofNat, edD_mod_p] at h1
  exact LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field.edD_nonsquare ⟨r.val, h1⟩

theorem Fp.sqrtM1_sq : Fp.ofNat sqrtM1 * Fp.ofNat sqrtM1 = -1 := by
  rw [← Fp.ofNat_fpSq, fpSq_sqrtM1_eq_fpNeg_one, Fp.ofNat_fpNeg, Fp.ofNat_one]

theorem Fp.two_ne_zero : (2 : Fp) ≠ 0 := by
  intro h; have := congrArg Fp.val h; revert this; change 2 % p25519 = 0 → False; unfold p25519; decide

/-! ## 2. Twisted Edwards Curve Equation & Completeness -/

@[ext] theorem EdPoint.ext {P Q : EdPoint} (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
  cases P; cases Q; cases hx; cases hy; rfl

theorem edOnCurve_iff (P : EdPoint) :
    edOnCurve P = true ↔
      P.x < p25519 ∧ P.y < p25519 ∧
      fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) =
        fpAdd 1 (fpMul edD (fpMul (fpSq P.x) (fpSq P.y))) := by
  unfold edOnCurve
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]

theorem edOnCurve_x_lt {P : EdPoint} (hP : edOnCurve P = true) : P.x < p25519 :=
  ((edOnCurve_iff P).mp hP).1

theorem edOnCurve_y_lt {P : EdPoint} (hP : edOnCurve P = true) : P.y < p25519 :=
  ((edOnCurve_iff P).mp hP).2.1

theorem edOnCurve_eq {P : EdPoint} (hP : edOnCurve P = true) :
    fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) =
      fpAdd 1 (fpMul edD (fpMul (fpSq P.x) (fpSq P.y))) :=
  ((edOnCurve_iff P).mp hP).2.2

theorem edOnCurve_fp_eq {P : EdPoint} (hP : edOnCurve P = true) :
    -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y =
      1 + Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y)) := by
  have h := congrArg Fp.ofNat (edOnCurve_eq hP)
  simpa using h

theorem edOnCurve_of_fp_eq {P : EdPoint} (hx : P.x < p25519) (hy : P.y < p25519)
    (h : -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y =
      1 + Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y))) :
    edOnCurve P = true := by
  rw [edOnCurve_iff]
  refine ⟨hx, hy, Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (fpAdd_lt _ _) ?_⟩
  simpa using h

/-- Curve equation in the form $(d y^2 + 1) x^2 \equiv y^2 - 1 \pmod{p_{25519}}$ used by `recoverXEven`. -/
theorem edOnCurve_curve_eq {P : EdPoint} (hP : edOnCurve P = true) :
    fpMul (fpAdd (fpMul edD (fpSq P.y)) 1) (fpSq P.x) = fpSub (fpSq P.y) 1 := by
  have hfp := edOnCurve_fp_eq hP
  apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) (fpSub_lt _ _)
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpSq, Fp.ofNat_one]
  grind

@[simp] theorem edOnCurve_edZero : edOnCurve edZero = true := by
  unfold edOnCurve edZero fpAdd fpNeg fpSq fpMul edD p25519; decide

@[simp] theorem edOnCurve_edBasepoint : edOnCurve edBasepoint = true := by
  unfold edOnCurve edBasepoint fpAdd fpNeg fpSq fpMul edD p25519; decide

theorem edOnCurve_edNeg {P : EdPoint} (hP : edOnCurve P = true) :
    edOnCurve (edNeg P) = true := by
  have hfp := edOnCurve_fp_eq hP
  apply edOnCurve_of_fp_eq (fpNeg_lt P.x) (Nat.mod_lt P.y p25519_pos)
  simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]
  grind

private theorem completeness_ring_id (d x1 y1 x2 y2 j : Fp)
    (h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)))
    (h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2)))
    (hd : 1 + d * ((x1 * x2) * (y1 * y2)) = 0)
    (hj : j * j = -1) :
    d * ((x1 * y1 * (x2 + j * y2)) * (x1 * y1 * (x2 + j * y2))) =
      (x1 - j * y1) * (x1 - j * y1) := by
  grind

private theorem sq_div_of_mul_sq_eq {d w v : Fp}
    (h : d * (w * w) = v * v) (hw : w ≠ 0) :
    (v * w⁻¹) * (v * w⁻¹) = d := by
  grind

/-- **Twisted Edwards Completeness (`+`)**: for any two curve points $P, Q$,
    $1 + d x_1 x_2 y_1 y_2 \not\equiv 0 \pmod{p_{25519}}$. -/
theorem edAdd_denom_add_ne_zero {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    fpAdd 1 (fpMul edD (fpMul (fpMul P.x Q.x) (fpMul P.y Q.y))) ≠ 0 := by
  intro h0
  let d := Fp.ofNat edD
  let x1 := Fp.ofNat P.x
  let y1 := Fp.ofNat P.y
  let x2 := Fp.ofNat Q.x
  let y2 := Fp.ofNat Q.y
  let i := Fp.ofNat sqrtM1
  have h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)) := edOnCurve_fp_eq hP
  have h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2)) := edOnCurve_fp_eq hQ
  have hd : 1 + d * ((x1 * x2) * (y1 * y2)) = 0 := by
    have := congrArg Fp.ofNat h0
    simpa [d, x1, y1, x2, y2] using this
  have hi : i * i = -1 := Fp.sqrtM1_sq
  have hni : (-i) * (-i) = -1 := by grind
  have h_pos := completeness_ring_id d x1 y1 x2 y2 i h1 h2 hd hi
  have h_neg := completeness_ring_id d x1 y1 x2 y2 (-i) h1 h2 hd hni
  by_cases h_diff : x1 - i * y1 = 0
  · by_cases h_sum : x1 - (-i) * y1 = 0
    · have h2x1 : (2 : Fp) * x1 = 0 := by grind
      have h2ne : (2 : Fp) ≠ 0 := Fp.two_ne_zero
      have h10 : (1 : Fp) = 0 := by grind
      exact absurd h10.symm (by decide)
    · have hw_ne : x1 * y1 * (x2 + (-i) * y2) ≠ 0 := by grind
      exact Fp.edD_nonsquare ⟨_, sq_div_of_mul_sq_eq h_neg hw_ne⟩
  · have hw_ne : x1 * y1 * (x2 + i * y2) ≠ 0 := by grind
    exact Fp.edD_nonsquare ⟨_, sq_div_of_mul_sq_eq h_pos hw_ne⟩

/-- **Twisted Edwards Completeness (`-`)**: for any two curve points $P, Q$,
    $1 - d x_1 x_2 y_1 y_2 \not\equiv 0 \pmod{p_{25519}}$. -/
theorem edAdd_denom_sub_ne_zero {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    fpSub 1 (fpMul edD (fpMul (fpMul P.x Q.x) (fpMul P.y Q.y))) ≠ 0 := by
  have hneg := edAdd_denom_add_ne_zero (edOnCurve_edNeg hP) hQ
  intro h0
  apply hneg
  apply Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (by unfold p25519; decide)
  have hfp0 : Fp.ofNat (fpSub 1 (fpMul edD (fpMul (fpMul P.x Q.x) (fpMul P.y Q.y)))) = 0 := by
    rw [h0, Fp.ofNat_zero]
  simp only [edNeg, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpMul, Fp.ofNat_fpNeg,
    Fp.ofNat_mod, Fp.ofNat_one, Fp.ofNat_zero] at hfp0 ⊢
  grind

/-! ## 3. Twisted Edwards Abelian Group Laws on `EdPoint` -/

theorem edAdd_x_lt (P Q : EdPoint) : (edAdd P Q).x < p25519 := fpMul_lt _ _
theorem edAdd_y_lt (P Q : EdPoint) : (edAdd P Q).y < p25519 := fpMul_lt _ _

theorem edAdd_fp_x (P Q : EdPoint) :
    Fp.ofNat (edAdd P Q).x =
      (Fp.ofNat P.x * Fp.ofNat Q.y + Fp.ofNat P.y * Fp.ofNat Q.x) *
        (1 + Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ := by
  unfold edAdd
  simp

theorem edAdd_fp_y (P Q : EdPoint) :
    Fp.ofNat (edAdd P Q).y =
      (Fp.ofNat P.y * Fp.ofNat Q.y + Fp.ofNat P.x * Fp.ofNat Q.x) *
        (1 - Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ := by
  unfold edAdd
  simp

theorem edAdd_fp_denom_add_ne_zero {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    (1 : Fp) + Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)) ≠ 0 := by
  intro h
  apply edAdd_denom_add_ne_zero hP hQ
  apply Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (by unfold p25519; decide)
  simpa using h

theorem edAdd_fp_denom_sub_ne_zero {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    (1 : Fp) - Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)) ≠ 0 := by
  intro h
  apply edAdd_denom_sub_ne_zero hP hQ
  apply Fp.eq_of_ofNat_eq (fpSub_lt _ _) (by unfold p25519; decide)
  simpa using h

private theorem edAdd_onCurve_ring (d x1 y1 x2 y2 : Fp)
    (h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)))
    (h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2))) :
    let u := x1 * y2 + y1 * x2
    let v := y1 * y2 + x1 * x2
    let dp := 1 + d * ((x1 * x2) * (y1 * y2))
    let dm := 1 - d * ((x1 * x2) * (y1 * y2));
    -((u * dm) * (u * dm)) + (v * dp) * (v * dp) =
      (dp * dm) * (dp * dm) + d * ((u * u) * (v * v)) := by
  grind

theorem edOnCurve_edAdd {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    edOnCurve (edAdd P Q) = true := by
  apply edOnCurve_of_fp_eq (edAdd_x_lt P Q) (edAdd_y_lt P Q)
  have h1 := edOnCurve_fp_eq hP
  have h2 := edOnCurve_fp_eq hQ
  have hdp := edAdd_fp_denom_add_ne_zero hP hQ
  have hdm := edAdd_fp_denom_sub_ne_zero hP hQ
  have hring := edAdd_onCurve_ring (Fp.ofNat edD) (Fp.ofNat P.x) (Fp.ofNat P.y)
    (Fp.ofNat Q.x) (Fp.ofNat Q.y) h1 h2
  dsimp only at hring
  rw [edAdd_fp_x, edAdd_fp_y]
  grind

theorem edOnCurve_edSub {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    edOnCurve (edSub P Q) = true :=
  edOnCurve_edAdd hP (edOnCurve_edNeg hQ)

theorem edAdd_comm (P Q : EdPoint) : edAdd P Q = edAdd Q P := by
  ext
  · apply Fp.eq_of_ofNat_eq (edAdd_x_lt P Q) (edAdd_x_lt Q P)
    rw [edAdd_fp_x, edAdd_fp_x]; grind
  · apply Fp.eq_of_ofNat_eq (edAdd_y_lt P Q) (edAdd_y_lt Q P)
    rw [edAdd_fp_y, edAdd_fp_y]; grind

@[simp] theorem edAdd_edZero {P : EdPoint} (hP : edOnCurve P = true) :
    edAdd P edZero = P := by
  ext
  · apply Fp.eq_of_ofNat_eq (edAdd_x_lt P edZero) (edOnCurve_x_lt hP)
    rw [edAdd_fp_x]; simp [edZero]; grind
  · apply Fp.eq_of_ofNat_eq (edAdd_y_lt P edZero) (edOnCurve_y_lt hP)
    rw [edAdd_fp_y]; simp [edZero]; grind

@[simp] theorem edZero_edAdd {P : EdPoint} (hP : edOnCurve P = true) :
    edAdd edZero P = P := by
  rw [edAdd_comm, edAdd_edZero hP]

@[simp] theorem edAdd_edNeg_self {P : EdPoint} (hP : edOnCurve P = true) :
    edAdd P (edNeg P) = edZero := by
  have h1 := edOnCurve_fp_eq hP
  have hdm := edAdd_fp_denom_sub_ne_zero hP (edOnCurve_edNeg hP)
  simp only [edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod] at hdm
  ext
  · apply Fp.eq_of_ofNat_eq (edAdd_x_lt P (edNeg P)) (by unfold edZero p25519; decide)
    rw [edAdd_fp_x]; simp [edNeg, edZero]; grind
  · apply Fp.eq_of_ofNat_eq (edAdd_y_lt P (edNeg P)) (by unfold edZero p25519; decide)
    rw [edAdd_fp_y]; simp [edNeg, edZero]; grind

@[simp] theorem edNeg_edAdd_self {P : EdPoint} (hP : edOnCurve P = true) :
    edAdd (edNeg P) P = edZero := by
  rw [edAdd_comm, edAdd_edNeg_self hP]

@[simp] theorem edSub_self {P : EdPoint} (hP : edOnCurve P = true) :
    edSub P P = edZero :=
  edAdd_edNeg_self hP

@[simp] theorem edNeg_edZero : edNeg edZero = edZero := by
  unfold edNeg edZero fpNeg p25519; decide

@[simp] theorem edNeg_edNeg {P : EdPoint} (hP : edOnCurve P = true) :
    edNeg (edNeg P) = P := by
  ext
  · dsimp only [edNeg]
    rw [fpNeg_fpNeg, Nat.mod_eq_of_lt (edOnCurve_x_lt hP)]
  · dsimp only [edNeg]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (edOnCurve_y_lt hP)]

theorem edNeg_edAdd (P Q : EdPoint) :
    edNeg (edAdd P Q) = edAdd (edNeg P) (edNeg Q) := by
  ext
  · apply Fp.eq_of_ofNat_eq (fpNeg_lt _) (edAdd_x_lt _ _)
    rw [edAdd_fp_x]; simp [edNeg, edAdd_fp_x]; grind
  · apply Fp.eq_of_ofNat_eq (Nat.mod_lt _ p25519_pos) (edAdd_y_lt _ _)
    rw [edAdd_fp_y]; simp [edNeg, edAdd_fp_y]; grind

private theorem edAdd_assoc_x_ring (d x1 y1 x2 y2 x3 y3 : Fp)
    (h1 : d * ((x1 * x1) * (y1 * y1)) = -(x1 * x1) + y1 * y1 - 1)
    (h2 : d * ((x2 * x2) * (y2 * y2)) = -(x2 * x2) + y2 * y2 - 1)
    (h3 : d * ((x3 * x3) * (y3 * y3)) = -(x3 * x3) + y3 * y3 - 1) :
    let u12 := x1 * y2 + y1 * x2
    let v12 := y1 * y2 + x1 * x2
    let dp12 := 1 + d * ((x1 * x2) * (y1 * y2))
    let dm12 := 1 - d * ((x1 * x2) * (y1 * y2))
    let u23 := x2 * y3 + y2 * x3
    let v23 := y2 * y3 + x2 * x3
    let dp23 := 1 + d * ((x2 * x3) * (y2 * y3))
    let dm23 := 1 - d * ((x2 * x3) * (y2 * y3));
    (u12 * dm12 * y3 + v12 * dp12 * x3) * (dp23 * dm23 + d * ((x1 * u23) * (y1 * v23))) =
      (x1 * dp23 * v23 + y1 * dm23 * u23) * (dp12 * dm12 + d * ((u12 * x3) * (v12 * y3))) := by
  grind

private theorem edAdd_assoc_y_ring (d x1 y1 x2 y2 x3 y3 : Fp)
    (h1 : d * ((x1 * x1) * (y1 * y1)) = -(x1 * x1) + y1 * y1 - 1)
    (h2 : d * ((x2 * x2) * (y2 * y2)) = -(x2 * x2) + y2 * y2 - 1)
    (h3 : d * ((x3 * x3) * (y3 * y3)) = -(x3 * x3) + y3 * y3 - 1) :
    let u12 := x1 * y2 + y1 * x2
    let v12 := y1 * y2 + x1 * x2
    let dp12 := 1 + d * ((x1 * x2) * (y1 * y2))
    let dm12 := 1 - d * ((x1 * x2) * (y1 * y2))
    let u23 := x2 * y3 + y2 * x3
    let v23 := y2 * y3 + x2 * x3
    let dp23 := 1 + d * ((x2 * x3) * (y2 * y3))
    let dm23 := 1 - d * ((x2 * x3) * (y2 * y3));
    (v12 * dp12 * y3 + u12 * dm12 * x3) * (dp23 * dm23 - d * ((x1 * u23) * (y1 * v23))) =
      (y1 * dp23 * v23 + x1 * dm23 * u23) * (dp12 * dm12 - d * ((u12 * x3) * (v12 * y3))) := by
  grind

private theorem edAdd_assoc_x_clear (d u12 v12 dp12 dm12 u23 v23 dp23 dm23 x1 y1 x3 y3 : Fp)
    (hdp12 : dp12 ≠ 0) (hdm12 : dm12 ≠ 0) (hdp23 : dp23 ≠ 0) (hdm23 : dm23 ≠ 0)
    (hdp12_3 : 1 + d * (((u12 * dp12⁻¹) * x3) * ((v12 * dm12⁻¹) * y3)) ≠ 0)
    (hdp1_23 : 1 + d * ((x1 * (u23 * dp23⁻¹)) * (y1 * (v23 * dm23⁻¹))) ≠ 0)
    (hring : (u12 * dm12 * y3 + v12 * dp12 * x3) * (dp23 * dm23 + d * ((x1 * u23) * (y1 * v23))) =
      (x1 * dp23 * v23 + y1 * dm23 * u23) * (dp12 * dm12 + d * ((u12 * x3) * (v12 * y3)))) :
    ((u12 * dp12⁻¹) * y3 + (v12 * dm12⁻¹) * x3) *
        (1 + d * (((u12 * dp12⁻¹) * x3) * ((v12 * dm12⁻¹) * y3)))⁻¹ =
      (x1 * (v23 * dm23⁻¹) + y1 * (u23 * dp23⁻¹)) *
        (1 + d * ((x1 * (u23 * dp23⁻¹)) * (y1 * (v23 * dm23⁻¹))))⁻¹ := by
  grind

private theorem edAdd_assoc_y_clear (d u12 v12 dp12 dm12 u23 v23 dp23 dm23 x1 y1 x3 y3 : Fp)
    (hdp12 : dp12 ≠ 0) (hdm12 : dm12 ≠ 0) (hdp23 : dp23 ≠ 0) (hdm23 : dm23 ≠ 0)
    (hdm12_3 : 1 - d * (((u12 * dp12⁻¹) * x3) * ((v12 * dm12⁻¹) * y3)) ≠ 0)
    (hdm1_23 : 1 - d * ((x1 * (u23 * dp23⁻¹)) * (y1 * (v23 * dm23⁻¹))) ≠ 0)
    (hring : (v12 * dp12 * y3 + u12 * dm12 * x3) * (dp23 * dm23 - d * ((x1 * u23) * (y1 * v23))) =
      (y1 * dp23 * v23 + x1 * dm23 * u23) * (dp12 * dm12 - d * ((u12 * x3) * (v12 * y3)))) :
    ((v12 * dm12⁻¹) * y3 + (u12 * dp12⁻¹) * x3) *
        (1 - d * (((u12 * dp12⁻¹) * x3) * ((v12 * dm12⁻¹) * y3)))⁻¹ =
      (y1 * (v23 * dm23⁻¹) + x1 * (u23 * dp23⁻¹)) *
        (1 - d * ((x1 * (u23 * dp23⁻¹)) * (y1 * (v23 * dm23⁻¹))))⁻¹ := by
  grind

theorem edAdd_assoc {P Q R : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) (hR : edOnCurve R = true) :
    edAdd (edAdd P Q) R = edAdd P (edAdd Q R) := by
  have hPQ : edOnCurve (edAdd P Q) = true := edOnCurve_edAdd hP hQ
  have hQR : edOnCurve (edAdd Q R) = true := edOnCurve_edAdd hQ hR
  have h1 : Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y)) =
      -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y - 1 := by
    have := edOnCurve_fp_eq hP; grind
  have h2 : Fp.ofNat edD * ((Fp.ofNat Q.x * Fp.ofNat Q.x) * (Fp.ofNat Q.y * Fp.ofNat Q.y)) =
      -(Fp.ofNat Q.x * Fp.ofNat Q.x) + Fp.ofNat Q.y * Fp.ofNat Q.y - 1 := by
    have := edOnCurve_fp_eq hQ; grind
  have h3 : Fp.ofNat edD * ((Fp.ofNat R.x * Fp.ofNat R.x) * (Fp.ofNat R.y * Fp.ofNat R.y)) =
      -(Fp.ofNat R.x * Fp.ofNat R.x) + Fp.ofNat R.y * Fp.ofNat R.y - 1 := by
    have := edOnCurve_fp_eq hR; grind
  have hdp12 := edAdd_fp_denom_add_ne_zero hP hQ
  have hdm12 := edAdd_fp_denom_sub_ne_zero hP hQ
  have hdp23 := edAdd_fp_denom_add_ne_zero hQ hR
  have hdm23 := edAdd_fp_denom_sub_ne_zero hQ hR
  have hdp12_3 := edAdd_fp_denom_add_ne_zero hPQ hR
  have hdm12_3 := edAdd_fp_denom_sub_ne_zero hPQ hR
  have hdp1_23 := edAdd_fp_denom_add_ne_zero hP hQR
  have hdm1_23 := edAdd_fp_denom_sub_ne_zero hP hQR
  rw [edAdd_fp_x P Q, edAdd_fp_y P Q] at hdp12_3 hdm12_3
  rw [edAdd_fp_x Q R, edAdd_fp_y Q R] at hdp1_23 hdm1_23
  ext
  · apply Fp.eq_of_ofNat_eq (edAdd_x_lt _ _) (edAdd_x_lt _ _)
    have hx_ring := edAdd_assoc_x_ring (Fp.ofNat edD)
      (Fp.ofNat P.x) (Fp.ofNat P.y) (Fp.ofNat Q.x) (Fp.ofNat Q.y) (Fp.ofNat R.x) (Fp.ofNat R.y)
      h1 h2 h3
    rw [edAdd_fp_x (edAdd P Q) R, edAdd_fp_x P (edAdd Q R),
        edAdd_fp_x P Q, edAdd_fp_y P Q, edAdd_fp_x Q R, edAdd_fp_y Q R]
    exact edAdd_assoc_x_clear _ _ _ _ _ _ _ _ _ _ _ _ _
      hdp12 hdm12 hdp23 hdm23 hdp12_3 hdp1_23 hx_ring
  · apply Fp.eq_of_ofNat_eq (edAdd_y_lt _ _) (edAdd_y_lt _ _)
    have hy_ring := edAdd_assoc_y_ring (Fp.ofNat edD)
      (Fp.ofNat P.x) (Fp.ofNat P.y) (Fp.ofNat Q.x) (Fp.ofNat Q.y) (Fp.ofNat R.x) (Fp.ofNat R.y)
      h1 h2 h3
    rw [edAdd_fp_y (edAdd P Q) R, edAdd_fp_y P (edAdd Q R),
        edAdd_fp_x P Q, edAdd_fp_y P Q, edAdd_fp_x Q R, edAdd_fp_y Q R]
    exact edAdd_assoc_y_clear _ _ _ _ _ _ _ _ _ _ _ _ _
      hdp12 hdm12 hdp23 hdm23 hdm12_3 hdm1_23 hy_ring

theorem edAdd_edSub_cancel {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    edSub (edAdd P Q) Q = P := by
  unfold edSub
  rw [edAdd_assoc hP hQ (edOnCurve_edNeg hQ), edAdd_edNeg_self hQ, edAdd_edZero hP]

theorem edSub_edAdd_cancel {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    edAdd (edSub P Q) Q = P := by
  unfold edSub
  rw [edAdd_assoc hP (edOnCurve_edNeg hQ) hQ, edNeg_edAdd_self hQ, edAdd_edZero hP]

theorem edSub_eq_iff_eq_edAdd {S R K : EdPoint}
    (hS : edOnCurve S = true) (hR : edOnCurve R = true) (hK : edOnCurve K = true) :
    edSub S K = R ↔ S = edAdd R K := by
  constructor
  · intro h
    rw [← h, edSub_edAdd_cancel hS hK]
  · intro h
    rw [h, edAdd_edSub_cancel hR hK]

/-! ## 4. Extended Coordinates (`EdExtPoint`) Equivalence & Completeness -/

@[simp] theorem Fp.ofNat_edD2 : Fp.ofNat edD2 = 2 * Fp.ofNat edD := by
  ext
  change edD2 % p25519 = fpMul (2 % p25519) (edD % p25519)
  unfold edD2 edD fpMul p25519
  decide

/-- Well-formedness invariant for extended twisted Edwards points $P = (X, Y, Z, T)$:
    $Z \not\equiv 0 \pmod p$, $T Z \equiv X Y \pmod p$, and the projected affine point
    $(X Z^{-1}, Y Z^{-1})$ lies on the curve. -/
structure EdExtValid (P : EdExtPoint) : Prop where
  z_ne_zero : Fp.ofNat P.Z ≠ 0
  tz_eq_xy : Fp.ofNat P.T * Fp.ofNat P.Z = Fp.ofNat P.X * Fp.ofNat P.Y
  on_curve : edOnCurve (edExtToAffine P) = true

theorem edExtToAffine_x_lt (P : EdExtPoint) : (edExtToAffine P).x < p25519 := fpMul_lt _ _
theorem edExtToAffine_y_lt (P : EdExtPoint) : (edExtToAffine P).y < p25519 := fpMul_lt _ _

theorem edExtToAffine_fp_x (P : EdExtPoint) :
    Fp.ofNat (edExtToAffine P).x = Fp.ofNat P.X * (Fp.ofNat P.Z)⁻¹ := by
  unfold edExtToAffine; simp

theorem edExtToAffine_fp_y (P : EdExtPoint) :
    Fp.ofNat (edExtToAffine P).y = Fp.ofNat P.Y * (Fp.ofNat P.Z)⁻¹ := by
  unfold edExtToAffine; simp

@[simp] theorem edExtToAffine_edExtZero : edExtToAffine edExtZero = edZero := by
  ext
  · change fpMul 0 (fpInv 1) = 0; simp [fpInv_one]
  · change fpMul 1 (fpInv 1) = 1; simp [fpInv_one]

theorem edExtValid_edExtZero : EdExtValid edExtZero where
  z_ne_zero := by intro h; have := congrArg Fp.val h; revert this; decide
  tz_eq_xy := by ext; simp [edExtZero]
  on_curve := by rw [edExtToAffine_edExtZero]; exact edOnCurve_edZero

@[simp] theorem edExtToAffine_edExtOfAffine {P : EdPoint} (hP : edOnCurve P = true) :
    edExtToAffine (edExtOfAffine P) = P := by
  ext
  · dsimp only [edExtOfAffine, edExtToAffine]
    rw [fpInv_one, fpMul_one, Nat.mod_mod, Nat.mod_eq_of_lt (edOnCurve_x_lt hP)]
  · dsimp only [edExtOfAffine, edExtToAffine]
    rw [fpInv_one, fpMul_one, Nat.mod_mod, Nat.mod_eq_of_lt (edOnCurve_y_lt hP)]

theorem edExtValid_edExtOfAffine {P : EdPoint} (hP : edOnCurve P = true) :
    EdExtValid (edExtOfAffine P) where
  z_ne_zero := edExtValid_edExtZero.z_ne_zero
  tz_eq_xy := by unfold edExtOfAffine; simp; grind
  on_curve := by rw [edExtToAffine_edExtOfAffine hP]; exact hP

theorem Fp.mul_ne_zero {a b : Fp} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hab
  have h1 : a * b * b⁻¹ = 0 * b⁻¹ := congrArg (· * b⁻¹) hab
  have h2 : a = 0 := by grind
  exact ha h2

private theorem edExtAdd_z_ne_zero_ring (d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2 : Fp)
    (h2 : (2 : Fp) ≠ 0) (hZ1 : Z1 ≠ 0) (hZ2 : Z2 ≠ 0)
    (hT1 : T1 * Z1 = X1 * Y1) (hT2 : T2 * Z2 = X2 * Y2)
    (hx1 : x1 = X1 * Z1⁻¹) (hy1 : y1 = Y1 * Z1⁻¹)
    (hx2 : x2 = X2 * Z2⁻¹) (hy2 : y2 = Y2 * Z2⁻¹)
    (hdp : 1 + d * ((x1 * x2) * (y1 * y2)) ≠ 0)
    (hdm : 1 - d * ((x1 * x2) * (y1 * y2)) ≠ 0) :
    (Z1 * (Z2 + Z2) - T1 * (2 * d * T2)) * (Z1 * (Z2 + Z2) + T1 * (2 * d * T2)) ≠ 0 := by
  have hF : Z1 * (Z2 + Z2) - T1 * (2 * d * T2) =
      2 * Z1 * Z2 * (1 - d * ((x1 * x2) * (y1 * y2))) := by grind
  have hG : Z1 * (Z2 + Z2) + T1 * (2 * d * T2) =
      2 * Z1 * Z2 * (1 + d * ((x1 * x2) * (y1 * y2))) := by grind
  rw [hF, hG]
  exact Fp.mul_ne_zero
    (Fp.mul_ne_zero (Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hZ2) hdm)
    (Fp.mul_ne_zero (Fp.mul_ne_zero (Fp.mul_ne_zero h2 hZ1) hZ2) hdp)

private theorem edExtAdd_x_ring (d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2 : Fp)
    (h2 : (2 : Fp) ≠ 0) (hZ1 : Z1 ≠ 0) (hZ2 : Z2 ≠ 0)
    (hT1 : T1 * Z1 = X1 * Y1) (hT2 : T2 * Z2 = X2 * Y2)
    (hx1 : x1 = X1 * Z1⁻¹) (hy1 : y1 = Y1 * Z1⁻¹)
    (hx2 : x2 = X2 * Z2⁻¹) (hy2 : y2 = Y2 * Z2⁻¹)
    (hdp : 1 + d * ((x1 * x2) * (y1 * y2)) ≠ 0)
    (hdm : 1 - d * ((x1 * x2) * (y1 * y2)) ≠ 0) :
    let A := (Y1 - X1) * (Y2 - X2)
    let B := (Y1 + X1) * (Y2 + X2)
    let C := T1 * (2 * d * T2)
    let D := Z1 * (Z2 + Z2)
    let E := B - A
    let F := D - C
    let G := D + C;
    (E * F) * (F * G)⁻¹ = (x1 * y2 + y1 * x2) * (1 + d * ((x1 * x2) * (y1 * y2)))⁻¹ := by
  have hFG := edExtAdd_z_ne_zero_ring d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2
    h2 hZ1 hZ2 hT1 hT2 hx1 hy1 hx2 hy2 hdp hdm
  grind

private theorem edExtAdd_y_ring (d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2 : Fp)
    (h2 : (2 : Fp) ≠ 0) (hZ1 : Z1 ≠ 0) (hZ2 : Z2 ≠ 0)
    (hT1 : T1 * Z1 = X1 * Y1) (hT2 : T2 * Z2 = X2 * Y2)
    (hx1 : x1 = X1 * Z1⁻¹) (hy1 : y1 = Y1 * Z1⁻¹)
    (hx2 : x2 = X2 * Z2⁻¹) (hy2 : y2 = Y2 * Z2⁻¹)
    (hdp : 1 + d * ((x1 * x2) * (y1 * y2)) ≠ 0)
    (hdm : 1 - d * ((x1 * x2) * (y1 * y2)) ≠ 0) :
    let A := (Y1 - X1) * (Y2 - X2)
    let B := (Y1 + X1) * (Y2 + X2)
    let C := T1 * (2 * d * T2)
    let D := Z1 * (Z2 + Z2)
    let F := D - C
    let G := D + C
    let H := B + A;
    (G * H) * (F * G)⁻¹ = (y1 * y2 + x1 * x2) * (1 - d * ((x1 * x2) * (y1 * y2)))⁻¹ := by
  have hFG := edExtAdd_z_ne_zero_ring d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2
    h2 hZ1 hZ2 hT1 hT2 hx1 hy1 hx2 hy2 hdp hdm
  grind

theorem edExtAdd_toAffine {P Q : EdExtPoint}
    (hP : EdExtValid P) (hQ : EdExtValid Q) :
    edExtToAffine (edExtAdd P Q) = edAdd (edExtToAffine P) (edExtToAffine Q) := by
  have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
  have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
  ext
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_x_lt _) (edAdd_x_lt _ _)
    rw [edExtToAffine_fp_x, edAdd_fp_x]
    unfold edExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_edD2]
    exact edExtAdd_x_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hQ.z_ne_zero hP.tz_eq_xy hQ.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      (edExtToAffine_fp_x Q) (edExtToAffine_fp_y Q) hdp hdm
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_y_lt _) (edAdd_y_lt _ _)
    rw [edExtToAffine_fp_y, edAdd_fp_y]
    unfold edExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_edD2]
    exact edExtAdd_y_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hQ.z_ne_zero hP.tz_eq_xy hQ.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      (edExtToAffine_fp_x Q) (edExtToAffine_fp_y Q) hdp hdm

theorem edExtValid_edExtAdd {P Q : EdExtPoint}
    (hP : EdExtValid P) (hQ : EdExtValid Q) :
    EdExtValid (edExtAdd P Q) where
  z_ne_zero := by
    have hdp := edAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
    have hdm := edAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
    unfold edExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_edD2]
    exact edExtAdd_z_ne_zero_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hQ.z_ne_zero hP.tz_eq_xy hQ.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      (edExtToAffine_fp_x Q) (edExtToAffine_fp_y Q) hdp hdm
  tz_eq_xy := by
    unfold edExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub]
    grind
  on_curve := by
    rw [edExtAdd_toAffine hP hQ]
    exact edOnCurve_edAdd hP.on_curve hQ.on_curve

/-! ## 5. Scalar Multiplication Homomorphism & Basepoint Order ($\ell B = \mathcal{O}$) -/

/-- Peano scalar multiplication $[n]P$ on affine twisted Edwards points for arbitrary $n \in \mathbb{N}$. -/
@[expose] def edNatSmul : Nat → EdPoint → EdPoint
  | 0, _ => edZero
  | n + 1, P => edAdd P (edNatSmul n P)

@[simp] theorem edNatSmul_zero (P : EdPoint) : edNatSmul 0 P = edZero := rfl
@[simp] theorem edNatSmul_succ (n : Nat) (P : EdPoint) :
    edNatSmul (n + 1) P = edAdd P (edNatSmul n P) := rfl

theorem edOnCurve_edNatSmul (n : Nat) {P : EdPoint} (hP : edOnCurve P = true) :
    edOnCurve (edNatSmul n P) = true := by
  induction n with
  | zero => exact edOnCurve_edZero
  | succ k ih => exact edOnCurve_edAdd hP ih

@[simp] theorem edNatSmul_edZero (n : Nat) : edNatSmul n edZero = edZero := by
  induction n with
  | zero => rfl
  | succ k ih => rw [edNatSmul_succ, ih, edAdd_edZero edOnCurve_edZero]

@[simp] theorem edNatSmul_one {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 1 P = P := by
  rw [edNatSmul_succ, edNatSmul_zero, edAdd_edZero hP]

theorem edNatSmul_add (m n : Nat) {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul (m + n) P = edAdd (edNatSmul m P) (edNatSmul n P) := by
  induction m with
  | zero =>
    rw [Nat.zero_add, edNatSmul_zero, edZero_edAdd (edOnCurve_edNatSmul n hP)]
  | succ k ih =>
    rw [Nat.succ_add, edNatSmul_succ, edNatSmul_succ, ih,
        edAdd_assoc hP (edOnCurve_edNatSmul k hP) (edOnCurve_edNatSmul n hP)]

theorem edNatSmul_two {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 2 P = edAdd P P := by
  change edNatSmul (1 + 1) P = edAdd P P
  rw [edNatSmul_add 1 1 hP, edNatSmul_one hP]

theorem edNatSmul_mul (m n : Nat) {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul (m * n) P = edNatSmul m (edNatSmul n P) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.add_comm (k * n) n, edNatSmul_add n (k * n) hP,
        edNatSmul_succ, ih]

theorem edNatSmul_edAdd (n : Nat) {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true) :
    edNatSmul n (edAdd P Q) = edAdd (edNatSmul n P) (edNatSmul n Q) := by
  induction n with
  | zero =>
    rw [edNatSmul_zero, edNatSmul_zero, edNatSmul_zero, edAdd_edZero edOnCurve_edZero]
  | succ k ih =>
    have hkP := edOnCurve_edNatSmul k hP
    have hkQ := edOnCurve_edNatSmul k hQ
    rw [edNatSmul_succ, edNatSmul_succ, edNatSmul_succ, ih,
        edAdd_assoc hP hQ (edOnCurve_edAdd hkP hkQ),
        ← edAdd_assoc hQ hkP hkQ,
        edAdd_comm Q (edNatSmul k P),
        edAdd_assoc hkP hQ hkQ,
        ← edAdd_assoc hP hkP (edOnCurve_edAdd hQ hkQ)]

theorem edExtSmulLoop_spec (fuel n : Nat) (P acc : EdExtPoint)
    (hn : n < 2 ^ fuel) (hP : EdExtValid P) (hacc : EdExtValid acc) :
    EdExtValid (edExtSmulLoop fuel n P acc) ∧
    edExtToAffine (edExtSmulLoop fuel n P acc) =
      edAdd (edExtToAffine acc) (edNatSmul n (edExtToAffine P)) := by
  induction fuel generalizing n P acc with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    refine ⟨hacc, ?_⟩
    rw [edExtSmulLoop, edNatSmul_zero, edAdd_edZero hacc.on_curve]
  | succ fuel ih =>
    unfold edExtSmulLoop
    by_cases h0 : n == 0
    · simp only [h0, ↓reduceIte]
      have hn0 : n = 0 := beq_iff_eq.mp h0
      subst hn0
      refine ⟨hacc, ?_⟩
      rw [edNatSmul_zero, edAdd_edZero hacc.on_curve]
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      have hn_div : n / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hn; omega
      have hPP : EdExtValid (edExtAdd P P) := edExtValid_edExtAdd hP hP
      have hacc' : EdExtValid (if n % 2 == 1 then edExtAdd acc P else acc) := by
        split
        · exact edExtValid_edExtAdd hacc hP
        · exact hacc
      obtain ⟨hvalid, heq⟩ := ih (n / 2) (edExtAdd P P)
        (if n % 2 == 1 then edExtAdd acc P else acc) hn_div hPP hacc'
      refine ⟨hvalid, ?_⟩
      rw [heq, edExtAdd_toAffine hP hP, ← edNatSmul_two hP.on_curve,
          ← edNatSmul_mul (n / 2) 2 hP.on_curve]
      by_cases hodd : n % 2 == 1
      · simp only [hodd, ↓reduceIte]
        have hrem : n % 2 = 1 := beq_iff_eq.mp hodd
        rw [edExtAdd_toAffine hacc hP,
            edAdd_assoc hacc.on_curve hP.on_curve (edOnCurve_edNatSmul _ hP.on_curve),
            ← edNatSmul_succ,
            show n / 2 * 2 + 1 = n by omega]
      · simp only [hodd, Bool.false_eq_true, ↓reduceIte]
        have hrem : n % 2 = 0 := by
          have : n % 2 ≠ 1 := by intro h; exact hodd (beq_iff_eq.mpr h)
          omega
        rw [show n / 2 * 2 = n by omega]

theorem edSmul_eq_edNatSmul {n : Nat} {P : EdPoint}
    (hn : n < 2 ^ 256) (hP : edOnCurve P = true) :
    edSmul n P = edNatSmul n P := by
  unfold edSmul
  obtain ⟨_, heq⟩ := edExtSmulLoop_spec 256 n (edExtOfAffine P) edExtZero
    hn (edExtValid_edExtOfAffine hP) edExtValid_edExtZero
  rw [heq, edExtToAffine_edExtZero, edExtToAffine_edExtOfAffine hP,
      edZero_edAdd (edOnCurve_edNatSmul n hP)]

theorem edOnCurve_edSmul {n : Nat} {P : EdPoint}
    (hn : n < 2 ^ 256) (hP : edOnCurve P = true) :
    edOnCurve (edSmul n P) = true := by
  rw [edSmul_eq_edNatSmul hn hP]
  exact edOnCurve_edNatSmul n hP

private theorem edExtToAffine_eq_edZero_of_X_eq_zero_Y_eq_Z {Q : EdExtPoint}
    (hX : Q.X = 0) (hYZ : Q.Y = Q.Z) (hZ : Q.Z % p25519 ≠ 0) :
    edExtToAffine Q = edZero := by
  ext
  · dsimp only [edExtToAffine, edZero]
    rw [hX, zero_fpMul]
  · dsimp only [edExtToAffine, edZero]
    rw [hYZ, fpMul_fpInv_cancel hZ]

set_option maxRecDepth 50000 in
private theorem edExtSmulLoop_edOrderL_edBasepoint :
    let Q := edExtSmulLoop 256 edOrderL (edExtOfAffine edBasepoint) edExtZero
    Q.X = 0 ∧ Q.Y = Q.Z ∧ Q.Z % p25519 ≠ 0 := by
  decide

theorem edSmul_edOrderL_edBasepoint : edSmul edOrderL edBasepoint = edZero := by
  unfold edSmul
  obtain ⟨hX, hYZ, hZ⟩ := edExtSmulLoop_edOrderL_edBasepoint
  exact edExtToAffine_eq_edZero_of_X_eq_zero_Y_eq_Z hX hYZ hZ

theorem edOrderL_lt_two_pow_256 : edOrderL < 2 ^ 256 := by
  unfold edOrderL; decide

theorem edNatSmul_edOrderL_edBasepoint : edNatSmul edOrderL edBasepoint = edZero := by
  rw [← edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edOnCurve_edBasepoint]
  exact edSmul_edOrderL_edBasepoint

theorem edNatSmul_mul_edOrderL_edBasepoint (q : Nat) :
    edNatSmul (edOrderL * q) edBasepoint = edZero := by
  rw [Nat.mul_comm, edNatSmul_mul q edOrderL edOnCurve_edBasepoint,
      edNatSmul_edOrderL_edBasepoint, edNatSmul_edZero]

theorem edNatSmul_mod_edOrderL_edBasepoint (n : Nat) :
    edNatSmul (n % edOrderL) edBasepoint = edNatSmul n edBasepoint := by
  conv => rhs; rw [← Nat.div_add_mod n edOrderL]
  rw [edNatSmul_add (edOrderL * (n / edOrderL)) (n % edOrderL) edOnCurve_edBasepoint,
      edNatSmul_mul_edOrderL_edBasepoint,
      edZero_edAdd (edOnCurve_edNatSmul _ edOnCurve_edBasepoint)]

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards

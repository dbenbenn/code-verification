/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational -- proof-setup: allow-public-import

/-!
# Quadratic Character, Dual Complete Twist Curve $E_{\text{twist}}$, & Montgomery Dichotomy (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1`)

Pure `0-sorry` mathematical proofs for:
1. Quadratic character `FpIsSquare` on $\mathbb{F}_{p_{25519}}$ ($p \equiv 5 \pmod 8$),
   constructive square roots via $a^{(p+3)/8}$ / $\sqrt{-1}$, and Euler Legendre multiplicativity.
2. Dual complete twisted Edwards curve $E_{\text{twist}}(\mathbb{F}_p)$:
   $-x^2 + y^2 = 1 + d^{-1} x^2 y^2$ (`edDInv = fpInv edD`), completeness, abelian group laws,
   and extended homogeneous scalar multiplication `twSmul_eq_twNatSmul`.
3. Montgomery Curve25519 $u$-coordinate dichotomy (`mont_lift_dichotomy`): every nonzero
   $u \in \mathbb{F}_p$ lifts to a non-2-torsion point on either $E(\mathbb{F}_p)$ or
   $E_{\text{twist}}(\mathbb{F}_p)$, partitioned disjointly by `FpIsSquare (Fp.ofNat (montRHS u))`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1

open VerifiedLibraries.Common (
  p25519 modPowLoop modPow fpAdd fpSub fpNeg fpMul fpSq fpPow fpInv sqrtM1 edD EdPoint
  EdExtPoint edZero edExtZero edExtOfAffine edExtToAffine edOnCurve edNeg)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  p25519_pos fpAdd_lt fpNeg_lt fpMul_lt fpMul_eq_mul_mod fpSq_eq_pow2_mod fpSq_mod fpSub_self
  fpMul_zero zero_fpMul fpMul_one fpSq_one fpPow_lt pow_p25519_sub_one_mod fpInv_zero
  fpInv_one fpInv_eq_of_fpMul_eq_one fpSq_eq_fpSq_iff euler_nonsquare edD_nonsquare)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  Fp edOnCurve_x_lt edOnCurve_y_lt edOnCurve_fp_eq edOnCurve_of_fp_eq edOnCurve_edZero
  edExtToAffine_x_lt edExtToAffine_y_lt edExtToAffine_fp_x edExtToAffine_fp_y
  edExtToAffine_edExtZero edExtValid_edExtZero)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  montRHS edToMontU edToMontU_lt)

/-! ## 1. Quadratic Character (`FpIsSquare`) & Constructive Square Roots in `Fp` -/

theorem fp_ne_of_val_ne {a b : Fp} (h : a.val ≠ b.val) : a ≠ b :=
  fun hab => h (congrArg Fp.val hab)

/-- Quadratic residue predicate on `Fp` ($\mathbb{F}_{p_{25519}}$). -/
@[expose] def FpIsSquare (a : Fp) : Prop :=
  ∃ r : Fp, r * r = a

theorem fp_isSquare_zero : FpIsSquare 0 := ⟨0, by grind⟩
theorem fp_isSquare_one : FpIsSquare 1 := ⟨1, by grind⟩
theorem fp_isSquare_neg_one : FpIsSquare (-1) := ⟨Fp.ofNat sqrtM1, Fp.sqrtM1_sq⟩
theorem fp_isSquare_sq (x : Fp) : FpIsSquare (x * x) := ⟨x, rfl⟩

theorem fp_isSquare_mul {a b : Fp} (ha : FpIsSquare a) (hb : FpIsSquare b) :
    FpIsSquare (a * b) := by
  rcases ha with ⟨ra, rfl⟩
  rcases hb with ⟨rb, rfl⟩
  exact ⟨ra * rb, by grind⟩

theorem fp_isSquare_inv {a : Fp} (ha : FpIsSquare a) : FpIsSquare a⁻¹ := by
  rcases ha with ⟨ra, rfl⟩
  exact ⟨ra⁻¹, by grind⟩

theorem fp_not_isSquare_edD : ¬ FpIsSquare (Fp.ofNat edD) := Fp.edD_nonsquare

private theorem modPowLoop_eq_aux (fuel : Nat) :
    ∀ (base exp m acc : Nat), exp < 2 ^ fuel →
      modPowLoop fuel base exp m acc = (acc * base ^ exp) % m := by
  induction fuel with
  | zero =>
    intro base exp m acc hexp
    have h0 : exp = 0 := by omega
    subst h0; simp [modPowLoop]
  | succ fuel ih =>
    intro base exp m acc hexp; unfold modPowLoop
    by_cases h0 : exp = 0
    · subst h0; simp
    · have hne : (exp == 0) = false := Bool.eq_false_iff.mpr (fun heq => h0 (beq_iff_eq.mp heq))
      have hdiv : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hexp; omega
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hsq : ((base * base) % m) ^ (exp / 2) % m = base ^ (2 * (exp / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rcases Nat.mod_two_eq_zero_or_one exp with heven | hodd
      · have hmod : (exp % 2 == 1) = false := by rw [heven]; rfl
        have hexp_eq : 2 * (exp / 2) = exp := by omega
        rw [hmod]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod, hsq, hexp_eq, ← Nat.mul_mod]
      · have hmod : (exp % 2 == 1) = true := by rw [hodd]; rfl
        have hexp_eq : (2 * (exp / 2)).succ = exp := by omega
        rw [hmod]; simp only [↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod ((acc * base) % m), Nat.mod_mod, hsq, ← Nat.mul_mod,
            Nat.mul_assoc acc, ← Nat.pow_succ', hexp_eq]

private theorem fpPow_eq_pow_mod_aux (a e : Nat) (he : e < 2 ^ 256) :
    fpPow a e = a ^ e % p25519 := by
  unfold fpPow modPow
  rw [modPowLoop_eq_aux 256 (a % p25519) e p25519 1 he, Nat.one_mul, ← Nat.pow_mod a e p25519]

theorem fpPow_half_or {a : Nat} (ha : a % p25519 ≠ 0) :
    fpPow a ((p25519 - 1) / 2) = 1 ∨ fpPow a ((p25519 - 1) / 2) = p25519 - 1 := by
  have he_lt : (p25519 - 1) / 2 < 2 ^ 256 := by unfold p25519; decide
  have hexp : (p25519 - 1) / 2 * 2 = p25519 - 1 := by unfold p25519; decide
  have hsq : fpSq (fpPow a ((p25519 - 1) / 2)) = fpSq 1 := by
    rw [fpPow_eq_pow_mod_aux _ _ he_lt, fpSq_mod, fpSq_eq_pow2_mod, ← Nat.pow_mul, hexp,
        pow_p25519_sub_one_mod ha, fpSq_one]
  have hL_mod : fpPow a ((p25519 - 1) / 2) % p25519 = fpPow a ((p25519 - 1) / 2) :=
    Nat.mod_eq_of_lt (fpPow_lt _ _)
  rcases (fpSq_eq_fpSq_iff (fpPow a ((p25519 - 1) / 2)) 1).mp hsq with h1 | hneg1
  · left; rw [← hL_mod, h1]; unfold p25519; decide
  · right; rw [← hL_mod, hneg1]; unfold fpNeg p25519; decide

theorem fp_isSquare_of_euler_eq_one {a : Fp}
    (h : fpPow a.val ((p25519 - 1) / 2) = 1) : FpIsSquare a := by
  by_cases ha0 : a = 0
  · subst ha0; exact fp_isSquare_zero
  · let r0 := fpPow a.val ((p25519 + 3) / 8)
    let z := Fp.ofNat r0
    have he8_lt : (p25519 + 3) / 8 < 2 ^ 256 := by unfold p25519; decide
    have he2_lt : (p25519 - 1) / 2 < 2 ^ 256 := by unfold p25519; decide
    have hexp : (p25519 + 3) / 8 * (2 * 2) = (p25519 - 1) / 2 + 2 := by unfold p25519; decide
    have hr0_pow4 : fpSq (fpSq r0) = fpSq a.val := by
      dsimp only [r0]
      rw [fpSq_eq_pow2_mod, fpPow_eq_pow_mod_aux _ _ he8_lt, fpSq_mod, fpSq_eq_pow2_mod,
          ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.pow_mul, hexp,
          Nat.pow_add, ← Nat.mod_mul_mod, ← fpPow_eq_pow_mod_aux _ _ he2_lt, h,
          Nat.one_mul, fpSq_eq_pow2_mod]
    have hz4 : (z * z) * (z * z) = a * a := by
      have hfp := congrArg Fp.ofNat hr0_pow4
      simp only [Fp.ofNat_fpSq, Fp.ofNat_val] at hfp
      exact hfp
    have hor : z * z = a ∨ z * z = -a := by grind
    rcases hor with hpos | hneg
    · exact ⟨z, hpos⟩
    · refine ⟨z * Fp.ofNat sqrtM1, ?_⟩
      have hi := Fp.sqrtM1_sq
      grind

theorem fp_not_isSquare_of_euler_eq_sub_one {a : Fp}
    (h : fpPow a.val ((p25519 - 1) / 2) = p25519 - 1) : ¬ FpIsSquare a := by
  rintro ⟨r, hr⟩
  have hsq : fpSq r.val = a.val % p25519 := by
    rw [Nat.mod_eq_of_lt a.isLt]
    unfold fpSq
    exact congrArg Fp.val hr
  exact euler_nonsquare h ⟨r.val, hsq⟩

theorem fp_euler_eq_sub_one_of_not_isSquare {a : Fp} (hna : ¬ FpIsSquare a) :
    fpPow a.val ((p25519 - 1) / 2) = p25519 - 1 := by
  have ha0 : a ≠ 0 := by intro h0; subst h0; exact hna fp_isSquare_zero
  have hmod : a.val % p25519 ≠ 0 := by
    rw [Nat.mod_eq_of_lt a.isLt]
    intro hv0; exact ha0 (Fp.ext hv0)
  rcases fpPow_half_or hmod with h1 | hsub1
  · exact absurd (fp_isSquare_of_euler_eq_one h1) hna
  · exact hsub1

theorem fpPow_mul_half (a b : Nat) :
    fpPow (fpMul a b) ((p25519 - 1) / 2) =
      fpMul (fpPow a ((p25519 - 1) / 2)) (fpPow b ((p25519 - 1) / 2)) := by
  have he_lt : (p25519 - 1) / 2 < 2 ^ 256 := by unfold p25519; decide
  rw [fpPow_eq_pow_mod_aux _ _ he_lt, fpPow_eq_pow_mod_aux _ _ he_lt, fpPow_eq_pow_mod_aux _ _ he_lt,
      fpMul_eq_mul_mod, fpMul_eq_mul_mod, ← Nat.pow_mod, Nat.mul_pow,
      ← Nat.mul_mod_mod, ← Nat.mod_mul_mod]

theorem fp_isSquare_mul_of_not_isSquare {a b : Fp}
    (ha : ¬ FpIsSquare a) (hb : ¬ FpIsSquare b) : FpIsSquare (a * b) := by
  have ea := fp_euler_eq_sub_one_of_not_isSquare ha
  have eb := fp_euler_eq_sub_one_of_not_isSquare hb
  apply fp_isSquare_of_euler_eq_one
  have hv : (a * b).val = fpMul a.val b.val := rfl
  rw [hv, fpPow_mul_half, ea, eb]
  unfold fpMul p25519; decide

theorem fp_not_isSquare_inv {a : Fp} (ha : ¬ FpIsSquare a) : ¬ FpIsSquare a⁻¹ := by
  intro hinv
  have ha0 : a ≠ 0 := by intro h0; subst h0; exact ha fp_isSquare_zero
  rcases hinv with ⟨r, hr⟩
  apply ha
  refine ⟨r⁻¹, ?_⟩
  grind

theorem fp_isSquare_div_of_not_isSquare {a b : Fp}
    (ha : ¬ FpIsSquare a) (hb : ¬ FpIsSquare b) : FpIsSquare (a * b⁻¹) :=
  fp_isSquare_mul_of_not_isSquare ha (fp_not_isSquare_inv hb)

/-! ## 2. Dual Twisted Edwards Constant `edDInv = fpInv edD` & Curve $E_{\text{twist}}$ -/

/-- Inverse twisted Edwards curve constant $d^{-1} = -121666 / 121665 \bmod p_{25519}$ defining the
    dual complete twisted Edwards model $-x^2 + y^2 = 1 + d^{-1} x^2 y^2$ of $E'(\mathbb{F}_p)$. -/
@[expose] def edDInv : Nat :=
  29203323570479832313932222820853031755424015489030106335172286495629888845891

/-- $2 d^{-1} \bmod p_{25519}$ for extended point addition on $E_{\text{twist}}$. -/
@[expose] def edDInv2 : Nat :=
  fpAdd edDInv edDInv

theorem edDInv_lt : edDInv < p25519 := by unfold edDInv p25519; decide
theorem fpMul_edD_edDInv : fpMul edD edDInv = 1 := by unfold fpMul edD edDInv p25519; decide

theorem edDInv_eq_fpInv_edD : edDInv = fpInv edD := by
  rw [fpInv_eq_of_fpMul_eq_one fpMul_edD_edDInv, Nat.mod_eq_of_lt edDInv_lt]

theorem fp_edD_mul_edDInv : Fp.ofNat edD * Fp.ofNat edDInv = 1 := by
  have h := congrArg Fp.ofNat fpMul_edD_edDInv
  simpa using h

theorem fp_ofNat_edDInv_eq_inv : Fp.ofNat edDInv = (Fp.ofNat edD)⁻¹ := by
  have h := fp_edD_mul_edDInv
  have hd0 : Fp.ofNat edD ≠ 0 := by intro h0; exact Fp.edD_nonsquare ⟨0, by grind⟩
  grind

theorem fp_edDInv_nonsquare : ¬ FpIsSquare (Fp.ofNat edDInv) := by
  rw [fp_ofNat_edDInv_eq_inv]
  exact fp_not_isSquare_inv Fp.edD_nonsquare

theorem fp_ofNat_edDInv2 : Fp.ofNat edDInv2 = 2 * Fp.ofNat edDInv := by
  unfold edDInv2
  simp only [Fp.ofNat_fpAdd]
  grind

/-- On-curve predicate for the complete quadratic-twist Edwards curve
    $E_{\text{twist}}(\mathbb{F}_p) : -x^2 + y^2 \equiv 1 + d^{-1} x^2 y^2 \pmod{p_{25519}}$. -/
@[expose] def twOnCurve (P : EdPoint) : Bool :=
  P.x < p25519 && P.y < p25519 &&
  fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) ==
    fpAdd 1 (fpMul edDInv (fpMul (fpSq P.x) (fpSq P.y)))

/-- Complete affine addition on $E_{\text{twist}}(\mathbb{F}_p)$. -/
@[expose] def twAdd (P Q : EdPoint) : EdPoint :=
  let x1y2 := fpMul P.x Q.y
  let y1x2 := fpMul P.y Q.x
  let y1y2 := fpMul P.y Q.y
  let x1x2 := fpMul P.x Q.x
  let dxxyy := fpMul edDInv (fpMul x1x2 y1y2)
  let x3 := fpMul (fpAdd x1y2 y1x2) (fpInv (fpAdd 1 dxxyy))
  let y3 := fpMul (fpAdd y1y2 x1x2) (fpInv (fpSub 1 dxxyy))
  ⟨x3, y3⟩

abbrev twZero : EdPoint := edZero
abbrev twNeg (P : EdPoint) : EdPoint := edNeg P
@[expose] def twSub (P Q : EdPoint) : EdPoint := twAdd P (twNeg Q)

/-- Complete extended twisted Edwards addition on $E_{\text{twist}}(\mathbb{F}_p)$. -/
@[expose] def twExtAdd (P Q : EdExtPoint) : EdExtPoint :=
  let A := fpMul (fpSub P.Y P.X) (fpSub Q.Y Q.X)
  let B := fpMul (fpAdd P.Y P.X) (fpAdd Q.Y Q.X)
  let C := fpMul P.T (fpMul edDInv2 Q.T)
  let D := fpMul P.Z (fpAdd Q.Z Q.Z)
  let E := fpSub B A
  let F := fpSub D C
  let G := fpAdd D C
  let H := fpAdd B A
  ⟨fpMul E F, fpMul G H, fpMul F G, fpMul E H⟩

/-- Double-and-add extended scalar multiplication loop on $E_{\text{twist}}(\mathbb{F}_p)$. -/
@[expose] def twExtSmulLoop : Nat → Nat → EdExtPoint → EdExtPoint → EdExtPoint
  | 0, _, _, acc => acc
  | fuel + 1, n, P, acc =>
    if n == 0 then acc
    else
      let acc' := if n % 2 == 1 then twExtAdd acc P else acc
      twExtSmulLoop fuel (n / 2) (twExtAdd P P) acc'

/-- Fast 256-bit scalar multiplication on $E_{\text{twist}}(\mathbb{F}_p)$. -/
@[expose] def twSmul (n : Nat) (P : EdPoint) : EdPoint :=
  edExtToAffine (twExtSmulLoop 256 n (edExtOfAffine P) edExtZero)

/-- Unary Peano scalar multiplication on $E_{\text{twist}}(\mathbb{F}_p)$. -/
@[expose] def twNatSmul : Nat → EdPoint → EdPoint
  | 0, _ => twZero
  | n + 1, P => twAdd P (twNatSmul n P)

/-! ## 3. Completeness, Abelian Group Laws, & `twSmul_eq_twNatSmul` on $E_{\text{twist}}$ -/

theorem twOnCurve_iff (P : EdPoint) :
    twOnCurve P = true ↔
      P.x < p25519 ∧ P.y < p25519 ∧
      fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) =
        fpAdd 1 (fpMul edDInv (fpMul (fpSq P.x) (fpSq P.y))) := by
  unfold twOnCurve
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]

theorem twOnCurve_x_lt {P : EdPoint} (hP : twOnCurve P = true) : P.x < p25519 :=
  ((twOnCurve_iff P).mp hP).1

theorem twOnCurve_y_lt {P : EdPoint} (hP : twOnCurve P = true) : P.y < p25519 :=
  ((twOnCurve_iff P).mp hP).2.1

theorem twOnCurve_fp_eq {P : EdPoint} (hP : twOnCurve P = true) :
    -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y =
      1 + Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y)) := by
  have h := congrArg Fp.ofNat ((twOnCurve_iff P).mp hP).2.2
  simpa using h

theorem twOnCurve_of_fp_eq {P : EdPoint} (hx : P.x < p25519) (hy : P.y < p25519)
    (h : -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y =
      1 + Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y))) :
    twOnCurve P = true := by
  rw [twOnCurve_iff]
  refine ⟨hx, hy, Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (fpAdd_lt _ _) ?_⟩
  simpa using h

@[simp] theorem twOnCurve_twZero : twOnCurve twZero = true := by
  unfold twOnCurve twZero edZero fpAdd fpNeg fpSq fpMul edDInv p25519; decide

theorem twOnCurve_twNeg {P : EdPoint} (hP : twOnCurve P = true) :
    twOnCurve (twNeg P) = true := by
  have hfp := twOnCurve_fp_eq hP
  apply twOnCurve_of_fp_eq (fpNeg_lt P.x) (Nat.mod_lt P.y p25519_pos)
  simp only [twNeg, edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod]
  grind

private theorem tw_completeness_ring_id (d x1 y1 x2 y2 j : Fp)
    (h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)))
    (h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2)))
    (hd : 1 + d * ((x1 * x2) * (y1 * y2)) = 0)
    (hj : j * j = -1) :
    d * ((x1 * y1 * (x2 + j * y2)) * (x1 * y1 * (x2 + j * y2))) =
      (x1 - j * y1) * (x1 - j * y1) := by
  grind

private theorem tw_sq_div {d w v : Fp}
    (h : d * (w * w) = v * v) (hw : w ≠ 0) :
    (v * w⁻¹) * (v * w⁻¹) = d := by
  grind

theorem twAdd_fp_denom_add_ne_zero {P Q : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true) :
    (1 : Fp) + Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)) ≠ 0 := by
  intro hd
  let d := Fp.ofNat edDInv
  let x1 := Fp.ofNat P.x
  let y1 := Fp.ofNat P.y
  let x2 := Fp.ofNat Q.x
  let y2 := Fp.ofNat Q.y
  let i := Fp.ofNat sqrtM1
  have h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)) := twOnCurve_fp_eq hP
  have h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2)) := twOnCurve_fp_eq hQ
  have hi : i * i = -1 := Fp.sqrtM1_sq
  have hni : (-i) * (-i) = -1 := by grind
  have h_pos := tw_completeness_ring_id d x1 y1 x2 y2 i h1 h2 hd hi
  have h_neg := tw_completeness_ring_id d x1 y1 x2 y2 (-i) h1 h2 hd hni
  by_cases h_diff : x1 - i * y1 = 0
  · by_cases h_sum : x1 - (-i) * y1 = 0
    · have h2ne : (2 : Fp) ≠ 0 := Fp.two_ne_zero
      have h10 : (1 : Fp) = 0 := by grind
      exact absurd h10.symm (fp_ne_of_val_ne (by change 0 ≠ 1 % p25519; unfold p25519; decide))
    · have hw_ne : x1 * y1 * (x2 + (-i) * y2) ≠ 0 := by grind
      exact fp_edDInv_nonsquare ⟨_, tw_sq_div h_neg hw_ne⟩
  · have hw_ne : x1 * y1 * (x2 + i * y2) ≠ 0 := by grind
    exact fp_edDInv_nonsquare ⟨_, tw_sq_div h_pos hw_ne⟩

theorem twAdd_fp_denom_sub_ne_zero {P Q : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true) :
    (1 : Fp) - Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)) ≠ 0 := by
  have hneg := twAdd_fp_denom_add_ne_zero (twOnCurve_twNeg hP) hQ
  intro h0
  apply hneg
  simp only [twNeg, edNeg, Fp.ofNat_fpNeg, Fp.ofNat_mod] at hneg ⊢
  grind

theorem twAdd_x_lt (P Q : EdPoint) : (twAdd P Q).x < p25519 := fpMul_lt _ _
theorem twAdd_y_lt (P Q : EdPoint) : (twAdd P Q).y < p25519 := fpMul_lt _ _

theorem twAdd_fp_x (P Q : EdPoint) :
    Fp.ofNat (twAdd P Q).x =
      (Fp.ofNat P.x * Fp.ofNat Q.y + Fp.ofNat P.y * Fp.ofNat Q.x) *
        (1 + Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ := by
  unfold twAdd; simp

theorem twAdd_fp_y (P Q : EdPoint) :
    Fp.ofNat (twAdd P Q).y =
      (Fp.ofNat P.y * Fp.ofNat Q.y + Fp.ofNat P.x * Fp.ofNat Q.x) *
        (1 - Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat Q.x) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ := by
  unfold twAdd; simp

private theorem twAdd_onCurve_ring (d x1 y1 x2 y2 : Fp)
    (h1 : -(x1 * x1) + y1 * y1 = 1 + d * ((x1 * x1) * (y1 * y1)))
    (h2 : -(x2 * x2) + y2 * y2 = 1 + d * ((x2 * x2) * (y2 * y2))) :
    let u := x1 * y2 + y1 * x2
    let v := y1 * y2 + x1 * x2
    let dp := 1 + d * ((x1 * x2) * (y1 * y2))
    let dm := 1 - d * ((x1 * x2) * (y1 * y2));
    -((u * dm) * (u * dm)) + (v * dp) * (v * dp) =
      (dp * dm) * (dp * dm) + d * ((u * u) * (v * v)) := by
  grind

theorem twOnCurve_twAdd {P Q : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true) :
    twOnCurve (twAdd P Q) = true := by
  apply twOnCurve_of_fp_eq (twAdd_x_lt P Q) (twAdd_y_lt P Q)
  have h1 := twOnCurve_fp_eq hP
  have h2 := twOnCurve_fp_eq hQ
  have hdp := twAdd_fp_denom_add_ne_zero hP hQ
  have hdm := twAdd_fp_denom_sub_ne_zero hP hQ
  have hring := twAdd_onCurve_ring (Fp.ofNat edDInv) (Fp.ofNat P.x) (Fp.ofNat P.y)
    (Fp.ofNat Q.x) (Fp.ofNat Q.y) h1 h2
  dsimp only at hring
  rw [twAdd_fp_x, twAdd_fp_y]
  grind

theorem twOnCurve_twSub {P Q : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true) :
    twOnCurve (twSub P Q) = true :=
  twOnCurve_twAdd hP (twOnCurve_twNeg hQ)

theorem twAdd_comm (P Q : EdPoint) : twAdd P Q = twAdd Q P := by
  ext
  · apply Fp.eq_of_ofNat_eq (twAdd_x_lt _ _) (twAdd_x_lt _ _)
    rw [twAdd_fp_x, twAdd_fp_x]; grind
  · apply Fp.eq_of_ofNat_eq (twAdd_y_lt _ _) (twAdd_y_lt _ _)
    rw [twAdd_fp_y, twAdd_fp_y]; grind

@[simp] theorem twAdd_twZero {P : EdPoint} (hP : twOnCurve P = true) :
    twAdd P twZero = P := by
  ext
  · apply Fp.eq_of_ofNat_eq (twAdd_x_lt _ _) (twOnCurve_x_lt hP)
    rw [twAdd_fp_x]; simp only [edZero, Fp.ofNat_zero, Fp.ofNat_one]; grind
  · apply Fp.eq_of_ofNat_eq (twAdd_y_lt _ _) (twOnCurve_y_lt hP)
    rw [twAdd_fp_y]; simp only [edZero, Fp.ofNat_zero, Fp.ofNat_one]; grind

@[simp] theorem twZero_twAdd {P : EdPoint} (hP : twOnCurve P = true) :
    twAdd twZero P = P := by
  rw [twAdd_comm, twAdd_twZero hP]

@[simp] theorem twAdd_twNeg_self {P : EdPoint} (hP : twOnCurve P = true) :
    twAdd P (twNeg P) = twZero := by
  have hfp := twOnCurve_fp_eq hP
  have hdm := twAdd_fp_denom_sub_ne_zero hP (twOnCurve_twNeg hP)
  ext
  · apply Fp.eq_of_ofNat_eq (twAdd_x_lt _ _) (edOnCurve_x_lt edOnCurve_edZero)
    rw [twAdd_fp_x]; simp only [twNeg, edNeg, edZero, Fp.ofNat_fpNeg, Fp.ofNat_mod, Fp.ofNat_zero]
    grind
  · apply Fp.eq_of_ofNat_eq (twAdd_y_lt _ _) (edOnCurve_y_lt edOnCurve_edZero)
    rw [twAdd_fp_y]
    simp only [twNeg, edNeg, edZero, Fp.ofNat_fpNeg, Fp.ofNat_mod, Fp.ofNat_one] at hdm ⊢
    grind

private theorem twAdd_assoc_x_ring (d x1 y1 x2 y2 x3 y3 : Fp)
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

private theorem twAdd_assoc_y_ring (d x1 y1 x2 y2 x3 y3 : Fp)
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

private theorem twAdd_assoc_x_clear (d u12 v12 dp12 dm12 u23 v23 dp23 dm23 x1 y1 x3 y3 : Fp)
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

private theorem twAdd_assoc_y_clear (d u12 v12 dp12 dm12 u23 v23 dp23 dm23 x1 y1 x3 y3 : Fp)
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

theorem twAdd_assoc {P Q R : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true) (hR : twOnCurve R = true) :
    twAdd (twAdd P Q) R = twAdd P (twAdd Q R) := by
  have hPQ : twOnCurve (twAdd P Q) = true := twOnCurve_twAdd hP hQ
  have hQR : twOnCurve (twAdd Q R) = true := twOnCurve_twAdd hQ hR
  have h1 : Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y)) =
      -(Fp.ofNat P.x * Fp.ofNat P.x) + Fp.ofNat P.y * Fp.ofNat P.y - 1 := by
    have := twOnCurve_fp_eq hP; grind
  have h2 : Fp.ofNat edDInv * ((Fp.ofNat Q.x * Fp.ofNat Q.x) * (Fp.ofNat Q.y * Fp.ofNat Q.y)) =
      -(Fp.ofNat Q.x * Fp.ofNat Q.x) + Fp.ofNat Q.y * Fp.ofNat Q.y - 1 := by
    have := twOnCurve_fp_eq hQ; grind
  have h3 : Fp.ofNat edDInv * ((Fp.ofNat R.x * Fp.ofNat R.x) * (Fp.ofNat R.y * Fp.ofNat R.y)) =
      -(Fp.ofNat R.x * Fp.ofNat R.x) + Fp.ofNat R.y * Fp.ofNat R.y - 1 := by
    have := twOnCurve_fp_eq hR; grind
  have hdp12 := twAdd_fp_denom_add_ne_zero hP hQ
  have hdm12 := twAdd_fp_denom_sub_ne_zero hP hQ
  have hdp23 := twAdd_fp_denom_add_ne_zero hQ hR
  have hdm23 := twAdd_fp_denom_sub_ne_zero hQ hR
  have hdp12_3 := twAdd_fp_denom_add_ne_zero hPQ hR
  have hdm12_3 := twAdd_fp_denom_sub_ne_zero hPQ hR
  have hdp1_23 := twAdd_fp_denom_add_ne_zero hP hQR
  have hdm1_23 := twAdd_fp_denom_sub_ne_zero hP hQR
  rw [twAdd_fp_x P Q, twAdd_fp_y P Q] at hdp12_3 hdm12_3
  rw [twAdd_fp_x Q R, twAdd_fp_y Q R] at hdp1_23 hdm1_23
  ext
  · apply Fp.eq_of_ofNat_eq (twAdd_x_lt _ _) (twAdd_x_lt _ _)
    have hx_ring := twAdd_assoc_x_ring (Fp.ofNat edDInv)
      (Fp.ofNat P.x) (Fp.ofNat P.y) (Fp.ofNat Q.x) (Fp.ofNat Q.y) (Fp.ofNat R.x) (Fp.ofNat R.y)
      h1 h2 h3
    rw [twAdd_fp_x (twAdd P Q) R, twAdd_fp_x P (twAdd Q R),
        twAdd_fp_x P Q, twAdd_fp_y P Q, twAdd_fp_x Q R, twAdd_fp_y Q R]
    exact twAdd_assoc_x_clear _ _ _ _ _ _ _ _ _ _ _ _ _
      hdp12 hdm12 hdp23 hdm23 hdp12_3 hdp1_23 hx_ring
  · apply Fp.eq_of_ofNat_eq (twAdd_y_lt _ _) (twAdd_y_lt _ _)
    have hy_ring := twAdd_assoc_y_ring (Fp.ofNat edDInv)
      (Fp.ofNat P.x) (Fp.ofNat P.y) (Fp.ofNat Q.x) (Fp.ofNat Q.y) (Fp.ofNat R.x) (Fp.ofNat R.y)
      h1 h2 h3
    rw [twAdd_fp_y (twAdd P Q) R, twAdd_fp_y P (twAdd Q R),
        twAdd_fp_x P Q, twAdd_fp_y P Q, twAdd_fp_x Q R, twAdd_fp_y Q R]
    exact twAdd_assoc_y_clear _ _ _ _ _ _ _ _ _ _ _ _ _
      hdp12 hdm12 hdp23 hdm23 hdm12_3 hdm1_23 hy_ring

theorem twAdd_twSub_cancel {P Q : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true) :
    twSub (twAdd P Q) Q = P := by
  unfold twSub
  rw [twAdd_assoc hP hQ (twOnCurve_twNeg hQ), twAdd_twNeg_self hQ, twAdd_twZero hP]

@[simp] theorem twNatSmul_zero (P : EdPoint) : twNatSmul 0 P = twZero := rfl
@[simp] theorem twNatSmul_succ (n : Nat) (P : EdPoint) :
    twNatSmul (n + 1) P = twAdd P (twNatSmul n P) := rfl

theorem twOnCurve_twNatSmul (n : Nat) {P : EdPoint} (hP : twOnCurve P = true) :
    twOnCurve (twNatSmul n P) = true := by
  induction n with
  | zero => exact twOnCurve_twZero
  | succ n ih => exact twOnCurve_twAdd hP ih

@[simp] theorem twNatSmul_twZero (n : Nat) : twNatSmul n twZero = twZero := by
  induction n with
  | zero => rfl
  | succ n ih => rw [twNatSmul_succ, ih, twAdd_twZero twOnCurve_twZero]

theorem twNatSmul_one {P : EdPoint} (hP : twOnCurve P = true) : twNatSmul 1 P = P := by
  rw [twNatSmul_succ, twNatSmul_zero, twAdd_twZero hP]

theorem twNatSmul_add (m n : Nat) {P : EdPoint} (hP : twOnCurve P = true) :
    twNatSmul (m + n) P = twAdd (twNatSmul m P) (twNatSmul n P) := by
  induction m with
  | zero => simp [twZero_twAdd (twOnCurve_twNatSmul n hP)]
  | succ m ih =>
    rw [Nat.succ_add, twNatSmul_succ, twNatSmul_succ, ih,
        twAdd_assoc hP (twOnCurve_twNatSmul m hP) (twOnCurve_twNatSmul n hP)]

theorem twNatSmul_two {P : EdPoint} (hP : twOnCurve P = true) :
    twNatSmul 2 P = twAdd P P := by
  rw [show (2 : Nat) = 1 + 1 from rfl, twNatSmul_add 1 1 hP, twNatSmul_one hP]

theorem twNatSmul_mul (m n : Nat) {P : EdPoint} (hP : twOnCurve P = true) :
    twNatSmul (m * n) P = twNatSmul m (twNatSmul n P) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Nat.add_comm (m * n) n, twNatSmul_add n (m * n) hP, ih, twNatSmul_succ]

/-- Extended homogeneous validity on $E_{\text{twist}}$. -/
structure TwExtValid (P : EdExtPoint) : Prop where
  z_ne_zero : Fp.ofNat P.Z ≠ 0
  tz_eq_xy : Fp.ofNat P.T * Fp.ofNat P.Z = Fp.ofNat P.X * Fp.ofNat P.Y
  on_curve : twOnCurve (edExtToAffine P) = true

theorem twExtValid_edExtZero : TwExtValid edExtZero where
  z_ne_zero := edExtValid_edExtZero.z_ne_zero
  tz_eq_xy := edExtValid_edExtZero.tz_eq_xy
  on_curve := by rw [edExtToAffine_edExtZero]; exact twOnCurve_twZero

theorem twExtToAffine_edExtOfAffine {P : EdPoint} (hP : twOnCurve P = true) :
    edExtToAffine (edExtOfAffine P) = P := by
  ext
  · dsimp only [edExtOfAffine, edExtToAffine]
    rw [fpInv_one, fpMul_one, Nat.mod_mod, Nat.mod_eq_of_lt (twOnCurve_x_lt hP)]
  · dsimp only [edExtOfAffine, edExtToAffine]
    rw [fpInv_one, fpMul_one, Nat.mod_mod, Nat.mod_eq_of_lt (twOnCurve_y_lt hP)]

theorem twExtValid_edExtOfAffine {P : EdPoint} (hP : twOnCurve P = true) :
    TwExtValid (edExtOfAffine P) where
  z_ne_zero := edExtValid_edExtZero.z_ne_zero
  tz_eq_xy := by unfold edExtOfAffine; simp; grind
  on_curve := by rw [twExtToAffine_edExtOfAffine hP]; exact hP

private theorem twExtAdd_z_ne_zero_ring (d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2 : Fp)
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

private theorem twExtAdd_x_ring (d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2 : Fp)
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
  have hFG := twExtAdd_z_ne_zero_ring d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2
    h2 hZ1 hZ2 hT1 hT2 hx1 hy1 hx2 hy2 hdp hdm
  grind

private theorem twExtAdd_y_ring (d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2 : Fp)
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
  have hFG := twExtAdd_z_ne_zero_ring d X1 Y1 Z1 T1 X2 Y2 Z2 T2 x1 y1 x2 y2
    h2 hZ1 hZ2 hT1 hT2 hx1 hy1 hx2 hy2 hdp hdm
  grind

theorem twExtAdd_toAffine {P Q : EdExtPoint}
    (hP : TwExtValid P) (hQ : TwExtValid Q) :
    edExtToAffine (twExtAdd P Q) = twAdd (edExtToAffine P) (edExtToAffine Q) := by
  have hdp := twAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
  have hdm := twAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
  ext
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_x_lt _) (twAdd_x_lt _ _)
    rw [edExtToAffine_fp_x, twAdd_fp_x]
    unfold twExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, fp_ofNat_edDInv2]
    exact twExtAdd_x_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hQ.z_ne_zero hP.tz_eq_xy hQ.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      (edExtToAffine_fp_x Q) (edExtToAffine_fp_y Q) hdp hdm
  · apply Fp.eq_of_ofNat_eq (edExtToAffine_y_lt _) (twAdd_y_lt _ _)
    rw [edExtToAffine_fp_y, twAdd_fp_y]
    unfold twExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, fp_ofNat_edDInv2]
    exact twExtAdd_y_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hQ.z_ne_zero hP.tz_eq_xy hQ.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      (edExtToAffine_fp_x Q) (edExtToAffine_fp_y Q) hdp hdm

theorem twExtValid_twExtAdd {P Q : EdExtPoint}
    (hP : TwExtValid P) (hQ : TwExtValid Q) :
    TwExtValid (twExtAdd P Q) where
  z_ne_zero := by
    have hdp := twAdd_fp_denom_add_ne_zero hP.on_curve hQ.on_curve
    have hdm := twAdd_fp_denom_sub_ne_zero hP.on_curve hQ.on_curve
    unfold twExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, fp_ofNat_edDInv2]
    exact twExtAdd_z_ne_zero_ring _ _ _ _ _ _ _ _ _ _ _ _ _
      Fp.two_ne_zero hP.z_ne_zero hQ.z_ne_zero hP.tz_eq_xy hQ.tz_eq_xy
      (edExtToAffine_fp_x P) (edExtToAffine_fp_y P)
      (edExtToAffine_fp_x Q) (edExtToAffine_fp_y Q) hdp hdm
  tz_eq_xy := by
    unfold twExtAdd
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub]
    grind
  on_curve := by
    rw [twExtAdd_toAffine hP hQ]
    exact twOnCurve_twAdd hP.on_curve hQ.on_curve

theorem twExtSmulLoop_spec (fuel n : Nat) (P acc : EdExtPoint)
    (hn : n < 2 ^ fuel) (hP : TwExtValid P) (hacc : TwExtValid acc) :
    TwExtValid (twExtSmulLoop fuel n P acc) ∧
    edExtToAffine (twExtSmulLoop fuel n P acc) =
      twAdd (edExtToAffine acc) (twNatSmul n (edExtToAffine P)) := by
  induction fuel generalizing n P acc with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    refine ⟨hacc, ?_⟩
    rw [twExtSmulLoop, twNatSmul_zero, twAdd_twZero hacc.on_curve]
  | succ fuel ih =>
    unfold twExtSmulLoop
    by_cases h0 : n == 0
    · simp only [h0, ↓reduceIte]
      have hn0 : n = 0 := beq_iff_eq.mp h0
      subst hn0
      refine ⟨hacc, ?_⟩
      rw [twNatSmul_zero, twAdd_twZero hacc.on_curve]
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      have hn_div : n / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hn; omega
      have hPP : TwExtValid (twExtAdd P P) := twExtValid_twExtAdd hP hP
      have hacc' : TwExtValid (if n % 2 == 1 then twExtAdd acc P else acc) := by
        split
        · exact twExtValid_twExtAdd hacc hP
        · exact hacc
      obtain ⟨hvalid, heq⟩ := ih (n / 2) (twExtAdd P P)
        (if n % 2 == 1 then twExtAdd acc P else acc) hn_div hPP hacc'
      refine ⟨hvalid, ?_⟩
      rw [heq, twExtAdd_toAffine hP hP, ← twNatSmul_two hP.on_curve,
          ← twNatSmul_mul (n / 2) 2 hP.on_curve]
      by_cases hodd : n % 2 == 1
      · simp only [hodd, ↓reduceIte]
        have hrem : n % 2 = 1 := beq_iff_eq.mp hodd
        rw [twExtAdd_toAffine hacc hP,
            twAdd_assoc hacc.on_curve hP.on_curve (twOnCurve_twNatSmul _ hP.on_curve),
            ← twNatSmul_succ,
            show n / 2 * 2 + 1 = n by omega]
      · simp only [hodd, Bool.false_eq_true, ↓reduceIte]
        have hrem : n % 2 = 0 := by
          have : n % 2 ≠ 1 := by intro h; exact hodd (beq_iff_eq.mpr h)
          omega
        rw [show n / 2 * 2 = n by omega]

theorem twSmul_eq_twNatSmul {n : Nat} {P : EdPoint}
    (hn : n < 2 ^ 256) (hP : twOnCurve P = true) :
    twSmul n P = twNatSmul n P := by
  unfold twSmul
  obtain ⟨_, heq⟩ := twExtSmulLoop_spec 256 n (edExtOfAffine P) edExtZero
    hn (twExtValid_edExtOfAffine hP) twExtValid_edExtZero
  rw [heq, edExtToAffine_edExtZero, twExtToAffine_edExtOfAffine hP,
      twZero_twAdd (twOnCurve_twNatSmul n hP)]

/-! ## 4. Montgomery $u$-Coordinate Dichotomy ($E(\mathbb{F}_p)$ vs $E_{\text{twist}}(\mathbb{F}_p)$) -/

/-- Birational Kummer map $u = (y + 1) \cdot (y - 1)^{-1} \bmod p_{25519}$ from $E_{\text{twist}}(\mathbb{F}_p)$
    (maps both $(0, 1)$ and $(0, p - 1)$ to $0$). -/
@[expose] def twToMontU (P : EdPoint) : Nat :=
  fpMul (fpAdd P.y 1) (fpInv (fpSub P.y 1))

theorem twToMontU_lt (P : EdPoint) : twToMontU P < p25519 := fpMul_lt _ _

private theorem fp_edD_num_rel : (121666 : Fp) * Fp.ofNat edD = -121665 := by
  ext; change fpMul 121666 edD = fpNeg 121665; unfold fpMul fpNeg edD p25519; decide

private theorem fp_edDInv_num_rel : (121665 : Fp) * Fp.ofNat edDInv = -121666 := by
  ext; change fpMul 121665 edDInv = fpNeg 121666; unfold fpMul fpNeg edDInv p25519; decide

private theorem fp_ofNat_486662 : Fp.ofNat 486662 = (486662 : Fp) := by
  ext; unfold Fp.ofNat p25519; decide

set_option maxRecDepth 20000 in
private theorem fp_isSquare_neg_486664 : FpIsSquare (-(486664 : Fp)) := by
  apply fp_isSquare_of_euler_eq_one
  have hv : (-(486664 : Fp)).val = fpNeg 486664 := by unfold fpNeg p25519; decide
  rw [hv]; unfold fpPow modPow fpNeg p25519; decide

set_option maxRecDepth 20000 in
private theorem fp_not_isSquare_neg_486660 : ¬ FpIsSquare (-(486660 : Fp)) := by
  apply fp_not_isSquare_of_euler_eq_sub_one
  have hv : (-(486660 : Fp)).val = fpNeg 486660 := by unfold fpNeg p25519; decide
  rw [hv]; unfold fpPow modPow fpNeg p25519; decide

set_option maxRecDepth 20000 in
private theorem fp_not_isSquare_disc : ¬ FpIsSquare (59209975560 : Fp) := by
  apply fp_not_isSquare_of_euler_eq_sub_one
  have hv : (59209975560 : Fp).val = 59209975560 := by decide
  rw [hv]; unfold fpPow modPow p25519; decide

theorem fp_mont_quad_ne_zero (u : Fp) : u * u + 486662 * u + 1 ≠ 0 := by
  intro h0
  have hsq : (u + 243331) * (u + 243331) = 59209975560 := by grind
  exact fp_not_isSquare_disc ⟨u + 243331, hsq⟩

theorem fp_ofNat_montRHS (u : Nat) :
    Fp.ofNat (montRHS u) =
      Fp.ofNat u * Fp.ofNat u * Fp.ofNat u + 486662 * (Fp.ofNat u * Fp.ofNat u) + Fp.ofNat u := by
  unfold montRHS
  simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpSq, fp_ofNat_486662]

theorem fp_montRHS_ne_zero_of_ne_zero {u : Nat} (hu : Fp.ofNat u ≠ 0) :
    Fp.ofNat (montRHS u) ≠ 0 := by
  rw [fp_ofNat_montRHS]
  have hq := fp_mont_quad_ne_zero (Fp.ofNat u)
  have hfac : Fp.ofNat u * Fp.ofNat u * Fp.ofNat u + 486662 * (Fp.ofNat u * Fp.ofNat u) + Fp.ofNat u =
      Fp.ofNat u * (Fp.ofNat u * Fp.ofNat u + 486662 * Fp.ofNat u + 1) := by grind
  rw [hfac]
  exact Fp.mul_ne_zero hu hq

theorem twOnCurve_order2 : twOnCurve ⟨0, p25519 - 1⟩ = true := by
  unfold twOnCurve fpAdd fpNeg fpSq fpMul edDInv p25519; decide

theorem edOnCurve_x_eq_zero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    P.x = 0 ↔ (P = edZero ∨ P = ⟨0, p25519 - 1⟩) := by
  constructor
  · intro hx0
    have hfp := edOnCurve_fp_eq hP
    have hx_fp : Fp.ofNat P.x = 0 := by rw [hx0, Fp.ofNat_zero]
    have hy_sq : Fp.ofNat P.y * Fp.ofNat P.y = 1 := by grind
    have hy_or : Fp.ofNat P.y = 1 ∨ Fp.ofNat P.y = -1 := by grind
    have hy_lt := edOnCurve_y_lt hP
    rcases hy_or with hy1 | hyn1
    · left; ext
      · exact hx0
      · exact Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide) hy1
    · right; ext
      · exact hx0
      · apply Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide)
        have hm1 : (-1 : Fp) = Fp.ofNat (p25519 - 1) := by ext; unfold Fp.ofNat p25519; decide
        exact hyn1.trans hm1
  · rintro (rfl | rfl) <;> rfl

theorem twOnCurve_x_eq_zero_iff {P : EdPoint} (hP : twOnCurve P = true) :
    P.x = 0 ↔ (P = edZero ∨ P = ⟨0, p25519 - 1⟩) := by
  constructor
  · intro hx0
    have hfp := twOnCurve_fp_eq hP
    have hx_fp : Fp.ofNat P.x = 0 := by rw [hx0, Fp.ofNat_zero]
    have hy_sq : Fp.ofNat P.y * Fp.ofNat P.y = 1 := by grind
    have hy_or : Fp.ofNat P.y = 1 ∨ Fp.ofNat P.y = -1 := by grind
    have hy_lt := twOnCurve_y_lt hP
    rcases hy_or with hy1 | hyn1
    · left; ext
      · exact hx0
      · exact Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide) hy1
    · right; ext
      · exact hx0
      · apply Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide)
        have hm1 : (-1 : Fp) = Fp.ofNat (p25519 - 1) := by ext; unfold Fp.ofNat p25519; decide
        exact hyn1.trans hm1
  · rintro (rfl | rfl) <;> rfl

theorem edToMontU_eq_zero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edToMontU P = 0 ↔ P.x = 0 := by
  rw [edOnCurve_x_eq_zero_iff hP]
  constructor
  · intro hu0
    have hfp : (1 + Fp.ofNat P.y) * (1 - Fp.ofNat P.y)⁻¹ = 0 := by
      have := congrArg Fp.ofNat hu0
      simpa [edToMontU] using this
    have hy_lt := edOnCurve_y_lt hP
    by_cases h1 : (1 : Fp) - Fp.ofNat P.y = 0
    · left
      have hy1 : Fp.ofNat P.y = 1 := by grind
      have hy_eq : P.y = 1 := Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide) hy1
      have hP_zero : P.x = 0 := by
        have hc := edOnCurve_fp_eq hP
        have hsq : Fp.ofNat P.x * Fp.ofNat P.x = 0 := by
          have hd_ne : (1 : Fp) + Fp.ofNat edD ≠ 0 := by
            intro hd0
            exact Fp.edD_nonsquare ⟨Fp.ofNat sqrtM1, by have := Fp.sqrtM1_sq; grind⟩
          grind
        have hx0 : Fp.ofNat P.x = 0 := by grind
        exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos hx0
      ext; exact hP_zero; exact hy_eq
    · right
      have hy_m1 : Fp.ofNat P.y = -1 := by grind
      have hm1 : (-1 : Fp) = Fp.ofNat (p25519 - 1) := by ext; unfold Fp.ofNat p25519; decide
      have hy_eq : P.y = p25519 - 1 :=
        Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide) (hy_m1.trans hm1)
      have hP_zero : P.x = 0 := by
        have hc := edOnCurve_fp_eq hP
        have hsq : Fp.ofNat P.x * Fp.ofNat P.x = 0 := by
          have hd_ne : (1 : Fp) + Fp.ofNat edD ≠ 0 := by
            intro hd0
            exact Fp.edD_nonsquare ⟨Fp.ofNat sqrtM1, by have := Fp.sqrtM1_sq; grind⟩
          grind
        have hx0 : Fp.ofNat P.x = 0 := by grind
        exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos hx0
      ext; exact hP_zero; exact hy_eq
  · rintro (rfl | rfl)
    · unfold edToMontU edZero; rw [fpSub_self, fpInv_zero, fpMul_zero]
    · have h0 : fpAdd 1 (p25519 - 1) = 0 := by unfold fpAdd p25519; decide
      unfold edToMontU; dsimp only; rw [h0, zero_fpMul]

theorem twToMontU_eq_zero_iff {P : EdPoint} (hP : twOnCurve P = true) :
    twToMontU P = 0 ↔ P.x = 0 := by
  rw [twOnCurve_x_eq_zero_iff hP]
  constructor
  · intro hu0
    have hfp : (Fp.ofNat P.y + 1) * (Fp.ofNat P.y - 1)⁻¹ = 0 := by
      have := congrArg Fp.ofNat hu0
      simpa [twToMontU] using this
    have hy_lt := twOnCurve_y_lt hP
    by_cases h1 : Fp.ofNat P.y - 1 = 0
    · left
      have hy1 : Fp.ofNat P.y = 1 := by grind
      have hy_eq : P.y = 1 := Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide) hy1
      have hP_zero : P.x = 0 := by
        have hc := twOnCurve_fp_eq hP
        have hsq : Fp.ofNat P.x * Fp.ofNat P.x = 0 := by
          have hd_ne : (1 : Fp) + Fp.ofNat edDInv ≠ 0 := by
            intro hd0
            exact fp_edDInv_nonsquare ⟨Fp.ofNat sqrtM1, by have := Fp.sqrtM1_sq; grind⟩
          grind
        have hx0 : Fp.ofNat P.x = 0 := by grind
        exact Fp.eq_of_ofNat_eq (twOnCurve_x_lt hP) p25519_pos hx0
      ext; exact hP_zero; exact hy_eq
    · right
      have hy_m1 : Fp.ofNat P.y = -1 := by grind
      have hm1 : (-1 : Fp) = Fp.ofNat (p25519 - 1) := by ext; unfold Fp.ofNat p25519; decide
      have hy_eq : P.y = p25519 - 1 :=
        Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide) (hy_m1.trans hm1)
      have hP_zero : P.x = 0 := by
        have hc := twOnCurve_fp_eq hP
        have hsq : Fp.ofNat P.x * Fp.ofNat P.x = 0 := by
          have hd_ne : (1 : Fp) + Fp.ofNat edDInv ≠ 0 := by
            intro hd0
            exact fp_edDInv_nonsquare ⟨Fp.ofNat sqrtM1, by have := Fp.sqrtM1_sq; grind⟩
          grind
        have hx0 : Fp.ofNat P.x = 0 := by grind
        exact Fp.eq_of_ofNat_eq (twOnCurve_x_lt hP) p25519_pos hx0
      ext; exact hP_zero; exact hy_eq
  · rintro (rfl | rfl)
    · unfold twToMontU edZero; rw [fpSub_self, fpInv_zero, fpMul_zero]
    · have h0 : fpAdd (p25519 - 1) 1 = 0 := by unfold fpAdd p25519; decide
      unfold twToMontU; dsimp only; rw [h0, zero_fpMul]

private theorem mont_ed_birational_id (d u y : Fp)
    (hd : 121666 * d = -121665) (hy : y * (u + 1) = u - 1) (hup1 : u + 1 ≠ 0) :
    (y * y - 1) * (u * u * u + 486662 * (u * u) + u) =
      (-(486664 : Fp) * (u * u)) * (1 + d * (y * y)) := by
  grind

private theorem mont_tw_birational_id (di u y : Fp)
    (hdi : 121665 * di = -121666) (hy : y * (u - 1) = u + 1) (hum1 : u - 1 ≠ 0) :
    (y * y - 1) * (u * u * u + 486662 * (u * u) + u) =
      (-(486660 : Fp) * (u * u)) * (1 + di * (y * y)) := by
  grind

private theorem mont_ed_rhs_factor (d u x y : Fp)
    (h2 : (2 : Fp) ≠ 0) (hd : 121666 * d = -121665)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hu : u = (1 + y) * (1 - y)⁻¹) (h1my : 1 - y ≠ 0) (hx : x ≠ 0) :
    u * u * u + 486662 * (u * u) + u = (-(486664 : Fp)) * ((u * x⁻¹) * (u * x⁻¹)) := by
  have hup1 : u + 1 ≠ 0 := by grind
  have hy_rel : y * (u + 1) = u - 1 := by grind
  have hid := mont_ed_birational_id d u y hd hy_rel hup1
  grind

private theorem mont_tw_rhs_factor (di u x y : Fp)
    (h2 : (2 : Fp) ≠ 0) (hdi : 121665 * di = -121666)
    (hc : -(x * x) + y * y = 1 + di * ((x * x) * (y * y)))
    (hu : u = (y + 1) * (y - 1)⁻¹) (hym1 : y - 1 ≠ 0) (hu0 : u ≠ 0)
    (h1dy2 : 1 + di * (y * y) ≠ 0) :
    (-(486660 : Fp)) = (u * u * u + 486662 * (u * u) + u) * ((x * u⁻¹) * (x * u⁻¹)) := by
  have hum1 : u - 1 ≠ 0 := by grind
  have hy_rel : y * (u - 1) = u + 1 := by grind
  have hid := mont_tw_birational_id di u y hdi hy_rel hum1
  grind

/-- Every non-2-torsion point on $E(\mathbb{F}_p)$ maps to a $u \in (0, p)$ with square `montRHS u`. -/
theorem edOnCurve_montRHS_isSquare {P : EdPoint}
    (hP : edOnCurve P = true) (hx : P.x ≠ 0) :
    FpIsSquare (Fp.ofNat (montRHS (edToMontU P))) := by
  have hu_ne0 : edToMontU P ≠ 0 := fun h => hx ((edToMontU_eq_zero_iff hP).mp h)
  have hu_def : Fp.ofNat (edToMontU P) = (1 + Fp.ofNat P.y) * (1 - Fp.ofNat P.y)⁻¹ := by
    unfold edToMontU; simp
  have h1my : (1 : Fp) - Fp.ofNat P.y ≠ 0 := by
    intro h0
    have hy1 : Fp.ofNat P.y = 1 := by grind
    have hyeq : P.y = 1 := Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) (by unfold p25519; decide) hy1
    have : edToMontU P = 0 := by
      unfold edToMontU; rw [hyeq, fpSub_self, fpInv_zero, fpMul_zero]
    exact hu_ne0 this
  have hx_ne0 : Fp.ofNat P.x ≠ 0 :=
    fun h0 => hx (Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos h0)
  rw [fp_ofNat_montRHS, mont_ed_rhs_factor (Fp.ofNat edD) (Fp.ofNat (edToMontU P))
      (Fp.ofNat P.x) (Fp.ofNat P.y) Fp.two_ne_zero fp_edD_num_rel (edOnCurve_fp_eq hP)
      hu_def h1my hx_ne0]
  exact fp_isSquare_mul fp_isSquare_neg_486664 (fp_isSquare_sq _)

/-- Every non-2-torsion point on $E_{\text{twist}}(\mathbb{F}_p)$ maps to a $u \in (0, p)$ with
    non-square `montRHS u`. -/
theorem twOnCurve_montRHS_not_isSquare {P : EdPoint}
    (hP : twOnCurve P = true) (hx : P.x ≠ 0) :
    ¬ FpIsSquare (Fp.ofNat (montRHS (twToMontU P))) := by
  have hu_ne0 : twToMontU P ≠ 0 := fun h => hx ((twToMontU_eq_zero_iff hP).mp h)
  have hu_def : Fp.ofNat (twToMontU P) = (Fp.ofNat P.y + 1) * (Fp.ofNat P.y - 1)⁻¹ := by
    unfold twToMontU; simp
  have hym1 : Fp.ofNat P.y - 1 ≠ 0 := by
    intro h0
    have hy1 : Fp.ofNat P.y = 1 := by grind
    have hyeq : P.y = 1 := Fp.eq_of_ofNat_eq (twOnCurve_y_lt hP) (by unfold p25519; decide) hy1
    have : twToMontU P = 0 := by
      unfold twToMontU; rw [hyeq, fpSub_self, fpInv_zero, fpMul_zero]
    exact hu_ne0 this
  have hu_fp_ne0 : Fp.ofNat (twToMontU P) ≠ 0 :=
    fun h0 => hu_ne0 (Fp.eq_of_ofNat_eq (twToMontU_lt P) p25519_pos h0)
  have h1dy2 : (1 : Fp) + Fp.ofNat edDInv * (Fp.ofNat P.y * Fp.ofNat P.y) ≠ 0 := by
    intro h0; exact fp_edDInv_nonsquare ⟨Fp.ofNat sqrtM1 * (Fp.ofNat P.y)⁻¹, by have := Fp.sqrtM1_sq; grind⟩
  have h_486660_eq : (-(486660 : Fp)) = Fp.ofNat (montRHS (twToMontU P)) *
      ((Fp.ofNat P.x * (Fp.ofNat (twToMontU P))⁻¹) * (Fp.ofNat P.x * (Fp.ofNat (twToMontU P))⁻¹)) := by
    rw [fp_ofNat_montRHS]
    exact mont_tw_rhs_factor (Fp.ofNat edDInv) (Fp.ofNat (twToMontU P))
      (Fp.ofNat P.x) (Fp.ofNat P.y) Fp.two_ne_zero fp_edDInv_num_rel (twOnCurve_fp_eq hP)
      hu_def hym1 hu_fp_ne0 h1dy2
  intro hsq
  exact fp_not_isSquare_neg_486660 (h_486660_eq ▸ fp_isSquare_mul hsq (fp_isSquare_sq _))

private theorem curve_of_x2_eq {x y d : Fp} (h1dy2 : 1 + d * (y * y) ≠ 0)
    (hx : x * x = (y * y - 1) * (1 + d * (y * y))⁻¹) :
    -(x * x) + y * y = 1 + d * ((x * x) * (y * y)) := by
  grind

private theorem x2_zero_imp {x y d : Fp} (h1dy2 : 1 + d * (y * y) ≠ 0)
    (hx : x * x = (y * y - 1) * (1 + d * (y * y))⁻¹) (hx0 : x = 0) :
    y * y - 1 = 0 := by
  grind

private theorem div_eq_of_mul_eq {a b c d : Fp} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : a * b⁻¹ = c * d⁻¹ := by
  grind

private theorem div_mul_eq_of_mul_eq {a b c d e : Fp} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = (c * e) * b) : a * b⁻¹ = (c * d⁻¹) * e := by
  grind

private theorem div_eq_val {a b c : Fp} (hb : b ≠ 0) (h : a = c * b) :
    a * b⁻¹ = c := by
  grind

private theorem mul_zero_imp {c u b : Fp} (hc : c ≠ 0) (hb : b ≠ 0)
    (h : (c * (u * u)) * b = 0) : u = 0 := by
  grind

private theorem mont_ed_lift_identities (d uf yf : Fp)
    (h2 : (2 : Fp) ≠ 0) (h486 : (-(486664 : Fp)) ≠ 0)
    (hd : 121666 * d = -121665) (hup1 : uf + 1 ≠ 0)
    (hrhs : uf * uf * uf + 486662 * (uf * uf) + uf ≠ 0)
    (h1dy2 : 1 + d * (yf * yf) ≠ 0)
    (hyf : yf = (uf - 1) * (uf + 1)⁻¹) :
    (yf * yf - 1) * (1 + d * (yf * yf))⁻¹ =
      ((-(486664 : Fp)) * (uf * uf)) * (uf * uf * uf + 486662 * (uf * uf) + uf)⁻¹ ∧
    (yf * yf - 1 = 0 → uf = 0) ∧
    (1 + yf) * (1 - yf)⁻¹ = uf := by
  have hy_rel : yf * (uf + 1) = uf - 1 := by grind
  have hid := mont_ed_birational_id d uf yf hd hy_rel hup1
  refine ⟨div_eq_of_mul_eq h1dy2 hrhs hid, ?_, ?_⟩
  · intro hy2_0
    have hmul0 : (-(486664 : Fp) * (uf * uf)) * (1 + d * (yf * yf)) = 0 := by
      have h0 : (0 : Fp) * (uf * uf * uf + 486662 * (uf * uf) + uf) = 0 := by grind
      rw [← hid, hy2_0, h0]
    exact mul_zero_imp h486 h1dy2 hmul0
  · have h1my : 1 - yf ≠ 0 := by intro h0; apply h2; grind
    have hmul : (1 + yf) * (uf + 1) = (uf * (1 - yf)) * (uf + 1) := by grind
    exact div_eq_val h1my (by grind)

private theorem mont_tw_lift_identities (di uf yf : Fp)
    (h2 : (2 : Fp) ≠ 0) (h486 : (-(486660 : Fp)) ≠ 0)
    (hdi : 121665 * di = -121666) (hum1 : uf - 1 ≠ 0)
    (hrhs : uf * uf * uf + 486662 * (uf * uf) + uf ≠ 0)
    (h1dy2 : 1 + di * (yf * yf) ≠ 0)
    (hyf : yf = (uf + 1) * (uf - 1)⁻¹) :
    (yf * yf - 1) * (1 + di * (yf * yf))⁻¹ =
      ((-(486660 : Fp)) * (uf * uf * uf + 486662 * (uf * uf) + uf)⁻¹) * (uf * uf) ∧
    (yf * yf - 1 = 0 → uf = 0) ∧
    (yf + 1) * (yf - 1)⁻¹ = uf := by
  have hy_rel : yf * (uf - 1) = uf + 1 := by grind
  have hid := mont_tw_birational_id di uf yf hdi hy_rel hum1
  refine ⟨div_mul_eq_of_mul_eq h1dy2 hrhs hid, ?_, ?_⟩
  · intro hy2_0
    have hmul0 : (-(486660 : Fp) * (uf * uf)) * (1 + di * (yf * yf)) = 0 := by
      have h0 : (0 : Fp) * (uf * uf * uf + 486662 * (uf * uf) + uf) = 0 := by grind
      rw [← hid, hy2_0, h0]
    exact mul_zero_imp h486 h1dy2 hmul0
  · have hym1 : yf - 1 ≠ 0 := by intro h0; apply h2; grind
    have hmul : (yf + 1) * (uf - 1) = (uf * (yf - 1)) * (uf - 1) := by grind
    exact div_eq_val hym1 (by grind)

/-- **Montgomery Curve25519 Lift Dichotomy**: every $u \in (0, p_{25519})$ lifts to either a
    non-2-torsion point on $E(\mathbb{F}_p)$ (`edToMontU P = u`) or a non-2-torsion point on
    $E_{\text{twist}}(\mathbb{F}_p)$ (`twToMontU P' = u`). -/
theorem mont_lift_dichotomy {u : Nat} (hu0 : 0 < u) (hu : u < p25519) :
    (∃ P : EdPoint, edOnCurve P = true ∧ P.x ≠ 0 ∧ edToMontU P = u) ∨
    (∃ P' : EdPoint, twOnCurve P' = true ∧ P'.x ≠ 0 ∧ twToMontU P' = u) := by
  have huf_ne0 : Fp.ofNat u ≠ 0 := by
    intro h0
    have : u = 0 := Fp.eq_of_ofNat_eq hu p25519_pos h0
    omega
  have hrhs_ne0 : Fp.ofNat u * Fp.ofNat u * Fp.ofNat u +
      486662 * (Fp.ofNat u * Fp.ofNat u) + Fp.ofNat u ≠ 0 := by
    rw [← fp_ofNat_montRHS]; exact fp_montRHS_ne_zero_of_ne_zero huf_ne0
  by_cases hsq : FpIsSquare (Fp.ofNat (montRHS u))
  · left
    have hup1 : Fp.ofNat u + 1 ≠ 0 := by
      intro h0
      have hrhs_val : Fp.ofNat (montRHS u) = 486660 := by
        rw [fp_ofNat_montRHS]; grind
      have hneg_sq : FpIsSquare (-(486660 : Fp)) := by
        have := fp_isSquare_mul fp_isSquare_neg_one (hrhs_val ▸ hsq)
        simpa [show (-1 : Fp) * 486660 = -486660 by grind] using this
      exact fp_not_isSquare_neg_486660 hneg_sq
    let yNat := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    have hyf_def : Fp.ofNat yNat = (Fp.ofNat u - 1) * (Fp.ofNat u + 1)⁻¹ := by
      dsimp only [yNat]; simp
    have h1dy2 : (1 : Fp) + Fp.ofNat edD * (Fp.ofNat yNat * Fp.ofNat yNat) ≠ 0 := by
      intro h0; exact Fp.edD_nonsquare ⟨Fp.ofNat sqrtM1 * (Fp.ofNat yNat)⁻¹, by have := Fp.sqrtM1_sq; grind⟩
    have h486 : (-(486664 : Fp)) ≠ 0 :=
      fp_ne_of_val_ne (by change fpNeg (486664 % p25519) ≠ 0; unfold fpNeg p25519; decide)
    obtain ⟨heq, hy2_imp, hrec⟩ := mont_ed_lift_identities (Fp.ofNat edD) (Fp.ofNat u)
      (Fp.ofNat yNat) Fp.two_ne_zero h486 fp_edD_num_rel hup1 hrhs_ne0 h1dy2 hyf_def
    have hx2_sq : FpIsSquare ((Fp.ofNat yNat * Fp.ofNat yNat - 1) *
        (1 + Fp.ofNat edD * (Fp.ofNat yNat * Fp.ofNat yNat))⁻¹) := by
      rw [heq, ← fp_ofNat_montRHS]
      exact fp_isSquare_mul (fp_isSquare_mul fp_isSquare_neg_486664 (fp_isSquare_sq _))
        (fp_isSquare_inv hsq)
    rcases hx2_sq with ⟨xf, hxf⟩
    refine ⟨⟨xf.val, yNat⟩, ?_, ?_, ?_⟩
    · apply edOnCurve_of_fp_eq xf.isLt (fpMul_lt _ _)
      dsimp only
      rw [Fp.ofNat_val]
      exact curve_of_x2_eq h1dy2 hxf
    · intro hx0
      have hxf0 : xf = 0 := Fp.ext hx0
      exact huf_ne0 (hy2_imp (x2_zero_imp h1dy2 hxf hxf0))
    · apply Fp.eq_of_ofNat_eq (edToMontU_lt _) hu
      have htu : Fp.ofNat (edToMontU ⟨xf.val, yNat⟩) = (1 + Fp.ofNat yNat) * (1 - Fp.ofNat yNat)⁻¹ := by
        unfold edToMontU; simp
      rw [htu, hrec]
  · right
    have hum1 : Fp.ofNat u - 1 ≠ 0 := by
      intro h0
      have hrhs_val : Fp.ofNat (montRHS u) = 486664 := by
        rw [fp_ofNat_montRHS]; grind
      have hpos_sq : FpIsSquare (486664 : Fp) := by
        have := fp_isSquare_mul fp_isSquare_neg_one fp_isSquare_neg_486664
        simpa [show (-1 : Fp) * (-486664) = 486664 by grind] using this
      exact hsq (hrhs_val ▸ hpos_sq)
    let yNat := fpMul (fpAdd u 1) (fpInv (fpSub u 1))
    have hyf_def : Fp.ofNat yNat = (Fp.ofNat u + 1) * (Fp.ofNat u - 1)⁻¹ := by
      dsimp only [yNat]; simp
    have h1dy2 : (1 : Fp) + Fp.ofNat edDInv * (Fp.ofNat yNat * Fp.ofNat yNat) ≠ 0 := by
      intro h0; exact fp_edDInv_nonsquare ⟨Fp.ofNat sqrtM1 * (Fp.ofNat yNat)⁻¹, by have := Fp.sqrtM1_sq; grind⟩
    have h486 : (-(486660 : Fp)) ≠ 0 :=
      fp_ne_of_val_ne (by change fpNeg (486660 % p25519) ≠ 0; unfold fpNeg p25519; decide)
    obtain ⟨heq, hy2_imp, hrec⟩ := mont_tw_lift_identities (Fp.ofNat edDInv) (Fp.ofNat u)
      (Fp.ofNat yNat) Fp.two_ne_zero h486 fp_edDInv_num_rel hum1 hrhs_ne0 h1dy2 hyf_def
    have hx2_sq : FpIsSquare ((Fp.ofNat yNat * Fp.ofNat yNat - 1) *
        (1 + Fp.ofNat edDInv * (Fp.ofNat yNat * Fp.ofNat yNat))⁻¹) := by
      rw [heq, ← fp_ofNat_montRHS]
      exact fp_isSquare_mul (fp_isSquare_div_of_not_isSquare fp_not_isSquare_neg_486660 hsq)
        (fp_isSquare_sq _)
    rcases hx2_sq with ⟨xf, hxf⟩
    refine ⟨⟨xf.val, yNat⟩, ?_, ?_, ?_⟩
    · apply twOnCurve_of_fp_eq xf.isLt (fpMul_lt _ _)
      dsimp only
      rw [Fp.ofNat_val]
      exact curve_of_x2_eq h1dy2 hxf
    · intro hx0
      have hxf0 : xf = 0 := Fp.ext hx0
      exact huf_ne0 (hy2_imp (x2_zero_imp h1dy2 hxf hxf0))
    · apply Fp.eq_of_ofNat_eq (twToMontU_lt _) hu
      have htu : Fp.ofNat (twToMontU ⟨xf.val, yNat⟩) = (Fp.ofNat yNat + 1) * (Fp.ofNat yNat - 1)⁻¹ := by
        unfold twToMontU; simp
      rw [htu, hrec]


end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1

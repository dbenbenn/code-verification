/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1 -- proof-setup: allow-public-import

/-!
# Cyclic Generators, Group Exponents, & Torsion on $E(\mathbb{F}_p)$ and $E_{\text{twist}}(\mathbb{F}_p)$ (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist`)

Pure `0-sorry` mathematical proofs for:
1. Uniqueness of Montgomery $u$-coordinate + $x$-parity lifts on $E(\mathbb{F}_p)$ and $E_{\text{twist}}(\mathbb{F}_p)$.
2. Explicit cyclic generators `genE` (exact order $8 \ell$) and `genTwist` (exact order $4 \ell_{\text{twist}}$).
3. Finite pigeonhole surjectivity (`inj_surj_fin`) and universal group-exponent theorems
   `edNatSmul_eight_mul_edOrderL` (`[8 \cdot \ell] P = \mathcal{O}$ on $E$) and
   `twNatSmul_four_mul_twistOrderL` (`[4 \cdot \ell_{\text{twist}}] P' = \mathcal{O}$ on $E_{\text{twist}}$).
4. Complete $u$-coordinate classification of $E(\mathbb{F}_p)[8]$ (`0, 1, lowOrderU8a, lowOrderU8b`) and
   $E_{\text{twist}}(\mathbb{F}_p)[4]$ (`0, p25519 - 1`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist

open VerifiedLibraries.Common (
  p25519 edOrderL fpAdd fpSub fpNeg fpMul fpSq fpInv sqrtM1 edD EdPoint EdExtPoint edZero
  edExtZero edExtOfAffine edExtToAffine edOnCurve edAdd edNeg edExtSmulLoop edSmul)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  p25519_pos fpSub_lt fpMul_lt fpSq_lt fpAdd_mod_left fpSub_mod_left fpNeg_zero fpMul_assoc
  fpMul_zero zero_fpMul fpMul_one one_fpMul fpInv_zero fpInv_one fpMul_fpInv_cancel
  fpInv_fpMul_cancel fpSq_eq_fpSq_iff edD_nonsquare fpNeg_mod_two_of_ne_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  Fp edOnCurve_x_lt edOnCurve_y_lt edOnCurve_fp_eq edOnCurve_edNeg edAdd_fp_x edAdd_fp_y
  edAdd_fp_denom_add_ne_zero edAdd_fp_denom_sub_ne_zero edOnCurve_edAdd edAdd_edZero
  edZero_edAdd edAdd_edNeg_self edNeg_edAdd_self edAdd_assoc edNatSmul edOnCurve_edNatSmul
  edNatSmul_edZero edNatSmul_add edNatSmul_two edNatSmul_mul edSmul_eq_edNatSmul)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.OrderPrimality (
  twistOrderL eight_mul_edOrderL_lt_two_pow_256 four_mul_twistOrderL_lt_two_pow_256
  curve_twist_card_sum edOrderL_prime twistOrderL_prime nat_pred_gcd
  dvd_four_mul_or_dvd_eight_of_dvd_eight_mul_prime
  dvd_two_mul_or_dvd_four_of_dvd_four_mul_prime)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  edToMontU edToMontU_lt)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1 (
  fp_ne_of_val_ne FpIsSquare fp_not_isSquare_of_euler_eq_sub_one edDInv fp_edDInv_nonsquare twOnCurve twAdd
  twZero twNeg twExtSmulLoop twSmul twNatSmul twOnCurve_x_lt twOnCurve_y_lt twOnCurve_fp_eq
  twOnCurve_twNeg twAdd_fp_denom_add_ne_zero twAdd_fp_x twOnCurve_twAdd twAdd_comm
  twAdd_twZero twZero_twAdd twAdd_twNeg_self twAdd_assoc twOnCurve_twNatSmul twNatSmul_twZero
  twNatSmul_add twNatSmul_two twNatSmul_mul twSmul_eq_twNatSmul twToMontU twToMontU_lt
  edOnCurve_x_eq_zero_iff twOnCurve_x_eq_zero_iff edToMontU_eq_zero_iff twToMontU_eq_zero_iff
  edOnCurve_montRHS_isSquare twOnCurve_montRHS_not_isSquare)

/-! ## 1. Uniqueness of Montgomery Lifts (`u` + `x % 2`) -/

@[simp] theorem twToMontU_twNeg (P : EdPoint) : twToMontU (twNeg P) = twToMontU P := by
  unfold twToMontU twNeg edNeg
  rw [fpAdd_mod_left, fpSub_mod_left]

private theorem y_eq_of_edMontU_eq {y1 y2 : Fp} (h2 : (2 : Fp) ≠ 0)
    (h1 : 1 - y1 ≠ 0) (h2' : 1 - y2 ≠ 0)
    (h : (1 + y1) * (1 - y1)⁻¹ = (1 + y2) * (1 - y2)⁻¹) : y1 = y2 := by
  grind

private theorem y_eq_of_twMontU_eq {y1 y2 : Fp} (h2 : (2 : Fp) ≠ 0)
    (h1 : y1 - 1 ≠ 0) (h2' : y2 - 1 ≠ 0)
    (h : (y1 + 1) * (y1 - 1)⁻¹ = (y2 + 1) * (y2 - 1)⁻¹) : y1 = y2 := by
  grind

private theorem x2_eq_of_curve_eq {x1 x2 y d : Fp} (hd : 1 + d * (y * y) ≠ 0)
    (hc1 : -(x1 * x1) + y * y = 1 + d * ((x1 * x1) * (y * y)))
    (hc2 : -(x2 * x2) + y * y = 1 + d * ((x2 * x2) * (y * y))) :
    x1 * x1 = x2 * x2 := by
  grind

theorem edToMontU_denom_ne_zero {P : EdPoint} (hP : edOnCurve P = true) (hx : P.x ≠ 0) :
    (1 : Fp) - Fp.ofNat P.y ≠ 0 := by
  intro h0
  have hsub0 : fpSub 1 P.y = 0 := by
    apply Fp.eq_of_ofNat_eq (fpSub_lt _ _) p25519_pos
    simpa using h0
  have hu0 : edToMontU P = 0 := by
    unfold edToMontU
    rw [hsub0, fpInv_zero, fpMul_zero]
  exact hx ((edToMontU_eq_zero_iff hP).mp hu0)

theorem twToMontU_denom_ne_zero {P : EdPoint} (hP : twOnCurve P = true) (hx : P.x ≠ 0) :
    Fp.ofNat P.y - 1 ≠ 0 := by
  intro h0
  have hsub0 : fpSub P.y 1 = 0 := by
    apply Fp.eq_of_ofNat_eq (fpSub_lt _ _) p25519_pos
    simpa using h0
  have hu0 : twToMontU P = 0 := by
    unfold twToMontU
    rw [hsub0, fpInv_zero, fpMul_zero]
  exact hx ((twToMontU_eq_zero_iff hP).mp hu0)

theorem edOnCurve_eq_of_edToMontU_eq {P Q : EdPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true)
    (hPx : P.x ≠ 0) (hQx : Q.x ≠ 0)
    (hu : edToMontU P = edToMontU Q) (hpar : P.x % 2 = Q.x % 2) :
    P = Q := by
  have h1P := edToMontU_denom_ne_zero hP hPx
  have h1Q := edToMontU_denom_ne_zero hQ hQx
  have hu_fp : (1 + Fp.ofNat P.y) * (1 - Fp.ofNat P.y)⁻¹ =
      (1 + Fp.ofNat Q.y) * (1 - Fp.ofNat Q.y)⁻¹ := by
    have := congrArg Fp.ofNat hu
    simpa [edToMontU] using this
  have hy_fp := y_eq_of_edMontU_eq Fp.two_ne_zero h1P h1Q hu_fp
  have hy : P.y = Q.y := Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) (edOnCurve_y_lt hQ) hy_fp
  have h1dy2 : (1 : Fp) + Fp.ofNat edD * (Fp.ofNat P.y * Fp.ofNat P.y) ≠ 0 := by
    intro h0
    exact Fp.edD_nonsquare ⟨Fp.ofNat sqrtM1 * (Fp.ofNat P.y)⁻¹, by have := Fp.sqrtM1_sq; grind⟩
  have hcP := edOnCurve_fp_eq hP
  have hcQ := edOnCurve_fp_eq hQ
  rw [← hy] at hcQ
  have hx2_fp := x2_eq_of_curve_eq h1dy2 hcP hcQ
  have hsq : fpSq P.x = fpSq Q.x := by
    apply Fp.eq_of_ofNat_eq (fpSq_lt _) (fpSq_lt _)
    simpa using hx2_fp
  have hPx_lt := edOnCurve_x_lt hP
  have hQx_lt := edOnCurve_x_lt hQ
  rcases (fpSq_eq_fpSq_iff P.x Q.x).mp hsq with hxeq | hxneg
  · rw [Nat.mod_eq_of_lt hPx_lt, Nat.mod_eq_of_lt hQx_lt] at hxeq
    ext; exact hxeq; exact hy
  · rw [Nat.mod_eq_of_lt hPx_lt] at hxneg
    have hQx_mod : Q.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hQx_lt]; exact hQx
    have hneg2 := fpNeg_mod_two_of_ne_zero hQx_mod
    rw [Nat.mod_eq_of_lt hQx_lt, ← hxneg] at hneg2
    omega

theorem twOnCurve_eq_of_twToMontU_eq {P Q : EdPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true)
    (hPx : P.x ≠ 0) (hQx : Q.x ≠ 0)
    (hu : twToMontU P = twToMontU Q) (hpar : P.x % 2 = Q.x % 2) :
    P = Q := by
  have h1P := twToMontU_denom_ne_zero hP hPx
  have h1Q := twToMontU_denom_ne_zero hQ hQx
  have hu_fp : (Fp.ofNat P.y + 1) * (Fp.ofNat P.y - 1)⁻¹ =
      (Fp.ofNat Q.y + 1) * (Fp.ofNat Q.y - 1)⁻¹ := by
    have := congrArg Fp.ofNat hu
    simpa [twToMontU] using this
  have hy_fp := y_eq_of_twMontU_eq Fp.two_ne_zero h1P h1Q hu_fp
  have hy : P.y = Q.y := Fp.eq_of_ofNat_eq (twOnCurve_y_lt hP) (twOnCurve_y_lt hQ) hy_fp
  have h1dy2 : (1 : Fp) + Fp.ofNat edDInv * (Fp.ofNat P.y * Fp.ofNat P.y) ≠ 0 := by
    intro h0
    exact fp_edDInv_nonsquare ⟨Fp.ofNat sqrtM1 * (Fp.ofNat P.y)⁻¹, by have := Fp.sqrtM1_sq; grind⟩
  have hcP := twOnCurve_fp_eq hP
  have hcQ := twOnCurve_fp_eq hQ
  rw [← hy] at hcQ
  have hx2_fp := x2_eq_of_curve_eq h1dy2 hcP hcQ
  have hsq : fpSq P.x = fpSq Q.x := by
    apply Fp.eq_of_ofNat_eq (fpSq_lt _) (fpSq_lt _)
    simpa using hx2_fp
  have hPx_lt := twOnCurve_x_lt hP
  have hQx_lt := twOnCurve_x_lt hQ
  rcases (fpSq_eq_fpSq_iff P.x Q.x).mp hsq with hxeq | hxneg
  · rw [Nat.mod_eq_of_lt hPx_lt, Nat.mod_eq_of_lt hQx_lt] at hxeq
    ext; exact hxeq; exact hy
  · rw [Nat.mod_eq_of_lt hPx_lt] at hxneg
    have hQx_mod : Q.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hQx_lt]; exact hQx
    have hneg2 := fpNeg_mod_two_of_ne_zero hQx_mod
    rw [Nat.mod_eq_of_lt hQx_lt, ← hxneg] at hneg2
    omega

/-! ## 2. Cyclic Generators `genE` and `genTwist` and Exact Orders -/

/-- Explicit cyclic generator of $E(\mathbb{F}_p)$ of order $8 \cdot \ell$. -/
@[expose] def genE : EdPoint :=
  ⟨52589339963068866056883795981360143007660399534554015914666871330345211179532,
   24812590550853470447908068216147408825700710999780120865598053715981384922836⟩

/-- Explicit cyclic generator of $E_{\text{twist}}(\mathbb{F}_p)$ of order $4 \cdot \ell_{\text{twist}}$. -/
@[expose] def genTwist : EdPoint :=
  ⟨7226562226454073972732863673687141706391764450784486856522205470343710347586, 2⟩

theorem edOnCurve_genE : edOnCurve genE = true := by
  unfold edOnCurve genE edD fpAdd fpNeg fpSq fpMul p25519; decide

theorem twOnCurve_genTwist : twOnCurve genTwist = true := by
  unfold twOnCurve genTwist edDInv fpAdd fpNeg fpSq fpMul p25519; decide

private theorem edExtToAffine_eq_edZero_of_XYZ {Q : EdExtPoint}
    (hX : Q.X = 0) (hYZ : Q.Y = Q.Z) (hZ : Q.Z % p25519 ≠ 0) :
    edExtToAffine Q = edZero := by
  ext
  · dsimp only [edExtToAffine, edZero]; rw [hX, zero_fpMul]
  · dsimp only [edExtToAffine, edZero]; rw [hYZ, fpMul_fpInv_cancel hZ]

private theorem edExtToAffine_ne_edZero_of_X_ne {Q : EdExtPoint}
    (hX : Q.X % p25519 ≠ 0) (hZ : Q.Z % p25519 ≠ 0) :
    edExtToAffine Q ≠ edZero := by
  intro h0
  have hx := congrArg EdPoint.x h0
  dsimp only [edExtToAffine, edZero] at hx
  have hmul : fpMul (fpMul Q.X (fpInv Q.Z)) Q.Z = 0 := by rw [hx, zero_fpMul]
  rw [fpMul_assoc, fpInv_fpMul_cancel hZ, fpMul_one] at hmul
  exact hX hmul

private theorem edExtToAffine_ne_edZero_of_Y_ne_Z {Q : EdExtPoint}
    (hYZ : Q.Y % p25519 ≠ Q.Z % p25519) (hZ : Q.Z % p25519 ≠ 0) :
    edExtToAffine Q ≠ edZero := by
  intro h0
  have hy := congrArg EdPoint.y h0
  dsimp only [edExtToAffine, edZero] at hy
  have hmul : fpMul (fpMul Q.Y (fpInv Q.Z)) Q.Z = fpMul 1 Q.Z := congrArg (fpMul · Q.Z) hy
  rw [fpMul_assoc, fpInv_fpMul_cancel hZ, fpMul_one, one_fpMul] at hmul
  exact hYZ hmul

set_option maxRecDepth 50000 in
private theorem genE_8L_raw :
    let Q := edExtSmulLoop 256 (8 * edOrderL) (edExtOfAffine genE) edExtZero
    Q.X = 0 ∧ Q.Y = Q.Z ∧ Q.Z % p25519 ≠ 0 := by decide

set_option maxRecDepth 50000 in
private theorem genE_4L_raw :
    let Q := edExtSmulLoop 256 (4 * edOrderL) (edExtOfAffine genE) edExtZero
    Q.Y % p25519 ≠ Q.Z % p25519 ∧ Q.Z % p25519 ≠ 0 := by decide

set_option maxRecDepth 50000 in
private theorem genE_8_raw :
    let Q := edExtSmulLoop 256 8 (edExtOfAffine genE) edExtZero
    Q.X % p25519 ≠ 0 ∧ Q.Z % p25519 ≠ 0 := by decide

set_option maxRecDepth 50000 in
private theorem genTwist_4Lt_raw :
    let Q := twExtSmulLoop 256 (4 * twistOrderL) (edExtOfAffine genTwist) edExtZero
    Q.X = 0 ∧ Q.Y = Q.Z ∧ Q.Z % p25519 ≠ 0 := by decide

set_option maxRecDepth 50000 in
private theorem genTwist_2Lt_raw :
    let Q := twExtSmulLoop 256 (2 * twistOrderL) (edExtOfAffine genTwist) edExtZero
    Q.Y % p25519 ≠ Q.Z % p25519 ∧ Q.Z % p25519 ≠ 0 := by decide

set_option maxRecDepth 50000 in
private theorem genTwist_4_raw :
    let Q := twExtSmulLoop 256 4 (edExtOfAffine genTwist) edExtZero
    Q.X % p25519 ≠ 0 ∧ Q.Z % p25519 ≠ 0 := by decide

theorem edNatSmul_eight_mul_edOrderL_genE : edNatSmul (8 * edOrderL) genE = edZero := by
  rw [← edSmul_eq_edNatSmul eight_mul_edOrderL_lt_two_pow_256 edOnCurve_genE]
  unfold edSmul
  obtain ⟨hX, hYZ, hZ⟩ := genE_8L_raw
  exact edExtToAffine_eq_edZero_of_XYZ hX hYZ hZ

theorem edNatSmul_four_mul_edOrderL_genE_ne : edNatSmul (4 * edOrderL) genE ≠ edZero := by
  have hlt : 4 * edOrderL < 2 ^ 256 := by have := eight_mul_edOrderL_lt_two_pow_256; omega
  rw [← edSmul_eq_edNatSmul hlt edOnCurve_genE]
  unfold edSmul
  obtain ⟨hYZ, hZ⟩ := genE_4L_raw
  exact edExtToAffine_ne_edZero_of_Y_ne_Z hYZ hZ

theorem edNatSmul_eight_genE_ne : edNatSmul 8 genE ≠ edZero := by
  have hlt : 8 < 2 ^ 256 := by decide
  rw [← edSmul_eq_edNatSmul hlt edOnCurve_genE]
  unfold edSmul
  obtain ⟨hX, hZ⟩ := genE_8_raw
  exact edExtToAffine_ne_edZero_of_X_ne hX hZ

theorem twNatSmul_four_mul_twistOrderL_genTwist :
    twNatSmul (4 * twistOrderL) genTwist = twZero := by
  rw [← twSmul_eq_twNatSmul four_mul_twistOrderL_lt_two_pow_256 twOnCurve_genTwist]
  unfold twSmul
  obtain ⟨hX, hYZ, hZ⟩ := genTwist_4Lt_raw
  exact edExtToAffine_eq_edZero_of_XYZ hX hYZ hZ

theorem twNatSmul_two_mul_twistOrderL_genTwist_ne :
    twNatSmul (2 * twistOrderL) genTwist ≠ twZero := by
  have hlt : 2 * twistOrderL < 2 ^ 256 := by have := four_mul_twistOrderL_lt_two_pow_256; omega
  rw [← twSmul_eq_twNatSmul hlt twOnCurve_genTwist]
  unfold twSmul
  obtain ⟨hYZ, hZ⟩ := genTwist_2Lt_raw
  exact edExtToAffine_ne_edZero_of_Y_ne_Z hYZ hZ

theorem twNatSmul_four_genTwist_ne : twNatSmul 4 genTwist ≠ twZero := by
  have hlt : 4 < 2 ^ 256 := by decide
  rw [← twSmul_eq_twNatSmul hlt twOnCurve_genTwist]
  unfold twSmul
  obtain ⟨hX, hZ⟩ := genTwist_4_raw
  exact edExtToAffine_ne_edZero_of_X_ne hX hZ

theorem edNatSmul_sub_eq_zero {G : EdPoint} (hG : edOnCurve G = true)
    {a b : Nat} (hab : a ≤ b)
    (ha : edNatSmul a G = edZero) (hb : edNatSmul b G = edZero) :
    edNatSmul (b - a) G = edZero := by
  have hsplit : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
  rw [hsplit, edNatSmul_add a (b - a) hG, ha,
      edZero_edAdd (edOnCurve_edNatSmul (b - a) hG)] at hb
  exact hb

theorem edNatSmul_gcd_eq_zero {G : EdPoint} (hG : edOnCurve G = true)
    {a b : Nat} (ha : edNatSmul a G = edZero) (hb : edNatSmul b G = edZero) :
    edNatSmul (Nat.gcd a b) G = edZero :=
  nat_pred_gcd (P := fun n => edNatSmul n G = edZero)
    (fun _ _ hxy hx hy => edNatSmul_sub_eq_zero hG hxy hx hy) a b ha hb

theorem edNatSmul_dvd_eq_zero {G : EdPoint} (hG : edOnCurve G = true)
    {d m : Nat} (hd : edNatSmul d G = edZero) (hdm : d ∣ m) :
    edNatSmul m G = edZero := by
  rcases hdm with ⟨q, rfl⟩
  rw [Nat.mul_comm, edNatSmul_mul q d hG, hd, edNatSmul_edZero]

theorem twNatSmul_sub_eq_zero {G : EdPoint} (hG : twOnCurve G = true)
    {a b : Nat} (hab : a ≤ b)
    (ha : twNatSmul a G = twZero) (hb : twNatSmul b G = twZero) :
    twNatSmul (b - a) G = twZero := by
  have hsplit : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
  rw [hsplit, twNatSmul_add a (b - a) hG, ha,
      twZero_twAdd (twOnCurve_twNatSmul (b - a) hG)] at hb
  exact hb

theorem twNatSmul_gcd_eq_zero {G : EdPoint} (hG : twOnCurve G = true)
    {a b : Nat} (ha : twNatSmul a G = twZero) (hb : twNatSmul b G = twZero) :
    twNatSmul (Nat.gcd a b) G = twZero :=
  nat_pred_gcd (P := fun n => twNatSmul n G = twZero)
    (fun _ _ hxy hx hy => twNatSmul_sub_eq_zero hG hxy hx hy) a b ha hb

theorem twNatSmul_dvd_eq_zero {G : EdPoint} (hG : twOnCurve G = true)
    {d m : Nat} (hd : twNatSmul d G = twZero) (hdm : d ∣ m) :
    twNatSmul m G = twZero := by
  rcases hdm with ⟨q, rfl⟩
  rw [Nat.mul_comm, twNatSmul_mul q d hG, hd, twNatSmul_twZero]

theorem genE_exact_order {k : Nat} (hk0 : 0 < k) (hk : k < 8 * edOrderL) :
    edNatSmul k genE ≠ edZero := by
  intro hk_zero
  have hgcd := edNatSmul_gcd_eq_zero edOnCurve_genE hk_zero edNatSmul_eight_mul_edOrderL_genE
  have hgcd_lt : Nat.gcd k (8 * edOrderL) < 8 * edOrderL :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd hk0 (Nat.gcd_dvd_left k (8 * edOrderL))) hk
  rcases dvd_four_mul_or_dvd_eight_of_dvd_eight_mul_prime edOrderL_prime
      (Nat.gcd_dvd_right k (8 * edOrderL)) hgcd_lt with h4L | h8
  · exact edNatSmul_four_mul_edOrderL_genE_ne (edNatSmul_dvd_eq_zero edOnCurve_genE hgcd h4L)
  · exact edNatSmul_eight_genE_ne (edNatSmul_dvd_eq_zero edOnCurve_genE hgcd h8)

theorem genTwist_exact_order {k : Nat} (hk0 : 0 < k) (hk : k < 4 * twistOrderL) :
    twNatSmul k genTwist ≠ twZero := by
  intro hk_zero
  have hgcd := twNatSmul_gcd_eq_zero twOnCurve_genTwist hk_zero
    twNatSmul_four_mul_twistOrderL_genTwist
  have hgcd_lt : Nat.gcd k (4 * twistOrderL) < 4 * twistOrderL :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd hk0 (Nat.gcd_dvd_left k (4 * twistOrderL))) hk
  rcases dvd_two_mul_or_dvd_four_of_dvd_four_mul_prime twistOrderL_prime
      (Nat.gcd_dvd_right k (4 * twistOrderL)) hgcd_lt with h2Lt | h4
  · exact twNatSmul_two_mul_twistOrderL_genTwist_ne
      (twNatSmul_dvd_eq_zero twOnCurve_genTwist hgcd h2Lt)
  · exact twNatSmul_four_genTwist_ne (twNatSmul_dvd_eq_zero twOnCurve_genTwist hgcd h4)

@[simp] theorem twNeg_twAdd_self {P : EdPoint} (hP : twOnCurve P = true) :
    twAdd (twNeg P) P = twZero := by
  rw [twAdd_comm, twAdd_twNeg_self hP]

theorem genE_inj_lt {i j : Nat} (hi : i < 8 * edOrderL) (hj : j < 8 * edOrderL)
    (h : edNatSmul i genE = edNatSmul j genE) : i = j := by
  by_cases hij : i = j
  · exact hij
  · by_cases hlt : i < j
    · exfalso
      have hsplit : j = i + (j - i) := (Nat.add_sub_of_le (Nat.le_of_lt hlt)).symm
      have heq := h
      rw [hsplit, edNatSmul_add i (j - i) edOnCurve_genE] at heq
      have hAi := edOnCurve_edNatSmul i edOnCurve_genE
      have hAd := edOnCurve_edNatSmul (j - i) edOnCurve_genE
      have hcancel := congrArg (edAdd (edNeg (edNatSmul i genE))) heq
      rw [edNeg_edAdd_self hAi, ← edAdd_assoc (edOnCurve_edNeg hAi) hAi hAd,
          edNeg_edAdd_self hAi, edZero_edAdd hAd] at hcancel
      exact genE_exact_order (by omega) (by omega) hcancel.symm
    · exfalso
      have hgt : j < i := by omega
      have hsplit : i = j + (i - j) := (Nat.add_sub_of_le (Nat.le_of_lt hgt)).symm
      have heq := h.symm
      rw [hsplit, edNatSmul_add j (i - j) edOnCurve_genE] at heq
      have hAj := edOnCurve_edNatSmul j edOnCurve_genE
      have hAd := edOnCurve_edNatSmul (i - j) edOnCurve_genE
      have hcancel := congrArg (edAdd (edNeg (edNatSmul j genE))) heq
      rw [edNeg_edAdd_self hAj, ← edAdd_assoc (edOnCurve_edNeg hAj) hAj hAd,
          edNeg_edAdd_self hAj, edZero_edAdd hAd] at hcancel
      exact genE_exact_order (by omega) (by omega) hcancel.symm

theorem genTwist_inj_lt {i j : Nat} (hi : i < 4 * twistOrderL) (hj : j < 4 * twistOrderL)
    (h : twNatSmul i genTwist = twNatSmul j genTwist) : i = j := by
  by_cases hij : i = j
  · exact hij
  · by_cases hlt : i < j
    · exfalso
      have hsplit : j = i + (j - i) := (Nat.add_sub_of_le (Nat.le_of_lt hlt)).symm
      have heq := h
      rw [hsplit, twNatSmul_add i (j - i) twOnCurve_genTwist] at heq
      have hAi := twOnCurve_twNatSmul i twOnCurve_genTwist
      have hAd := twOnCurve_twNatSmul (j - i) twOnCurve_genTwist
      have hcancel := congrArg (twAdd (twNeg (twNatSmul i genTwist))) heq
      rw [twNeg_twAdd_self hAi, ← twAdd_assoc (twOnCurve_twNeg hAi) hAi hAd,
          twNeg_twAdd_self hAi, twZero_twAdd hAd] at hcancel
      exact genTwist_exact_order (by omega) (by omega) hcancel.symm
    · exfalso
      have hgt : j < i := by omega
      have hsplit : i = j + (i - j) := (Nat.add_sub_of_le (Nat.le_of_lt hgt)).symm
      have heq := h.symm
      rw [hsplit, twNatSmul_add j (i - j) twOnCurve_genTwist] at heq
      have hAj := twOnCurve_twNatSmul j twOnCurve_genTwist
      have hAd := twOnCurve_twNatSmul (i - j) twOnCurve_genTwist
      have hcancel := congrArg (twAdd (twNeg (twNatSmul j genTwist))) heq
      rw [twNeg_twAdd_self hAj, ← twAdd_assoc (twOnCurve_twNeg hAj) hAj hAd,
          twNeg_twAdd_self hAj, twZero_twAdd hAd] at hcancel
      exact genTwist_exact_order (by omega) (by omega) hcancel.symm

/-! ## 3. Pure-`Init` Finite Pigeonhole Surjectivity & Universal Group Exponents -/

/-- Pure-`Init` finite pigeonhole principle: every injective map `Fin N → Fin N` is surjective. -/
theorem inj_surj_fin : ∀ {N : Nat} (f : Fin N → Fin N),
    (∀ i j, f i = f j → i = j) → ∀ y : Fin N, ∃ x : Fin N, f x = y
  | 0, _, _, y => nomatch y
  | n + 1, f, hinj, y => by
    by_cases hy : y = f ⟨n, Nat.lt_succ_self n⟩
    · exact ⟨⟨n, Nat.lt_succ_self n⟩, hy.symm⟩
    · have h_avoid : ∀ i : Fin n,
          (if (f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val = n then
             (f ⟨n, Nat.lt_succ_self n⟩).val
           else (f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val) < n := by
        intro i
        split
        · next hfn =>
          have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) ≠
              ⟨n, Nat.lt_succ_self n⟩ := by
            intro heq
            have hval : i.val = n := congrArg Fin.val heq
            have := i.isLt
            omega
          have hfl_ne : f ⟨n, Nat.lt_succ_self n⟩ ≠ f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
            intro heq; exact hne (hinj _ _ heq).symm
          have hfl_val : (f ⟨n, Nat.lt_succ_self n⟩).val ≠ n := by
            intro hv; apply hfl_ne; ext; omega
          have := (f ⟨n, Nat.lt_succ_self n⟩).isLt
          omega
        · next hfn =>
          have := (f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).isLt
          omega
      let g : Fin n → Fin n := fun i => ⟨_, h_avoid i⟩
      have hginj : ∀ i j : Fin n, g i = g j → i = j := by
        intro i j hgij
        have hv : (g i).val = (g j).val := congrArg Fin.val hgij
        dsimp only [g] at hv
        by_cases hi : (f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val = n <;>
          by_cases hj : (f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩).val = n
        · have feq : f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
              f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by ext; omega
          have hij : i.val = j.val := congrArg (@Fin.val (n + 1)) (hinj _ _ feq)
          exact Fin.ext hij
        · simp only [hi, hj, ↓reduceIte] at hv
          have feq : f ⟨n, Nat.lt_succ_self n⟩ = f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by
            ext; exact hv
          have hval : n = j.val := congrArg Fin.val (hinj _ _ feq)
          have := j.isLt
          omega
        · simp only [hi, hj, ↓reduceIte] at hv
          have feq : f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = f ⟨n, Nat.lt_succ_self n⟩ := by
            ext; exact hv
          have hval : i.val = n := congrArg Fin.val (hinj _ _ feq)
          have := i.isLt
          omega
        · simp only [hi, hj, ↓reduceIte] at hv
          have feq : f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
              f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by ext; exact hv
          have hij : i.val = j.val := congrArg (@Fin.val (n + 1)) (hinj _ _ feq)
          exact Fin.ext hij
      by_cases hyn : y.val = n
      · have hfl_lt : (f ⟨n, Nat.lt_succ_self n⟩).val < n := by
          have hne_val : (f ⟨n, Nat.lt_succ_self n⟩).val ≠ n := by
            intro hv; apply hy; ext; omega
          have := (f ⟨n, Nat.lt_succ_self n⟩).isLt
          omega
        obtain ⟨x0, hx0⟩ := inj_surj_fin g hginj ⟨(f ⟨n, Nat.lt_succ_self n⟩).val, hfl_lt⟩
        have hv : (g x0).val = (f ⟨n, Nat.lt_succ_self n⟩).val := congrArg Fin.val hx0
        dsimp only [g] at hv
        by_cases hx0_n : (f ⟨x0.val, Nat.lt_succ_of_lt x0.isLt⟩).val = n
        · refine ⟨⟨x0.val, Nat.lt_succ_of_lt x0.isLt⟩, ?_⟩
          ext; omega
        · simp only [hx0_n, ↓reduceIte] at hv
          have feq : f ⟨x0.val, Nat.lt_succ_of_lt x0.isLt⟩ = f ⟨n, Nat.lt_succ_self n⟩ := by
            ext; exact hv
          have hval : x0.val = n := congrArg Fin.val (hinj _ _ feq)
          have := x0.isLt
          omega
      · have hy_lt : y.val < n := by have := y.isLt; omega
        obtain ⟨x0, hx0⟩ := inj_surj_fin g hginj ⟨y.val, hy_lt⟩
        have hv : (g x0).val = y.val := congrArg Fin.val hx0
        dsimp only [g] at hv
        by_cases hx0_n : (f ⟨x0.val, Nat.lt_succ_of_lt x0.isLt⟩).val = n
        · simp only [hx0_n, ↓reduceIte] at hv
          exfalso; apply hy; ext; exact hv.symm
        · simp only [hx0_n, ↓reduceIte] at hv
          refine ⟨⟨x0.val, Nat.lt_succ_of_lt x0.isLt⟩, ?_⟩
          ext; exact hv

/-- Injection from $E(\mathbb{F}_p) \sqcup E_{\text{twist}}(\mathbb{F}_p)$ into
    `{0, ..., 2 * (p25519 + 1) - 1}` via Montgomery $u$-coordinates and $x$-parity. -/
private def encodeCurveSum : EdPoint ⊕ EdPoint → Nat
  | Sum.inl P =>
    if P.x = 0 then (if P.y = 1 then 2 * p25519 else 0)
    else 2 * edToMontU P + P.x % 2
  | Sum.inr P' =>
    if P'.x = 0 then (if P'.y = 1 then 2 * p25519 + 1 else 1)
    else 2 * twToMontU P' + P'.x % 2

private def ValidCurveSum : EdPoint ⊕ EdPoint → Prop
  | Sum.inl P => edOnCurve P = true
  | Sum.inr P' => twOnCurve P' = true

private theorem encodeCurveSum_lt {s : EdPoint ⊕ EdPoint} :
    encodeCurveSum s < 2 * (p25519 + 1) := by
  cases s with
  | inl P =>
    dsimp only [encodeCurveSum]
    have hp := p25519_pos
    have hu := edToMontU_lt P
    generalize p25519 = p at hp hu ⊢
    split
    · split <;> omega
    · omega
  | inr P' =>
    dsimp only [encodeCurveSum]
    have hp := p25519_pos
    have hu := twToMontU_lt P'
    generalize p25519 = p at hp hu ⊢
    split
    · split <;> omega
    · omega

private theorem encodeCurveSum_special_iff (s : EdPoint ⊕ EdPoint) (hs : ValidCurveSum s) :
    (encodeCurveSum s = 0 ∨ encodeCurveSum s = 1 ∨
     encodeCurveSum s = 2 * p25519 ∨ encodeCurveSum s = 2 * p25519 + 1) ↔
    (match s with | Sum.inl P => P.x = 0 | Sum.inr P' => P'.x = 0) := by
  cases s with
  | inl P =>
    dsimp only [ValidCurveSum] at hs
    dsimp only [encodeCurveSum]
    by_cases hx : P.x = 0
    · simp only [hx, ↓reduceIte]
      constructor
      · intro _; exact trivial
      · intro _; split
        · right; right; left; rfl
        · left; rfl
    · simp only [hx, ↓reduceIte]
      have hu_ne : edToMontU P ≠ 0 := fun hu0 => hx ((edToMontU_eq_zero_iff hs).mp hu0)
      have hu_lt := edToMontU_lt P
      generalize p25519 = p at hu_lt ⊢
      constructor
      · intro h; omega
      · exact False.elim
  | inr P' =>
    dsimp only [ValidCurveSum] at hs
    dsimp only [encodeCurveSum]
    by_cases hx : P'.x = 0
    · simp only [hx, ↓reduceIte]
      constructor
      · intro _; exact trivial
      · intro _; split
        · right; right; right; rfl
        · right; left; rfl
    · simp only [hx, ↓reduceIte]
      have hu_ne : twToMontU P' ≠ 0 := fun hu0 => hx ((twToMontU_eq_zero_iff hs).mp hu0)
      have hu_lt := twToMontU_lt P'
      generalize p25519 = p at hu_lt ⊢
      constructor
      · intro h; omega
      · exact False.elim

private theorem encodeCurveSum_inj (s1 s2 : EdPoint ⊕ EdPoint)
    (hs1 : ValidCurveSum s1) (hs2 : ValidCurveSum s2)
    (heq : encodeCurveSum s1 = encodeCurveSum s2) : s1 = s2 := by
  have hp : p25519 > 2 := by unfold p25519; decide
  have hp1_ne : p25519 - 1 ≠ 1 := by unfold p25519; decide
  cases s1 with
  | inl P =>
    dsimp only [ValidCurveSum] at hs1
    by_cases hPx : P.x = 0
    · have hspec : encodeCurveSum (Sum.inl P) = 0 ∨ encodeCurveSum (Sum.inl P) = 1 ∨
          encodeCurveSum (Sum.inl P) = 2 * p25519 ∨ encodeCurveSum (Sum.inl P) = 2 * p25519 + 1 :=
        (encodeCurveSum_special_iff (Sum.inl P) hs1).mpr hPx
      rw [heq] at hspec
      have hs2_x0 := (encodeCurveSum_special_iff s2 hs2).mp hspec
      cases s2 with
      | inl Q =>
        dsimp only [ValidCurveSum] at hs2
        dsimp only at hs2_x0
        dsimp only [encodeCurveSum] at heq
        simp only [hPx, hs2_x0, ↓reduceIte] at heq
        rcases (edOnCurve_x_eq_zero_iff hs1).mp hPx with rfl | rfl <;>
          rcases (edOnCurve_x_eq_zero_iff hs2).mp hs2_x0 with rfl | rfl
        · rfl
        · dsimp only [edZero] at heq
          simp only [hp1_ne, ↓reduceIte] at heq
          generalize p25519 = p at hp heq; omega
        · dsimp only [edZero] at heq
          simp only [hp1_ne, ↓reduceIte] at heq
          generalize p25519 = p at hp heq; omega
        · rfl
      | inr Q' =>
        dsimp only at hs2_x0
        dsimp only [encodeCurveSum] at heq
        simp only [hPx, hs2_x0, ↓reduceIte] at heq
        by_cases hPy : P.y = 1 <;> by_cases hQy : Q'.y = 1 <;>
          simp only [hPy, hQy, ↓reduceIte] at heq <;>
          (generalize p25519 = p at hp heq; omega)
    · have hnspec : ¬ (encodeCurveSum (Sum.inl P) = 0 ∨ encodeCurveSum (Sum.inl P) = 1 ∨
          encodeCurveSum (Sum.inl P) = 2 * p25519 ∨ encodeCurveSum (Sum.inl P) = 2 * p25519 + 1) :=
        fun h => hPx ((encodeCurveSum_special_iff (Sum.inl P) hs1).mp h)
      rw [heq] at hnspec
      cases s2 with
      | inl Q =>
        dsimp only [ValidCurveSum] at hs2
        have hQx : Q.x ≠ 0 := fun h0 => hnspec ((encodeCurveSum_special_iff (Sum.inl Q) hs2).mpr h0)
        dsimp only [encodeCurveSum] at heq
        simp only [hPx, hQx, ↓reduceIte] at heq
        have hu : edToMontU P = edToMontU Q := by omega
        have hpar : P.x % 2 = Q.x % 2 := by omega
        exact congrArg Sum.inl (edOnCurve_eq_of_edToMontU_eq hs1 hs2 hPx hQx hu hpar)
      | inr Q' =>
        dsimp only [ValidCurveSum] at hs2
        have hQx : Q'.x ≠ 0 := fun h0 => hnspec ((encodeCurveSum_special_iff (Sum.inr Q') hs2).mpr h0)
        dsimp only [encodeCurveSum] at heq
        simp only [hPx, hQx, ↓reduceIte] at heq
        have hu : edToMontU P = twToMontU Q' := by omega
        exfalso
        exact twOnCurve_montRHS_not_isSquare hs2 hQx
          (hu ▸ edOnCurve_montRHS_isSquare hs1 hPx)
  | inr P' =>
    dsimp only [ValidCurveSum] at hs1
    by_cases hPx : P'.x = 0
    · have hspec : encodeCurveSum (Sum.inr P') = 0 ∨ encodeCurveSum (Sum.inr P') = 1 ∨
          encodeCurveSum (Sum.inr P') = 2 * p25519 ∨ encodeCurveSum (Sum.inr P') = 2 * p25519 + 1 :=
        (encodeCurveSum_special_iff (Sum.inr P') hs1).mpr hPx
      rw [heq] at hspec
      have hs2_x0 := (encodeCurveSum_special_iff s2 hs2).mp hspec
      cases s2 with
      | inl Q =>
        dsimp only at hs2_x0
        dsimp only [encodeCurveSum] at heq
        simp only [hPx, hs2_x0, ↓reduceIte] at heq
        by_cases hPy : P'.y = 1 <;> by_cases hQy : Q.y = 1 <;>
          simp only [hPy, hQy, ↓reduceIte] at heq <;>
          (generalize p25519 = p at hp heq; omega)
      | inr Q' =>
        dsimp only [ValidCurveSum] at hs2
        dsimp only at hs2_x0
        dsimp only [encodeCurveSum] at heq
        simp only [hPx, hs2_x0, ↓reduceIte] at heq
        rcases (twOnCurve_x_eq_zero_iff hs1).mp hPx with rfl | rfl <;>
          rcases (twOnCurve_x_eq_zero_iff hs2).mp hs2_x0 with rfl | rfl
        · rfl
        · dsimp only [edZero] at heq
          simp only [hp1_ne, ↓reduceIte] at heq
          generalize p25519 = p at hp heq; omega
        · dsimp only [edZero] at heq
          simp only [hp1_ne, ↓reduceIte] at heq
          generalize p25519 = p at hp heq; omega
        · rfl
    · have hnspec : ¬ (encodeCurveSum (Sum.inr P') = 0 ∨ encodeCurveSum (Sum.inr P') = 1 ∨
          encodeCurveSum (Sum.inr P') = 2 * p25519 ∨ encodeCurveSum (Sum.inr P') = 2 * p25519 + 1) :=
        fun h => hPx ((encodeCurveSum_special_iff (Sum.inr P') hs1).mp h)
      rw [heq] at hnspec
      cases s2 with
      | inl Q =>
        dsimp only [ValidCurveSum] at hs2
        have hQx : Q.x ≠ 0 := fun h0 => hnspec ((encodeCurveSum_special_iff (Sum.inl Q) hs2).mpr h0)
        dsimp only [encodeCurveSum] at heq
        simp only [hPx, hQx, ↓reduceIte] at heq
        have hu : twToMontU P' = edToMontU Q := by omega
        exfalso
        exact twOnCurve_montRHS_not_isSquare hs1 hPx
          (hu.symm ▸ edOnCurve_montRHS_isSquare hs2 hQx)
      | inr Q' =>
        dsimp only [ValidCurveSum] at hs2
        have hQx : Q'.x ≠ 0 := fun h0 => hnspec ((encodeCurveSum_special_iff (Sum.inr Q') hs2).mpr h0)
        dsimp only [encodeCurveSum] at heq
        simp only [hPx, hQx, ↓reduceIte] at heq
        have hu : twToMontU P' = twToMontU Q' := by omega
        have hpar : P'.x % 2 = Q'.x % 2 := by omega
        exact congrArg Sum.inr (twOnCurve_eq_of_twToMontU_eq hs1 hs2 hPx hQx hu hpar)

private def enumGenerators (i : Fin (2 * (p25519 + 1))) : EdPoint ⊕ EdPoint :=
  if i.val < 8 * edOrderL then
    Sum.inl (edNatSmul i.val genE)
  else
    Sum.inr (twNatSmul (i.val - 8 * edOrderL) genTwist)

private theorem enumGenerators_valid (i : Fin (2 * (p25519 + 1))) :
    ValidCurveSum (enumGenerators i) := by
  unfold enumGenerators
  split
  · exact edOnCurve_edNatSmul i.val edOnCurve_genE
  · exact twOnCurve_twNatSmul (i.val - 8 * edOrderL) twOnCurve_genTwist

private theorem sub_lt_four_mul_twistOrderL {k : Nat}
    (hk : k < 2 * (p25519 + 1)) (hge : ¬ k < 8 * edOrderL) :
    k - 8 * edOrderL < 4 * twistOrderL := by
  have hsum := curve_twist_card_sum
  generalize 8 * edOrderL = A at hge hsum ⊢
  generalize 4 * twistOrderL = B at hsum ⊢
  generalize 2 * (p25519 + 1) = C at hk hsum
  omega

private theorem sum_inl_inj {α β : Type} {a b : α} (h : (Sum.inl a : α ⊕ β) = Sum.inl b) :
    a = b := by
  cases h; rfl

private theorem sum_inr_inj {α β : Type} {a b : β} (h : (Sum.inr a : α ⊕ β) = Sum.inr b) :
    a = b := by
  cases h; rfl

private theorem enumGenerators_inj {i j : Fin (2 * (p25519 + 1))}
    (heq : enumGenerators i = enumGenerators j) : i = j := by
  dsimp only [enumGenerators] at heq
  by_cases hi : i.val < 8 * edOrderL <;> by_cases hj : j.val < 8 * edOrderL
  · simp only [hi, hj, ↓reduceIte] at heq
    exact Fin.ext (genE_inj_lt hi hj (sum_inl_inj heq))
  · simp only [hi, hj, ↓reduceIte] at heq; nomatch heq
  · simp only [hi, hj, ↓reduceIte] at heq; nomatch heq
  · simp only [hi, hj, ↓reduceIte] at heq
    have hi_tw := sub_lt_four_mul_twistOrderL i.isLt hi
    have hj_tw := sub_lt_four_mul_twistOrderL j.isLt hj
    have hsub := genTwist_inj_lt hi_tw hj_tw (sum_inr_inj heq)
    apply Fin.ext
    generalize 8 * edOrderL = A at hi hj hsub
    omega

private def finGeneratorMap (i : Fin (2 * (p25519 + 1))) : Fin (2 * (p25519 + 1)) :=
  ⟨encodeCurveSum (enumGenerators i), encodeCurveSum_lt⟩

private theorem finGeneratorMap_surj :
    ∀ y : Fin (2 * (p25519 + 1)), ∃ i : Fin (2 * (p25519 + 1)), finGeneratorMap i = y := by
  apply inj_surj_fin finGeneratorMap
  intro i j hij
  have henc : encodeCurveSum (enumGenerators i) = encodeCurveSum (enumGenerators j) :=
    congrArg Fin.val hij
  exact enumGenerators_inj
    (encodeCurveSum_inj _ _ (enumGenerators_valid i) (enumGenerators_valid j) henc)

/-- Every point on $E(\mathbb{F}_p)$ lies in the cyclic subgroup generated by `genE`. -/
theorem edOnCurve_exists_genE {P : EdPoint} (hP : edOnCurve P = true) :
    ∃ i : Nat, i < 8 * edOrderL ∧ P = edNatSmul i genE := by
  obtain ⟨i, hi_eq⟩ := finGeneratorMap_surj ⟨encodeCurveSum (Sum.inl P), encodeCurveSum_lt⟩
  have henc : encodeCurveSum (enumGenerators i) = encodeCurveSum (Sum.inl P) :=
    congrArg Fin.val hi_eq
  have hsum_eq := encodeCurveSum_inj _ (Sum.inl P) (enumGenerators_valid i) hP henc
  dsimp only [enumGenerators] at hsum_eq
  by_cases hlt : i.val < 8 * edOrderL
  · simp only [hlt, ↓reduceIte] at hsum_eq
    exact ⟨i.val, hlt, (sum_inl_inj hsum_eq).symm⟩
  · simp only [hlt, ↓reduceIte] at hsum_eq; nomatch hsum_eq

/-- Every point on $E_{\text{twist}}(\mathbb{F}_p)$ lies in the cyclic subgroup generated by `genTwist`. -/
theorem twOnCurve_exists_genTwist {P' : EdPoint} (hP' : twOnCurve P' = true) :
    ∃ j : Nat, j < 4 * twistOrderL ∧ P' = twNatSmul j genTwist := by
  obtain ⟨i, hi_eq⟩ := finGeneratorMap_surj ⟨encodeCurveSum (Sum.inr P'), encodeCurveSum_lt⟩
  have henc : encodeCurveSum (enumGenerators i) = encodeCurveSum (Sum.inr P') :=
    congrArg Fin.val hi_eq
  have hsum_eq := encodeCurveSum_inj _ (Sum.inr P') (enumGenerators_valid i) hP' henc
  dsimp only [enumGenerators] at hsum_eq
  by_cases hlt : i.val < 8 * edOrderL
  · simp only [hlt, ↓reduceIte] at hsum_eq; nomatch hsum_eq
  · simp only [hlt, ↓reduceIte] at hsum_eq
    exact ⟨i.val - 8 * edOrderL, sub_lt_four_mul_twistOrderL i.isLt hlt,
      (sum_inr_inj hsum_eq).symm⟩

/-- **Universal Group Exponent on $E(\mathbb{F}_p)$**: $[8 \cdot \ell] P = \mathcal{O}$ for every
    point $P \in E(\mathbb{F}_p)$. -/
theorem edNatSmul_eight_mul_edOrderL {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul (8 * edOrderL) P = edZero := by
  obtain ⟨i, _, rfl⟩ := edOnCurve_exists_genE hP
  rw [← edNatSmul_mul (8 * edOrderL) i edOnCurve_genE,
      Nat.mul_comm (8 * edOrderL) i,
      edNatSmul_mul i (8 * edOrderL) edOnCurve_genE,
      edNatSmul_eight_mul_edOrderL_genE, edNatSmul_edZero]

/-- **Universal Group Exponent on $E_{\text{twist}}(\mathbb{F}_p)$**:
    $[4 \cdot \ell_{\text{twist}}] P' = \mathcal{O}$ for every point $P' \in E_{\text{twist}}(\mathbb{F}_p)$. -/
theorem twNatSmul_four_mul_twistOrderL {P' : EdPoint} (hP' : twOnCurve P' = true) :
    twNatSmul (4 * twistOrderL) P' = twZero := by
  obtain ⟨j, _, rfl⟩ := twOnCurve_exists_genTwist hP'
  rw [← twNatSmul_mul (4 * twistOrderL) j twOnCurve_genTwist,
      Nat.mul_comm (4 * twistOrderL) j,
      twNatSmul_mul j (4 * twistOrderL) twOnCurve_genTwist,
      twNatSmul_four_mul_twistOrderL_genTwist, twNatSmul_twZero]

/-! ## 4. Complete Classification of $E(\mathbb{F}_p)[8]$ and $E_{\text{twist}}(\mathbb{F}_p)[4]$ -/

/-- First primitive order-8 Montgomery $u$-coordinate on $E(\mathbb{F}_p)$. -/
@[expose] def lowOrderU8a : Nat :=
  325606250916557431795983626356110631294008115727848805560023387167927233504

/-- Second primitive order-8 Montgomery $u$-coordinate on $E(\mathbb{F}_p)$. -/
@[expose] def lowOrderU8b : Nat :=
  39382357235489614581723060781553021112529911719440698176882885853963445705823

theorem edNatSmul_two_eq_zero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 2 P = edZero ↔ P.x = 0 := by
  rw [edNatSmul_two hP]
  constructor
  · intro h2P
    have hP_eq_neg : P = edNeg P := by
      have h := congrArg (edAdd (edNeg P)) h2P
      rw [← edAdd_assoc (edOnCurve_edNeg hP) hP hP, edNeg_edAdd_self hP,
          edZero_edAdd hP, edAdd_edZero (edOnCurve_edNeg hP)] at h
      exact h
    have hx_neg : P.x = fpNeg P.x := congrArg EdPoint.x hP_eq_neg
    have hxf : Fp.ofNat P.x = -Fp.ofNat P.x := by
      have := congrArg Fp.ofNat hx_neg; simpa using this
    have hx0 : Fp.ofNat P.x = 0 := by have := Fp.two_ne_zero; grind
    exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos hx0
  · intro hx0
    have hneg_eq : edNeg P = P := by
      ext
      · dsimp only [edNeg]; rw [hx0, fpNeg_zero]
      · dsimp only [edNeg]; exact Nat.mod_eq_of_lt (edOnCurve_y_lt hP)
    have h := edAdd_edNeg_self hP
    rw [hneg_eq] at h
    exact h

theorem edNatSmul_two_eq_zero_iff_montU {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 2 P = edZero ↔ edToMontU P = 0 :=
  (edNatSmul_two_eq_zero_iff hP).trans (edToMontU_eq_zero_iff hP).symm

theorem twNatSmul_two_eq_zero_iff {P : EdPoint} (hP : twOnCurve P = true) :
    twNatSmul 2 P = twZero ↔ P.x = 0 := by
  rw [twNatSmul_two hP]
  constructor
  · intro h2P
    have hP_eq_neg : P = twNeg P := by
      have h := congrArg (twAdd (twNeg P)) h2P
      rw [← twAdd_assoc (twOnCurve_twNeg hP) hP hP, twAdd_comm (twNeg P) P,
          twAdd_twNeg_self hP, twZero_twAdd hP, twAdd_twZero (twOnCurve_twNeg hP)] at h
      exact h
    have hx_neg : P.x = fpNeg P.x := congrArg EdPoint.x hP_eq_neg
    have hxf : Fp.ofNat P.x = -Fp.ofNat P.x := by
      have := congrArg Fp.ofNat hx_neg; simpa using this
    have hx0 : Fp.ofNat P.x = 0 := by have := Fp.two_ne_zero; grind
    exact Fp.eq_of_ofNat_eq (twOnCurve_x_lt hP) p25519_pos hx0
  · intro hx0
    have hneg_eq : twNeg P = P := by
      ext
      · dsimp only [twNeg, edNeg]; rw [hx0, fpNeg_zero]
      · dsimp only [twNeg, edNeg]; exact Nat.mod_eq_of_lt (twOnCurve_y_lt hP)
    have h := twAdd_twNeg_self hP
    rw [hneg_eq] at h
    exact h

theorem twNatSmul_two_eq_zero_iff_montU {P : EdPoint} (hP : twOnCurve P = true) :
    twNatSmul 2 P = twZero ↔ twToMontU P = 0 :=
  (twNatSmul_two_eq_zero_iff hP).trans (twToMontU_eq_zero_iff hP).symm

private theorem dbl_x_zero_iff {x y d : Fp} (h2 : (2 : Fp) ≠ 0)
    (hden : 1 + d * ((x * x) * (y * y)) ≠ 0) :
    (x * y + y * x) * (1 + d * ((x * x) * (y * y)))⁻¹ = 0 ↔ x = 0 ∨ y = 0 := by
  grind

theorem edAdd_self_x_eq_zero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    (edAdd P P).x = 0 ↔ P.x = 0 ∨ P.y = 0 := by
  have hx_lt : (edAdd P P).x < p25519 := fpMul_lt _ _
  have h1 : (edAdd P P).x = 0 ↔ Fp.ofNat (edAdd P P).x = 0 :=
    ⟨fun h => by simp [h], fun h => Fp.eq_of_ofNat_eq hx_lt p25519_pos h⟩
  rw [h1, edAdd_fp_x P P,
      dbl_x_zero_iff Fp.two_ne_zero (edAdd_fp_denom_add_ne_zero hP hP)]
  constructor
  · rintro (hx | hy)
    · left; exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos hx
    · right; exact Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) p25519_pos hy
  · rintro (hx | hy)
    · left; simp [hx]
    · right; simp [hy]

theorem edNatSmul_four_eq_zero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 4 P = edZero ↔ P.x = 0 ∨ P.y = 0 := by
  rw [show (4 : Nat) = 2 * 2 from rfl, edNatSmul_mul 2 2 hP, edNatSmul_two hP,
      edNatSmul_two_eq_zero_iff (edOnCurve_edAdd hP hP)]
  exact edAdd_self_x_eq_zero_iff hP

theorem twNatSmul_four_eq_zero_iff {P : EdPoint} (hP : twOnCurve P = true) :
    twNatSmul 4 P = twZero ↔ P.x = 0 ∨ P.y = 0 := by
  rw [show (4 : Nat) = 2 * 2 from rfl, twNatSmul_mul 2 2 hP, twNatSmul_two hP,
      twNatSmul_two_eq_zero_iff (twOnCurve_twAdd hP hP)]
  have hx_lt : (twAdd P P).x < p25519 := fpMul_lt _ _
  have h1 : (twAdd P P).x = 0 ↔ Fp.ofNat (twAdd P P).x = 0 :=
    ⟨fun h => by simp [h], fun h => Fp.eq_of_ofNat_eq hx_lt p25519_pos h⟩
  rw [h1, twAdd_fp_x P P,
      dbl_x_zero_iff Fp.two_ne_zero (twAdd_fp_denom_add_ne_zero hP hP)]
  constructor
  · rintro (hx | hy)
    · left; exact Fp.eq_of_ofNat_eq (twOnCurve_x_lt hP) p25519_pos hx
    · right; exact Fp.eq_of_ofNat_eq (twOnCurve_y_lt hP) p25519_pos hy
  · rintro (hx | hy)
    · left; simp [hx]
    · right; simp [hy]

theorem edToMontU_eq_one_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edToMontU P = 1 ↔ P.y = 0 := by
  constructor
  · intro hu1
    have hu_ne0 : edToMontU P ≠ 0 := by rw [hu1]; decide
    have hPx : P.x ≠ 0 := fun hx0 => hu_ne0 ((edToMontU_eq_zero_iff hP).mpr hx0)
    have hden := edToMontU_denom_ne_zero hP hPx
    have hfp : (1 + Fp.ofNat P.y) * (1 - Fp.ofNat P.y)⁻¹ = 1 := by
      have := congrArg Fp.ofNat hu1; simpa [edToMontU] using this
    have hy0 : Fp.ofNat P.y = 0 := by have := Fp.two_ne_zero; grind
    exact Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) p25519_pos hy0
  · intro hy0
    unfold edToMontU
    rw [hy0]
    unfold fpAdd fpSub fpMul
    rw [show (1 + 0) % p25519 = 1 by unfold p25519; decide,
        show (1 + p25519 - 0 % p25519) % p25519 = 1 by unfold p25519; decide,
        fpInv_one]
    unfold p25519; decide

theorem twToMontU_eq_sub_one_iff {P : EdPoint} (hP : twOnCurve P = true) :
    twToMontU P = p25519 - 1 ↔ P.y = 0 := by
  have hm1 : Fp.ofNat (p25519 - 1) = (-1 : Fp) := by ext; unfold Fp.ofNat p25519; decide
  constructor
  · intro hu
    have hu_ne0 : twToMontU P ≠ 0 := by rw [hu]; unfold p25519; decide
    have hPx : P.x ≠ 0 := fun hx0 => hu_ne0 ((twToMontU_eq_zero_iff hP).mpr hx0)
    have hden := twToMontU_denom_ne_zero hP hPx
    have hfp : (Fp.ofNat P.y + 1) * (Fp.ofNat P.y - 1)⁻¹ = -1 := by
      have := congrArg Fp.ofNat hu
      rw [hm1] at this
      simpa [twToMontU] using this
    have hy0 : Fp.ofNat P.y = 0 := by have := Fp.two_ne_zero; grind
    exact Fp.eq_of_ofNat_eq (twOnCurve_y_lt hP) p25519_pos hy0
  · intro hy0
    apply Fp.eq_of_ofNat_eq (twToMontU_lt P) (by unfold p25519; decide)
    rw [hm1]
    have hfp : Fp.ofNat (twToMontU P) = (Fp.ofNat P.y + 1) * (Fp.ofNat P.y - 1)⁻¹ := by
      unfold twToMontU; simp
    rw [hfp, hy0, Fp.ofNat_zero]
    have hneg1 : (0 : Fp) - 1 ≠ 0 :=
      fp_ne_of_val_ne (by change fpSub 0 (1 % p25519) ≠ 0; unfold fpSub p25519; decide)
    grind

/-- **Complete 4-Torsion Classification on $E_{\text{twist}}(\mathbb{F}_p)$**:
    $[4] P' = \mathcal{O} \iff u(P') \in \{0, p_{25519} - 1\}$. -/
theorem twNatSmul_four_eq_zero_iff_montU {P : EdPoint} (hP : twOnCurve P = true) :
    twNatSmul 4 P = twZero ↔ twToMontU P = 0 ∨ twToMontU P = p25519 - 1 := by
  rw [twNatSmul_four_eq_zero_iff hP, ← twToMontU_eq_zero_iff hP, ← twToMontU_eq_sub_one_iff hP]

private def quarticShift : Nat :=
  48802004052532134862652268456126542835229456083994414501085850622543968879636

private def quarticDisc : Nat :=
  18188081132251925698266448096434822182811072497651735037285882762825192367288

set_option maxRecDepth 20000 in
private theorem not_isSquare_quarticDisc : ¬ FpIsSquare (Fp.ofNat quarticDisc) := by
  apply fp_not_isSquare_of_euler_eq_sub_one
  unfold Fp.ofNat quarticDisc p25519
  decide

private theorem quartic_factor_ring (u a b h D : Fp)
    (hab : a * b = 1) (hhD : h * h - D = 1)
    (hc3 : 2 * h - (a + b) = -4)
    (hc2 : 2 - (a + b) * (2 * h) = -1946650) :
    u * u * u * u - 4 * (u * u * u) - 1946650 * (u * u) - 4 * u + 1 =
      (u - a) * (u - b) * ((u + h) * (u + h) - D) := by
  grind

private theorem dbl_y_quartic_bridge (d x y u : Fp)
    (h121 : (121666 : Fp) * d = -121665)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hy_rel : y * (u + 1) = u - 1) :
    (121666 : Fp) * ((u + 1) * (u + 1) * (u + 1) * (u + 1)) *
        ((1 + d * (y * y)) * (y * y + x * x)) =
      u * u * u * u - 4 * (u * u * u) - 1946650 * (u * u) - 4 * u + 1 := by
  grind

private theorem mul_inv_eq_zero_iff {a b : Fp} (hb : b ≠ 0) :
    a * b⁻¹ = 0 ↔ a = 0 := by
  grind

private theorem up1_ne_zero_and_rel {u y : Fp}
    (h2 : (2 : Fp) ≠ 0) (h1my : 1 - y ≠ 0) (hu : u = (1 + y) * (1 - y)⁻¹) :
    u + 1 ≠ 0 ∧ y * (u + 1) = u - 1 := by
  grind

private theorem zero_iff_roots {c u4 d1 s u a b q : Fp}
    (hc : c ≠ 0) (hu4 : u4 ≠ 0) (hd1 : d1 ≠ 0) (hq : q ≠ 0)
    (hbr : c * u4 * (d1 * s) = (u - a) * (u - b) * q) :
    s = 0 ↔ u = a ∨ u = b := by
  grind

theorem edAdd_self_y_eq_zero_iff_montU {P : EdPoint} (hP : edOnCurve P = true) :
    (edAdd P P).y = 0 ↔ edToMontU P = lowOrderU8a ∨ edToMontU P = lowOrderU8b := by
  have hy_lt : (edAdd P P).y < p25519 := fpMul_lt _ _
  have h_y0 : (edAdd P P).y = 0 ↔ Fp.ofNat P.y * Fp.ofNat P.y + Fp.ofNat P.x * Fp.ofNat P.x = 0 := by
    have h1 : (edAdd P P).y = 0 ↔ Fp.ofNat (edAdd P P).y = 0 :=
      ⟨fun h => by simp [h], fun h => Fp.eq_of_ofNat_eq hy_lt p25519_pos h⟩
    rw [h1, edAdd_fp_y P P]
    exact mul_inv_eq_zero_iff (edAdd_fp_denom_sub_ne_zero hP hP)
  rw [h_y0]
  by_cases hPx : P.x = 0
  · constructor
    · intro hsum
      exfalso
      have hc := edOnCurve_fp_eq hP
      have hx0 : Fp.ofNat P.x = 0 := by simp [hPx]
      have h10 : (1 : Fp) ≠ 0 :=
        fp_ne_of_val_ne (by change 1 % p25519 ≠ 0; unfold p25519; decide)
      grind
    · rintro (hua | hub)
      · have hu0 := (edToMontU_eq_zero_iff hP).mpr hPx
        rw [hu0] at hua; unfold lowOrderU8a at hua; omega
      · have hu0 := (edToMontU_eq_zero_iff hP).mpr hPx
        rw [hu0] at hub; unfold lowOrderU8b at hub; omega
  · have h1my := edToMontU_denom_ne_zero hP hPx
    have hu_def : Fp.ofNat (edToMontU P) = (1 + Fp.ofNat P.y) * (1 - Fp.ofNat P.y)⁻¹ := by
      unfold edToMontU; simp
    obtain ⟨hup1, hy_rel⟩ := up1_ne_zero_and_rel Fp.two_ne_zero h1my hu_def
    have h1dy2 : (1 : Fp) + Fp.ofNat edD * (Fp.ofNat P.y * Fp.ofNat P.y) ≠ 0 := by
      intro h0
      exact Fp.edD_nonsquare ⟨Fp.ofNat sqrtM1 * (Fp.ofNat P.y)⁻¹, by have := Fp.sqrtM1_sq; grind⟩
    have hc := edOnCurve_fp_eq hP
    have hd_rel : (121666 : Fp) * Fp.ofNat edD = -121665 := by
      ext; unfold Fp.ofNat edD p25519; decide
    have hbridge := dbl_y_quartic_bridge (Fp.ofNat edD) (Fp.ofNat P.x) (Fp.ofNat P.y)
      (Fp.ofNat (edToMontU P)) hd_rel hc hy_rel
    have hab : Fp.ofNat lowOrderU8a * Fp.ofNat lowOrderU8b = 1 := by
      ext; unfold Fp.ofNat lowOrderU8a lowOrderU8b p25519; decide
    have hhD : Fp.ofNat quarticShift * Fp.ofNat quarticShift - Fp.ofNat quarticDisc = 1 := by
      ext; unfold Fp.ofNat quarticShift quarticDisc p25519; decide
    have hc3 : 2 * Fp.ofNat quarticShift - (Fp.ofNat lowOrderU8a + Fp.ofNat lowOrderU8b) = -4 := by
      ext; unfold Fp.ofNat quarticShift lowOrderU8a lowOrderU8b p25519; decide
    have hc2 : 2 - (Fp.ofNat lowOrderU8a + Fp.ofNat lowOrderU8b) * (2 * Fp.ofNat quarticShift) =
        -1946650 := by
      ext; unfold Fp.ofNat quarticShift lowOrderU8a lowOrderU8b p25519; decide
    have hfac := quartic_factor_ring (Fp.ofNat (edToMontU P))
      (Fp.ofNat lowOrderU8a) (Fp.ofNat lowOrderU8b)
      (Fp.ofNat quarticShift) (Fp.ofNat quarticDisc) hab hhD hc3 hc2
    rw [hfac] at hbridge
    have hquad_ne : (Fp.ofNat (edToMontU P) + Fp.ofNat quarticShift) *
        (Fp.ofNat (edToMontU P) + Fp.ofNat quarticShift) - Fp.ofNat quarticDisc ≠ 0 := by
      intro hq0
      exact not_isSquare_quarticDisc ⟨Fp.ofNat (edToMontU P) + Fp.ofNat quarticShift, by grind⟩
    have hc121 : (121666 : Fp) ≠ 0 :=
      fp_ne_of_val_ne (by change 121666 % p25519 ≠ 0; unfold p25519; decide)
    have hu4_ne : (Fp.ofNat (edToMontU P) + 1) * (Fp.ofNat (edToMontU P) + 1) *
        (Fp.ofNat (edToMontU P) + 1) * (Fp.ofNat (edToMontU P) + 1) ≠ 0 := by grind
    have hprod_iff := zero_iff_roots hc121 hu4_ne h1dy2 hquad_ne hbridge
    rw [hprod_iff]
    constructor
    · rintro (hua | hub)
      · left; exact Fp.eq_of_ofNat_eq (edToMontU_lt P) (by unfold lowOrderU8a p25519; decide) hua
      · right; exact Fp.eq_of_ofNat_eq (edToMontU_lt P) (by unfold lowOrderU8b p25519; decide) hub
    · rintro (hua | hub)
      · left; rw [hua]
      · right; rw [hub]

/-- **Complete 8-Torsion Classification on $E(\mathbb{F}_p)$**:
    $[8] P = \mathcal{O} \iff u(P) \in \{0, 1, u_{8a}, u_{8b}\}$. -/
theorem edNatSmul_eight_eq_zero_iff_montU {P : EdPoint} (hP : edOnCurve P = true) :
    edNatSmul 8 P = edZero ↔
      edToMontU P = 0 ∨ edToMontU P = 1 ∨
      edToMontU P = lowOrderU8a ∨ edToMontU P = lowOrderU8b := by
  rw [show (8 : Nat) = 4 * 2 from rfl, edNatSmul_mul 4 2 hP, edNatSmul_two hP,
      edNatSmul_four_eq_zero_iff (edOnCurve_edAdd hP hP),
      edAdd_self_x_eq_zero_iff hP, edAdd_self_y_eq_zero_iff_montU hP,
      ← edToMontU_eq_zero_iff hP, ← edToMontU_eq_one_iff hP, or_assoc]


end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist -- proof-setup: allow-public-import

/-!
# Projective Kummer-Line Ladder Soundness on $E(\mathbb{F}_p)$ and $E_{\text{twist}}(\mathbb{F}_p)$ (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer`)

Pure `0-sorry` mathematical proofs for `montDiffAddAndDouble` and `montLadderLoop`:
1. Degenerate $u_1 = 0$ ladder (`montLadderLoop_zero`): every step preserves $U = 0 \lor W = 0$,
   so `fpMul res.U (fpInv res.W) = 0`.
2. Zero-case-split projective Kummer representation `kummerE P Q` on $E(\mathbb{F}_p)$:
   $(U : W) = (\lambda (1 + y) : \lambda (1 - y))$ for $\lambda \in \mathbb{F}_p^\times$,
   preserved unconditionally across `montDiffAddAndDouble` and `montLadderLoop`.
3. Dual zero-case-split projective Kummer representation `kummerTwist P' Q` on $E_{\text{twist}}(\mathbb{F}_p)$:
   $(U : W) = (\lambda (y + 1) : \lambda (y - 1))$ for $\lambda \in \mathbb{F}_p^\times$,
   preserved unconditionally across `montDiffAddAndDouble` and `montLadderLoop`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer

open VerifiedLibraries.Common (
  p25519 fpNeg fpMul fpInv sqrtM1 edD EdPoint edZero edOnCurve edAdd edNeg)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  a24 MontProjPoint montDiffAddAndDouble montLadderLoop)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Field (
  p25519_pos fpMul_lt fpSq_mod fpAdd_zero zero_fpAdd fpNeg_zero fpNeg_fpNeg fpSub_self
  fpSub_zero zero_fpSub fpMul_zero zero_fpMul fpSq_fpNeg fpInv_zero edD_nonsquare)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  Fp edOnCurve_x_lt edOnCurve_fp_eq edOnCurve_edNeg edAdd_fp_y edAdd_fp_denom_sub_ne_zero
  edOnCurve_edAdd edAdd_comm edAdd_edZero edZero_edAdd edAdd_edNeg_self edNeg_edAdd
  edAdd_assoc edNatSmul edNatSmul_succ edOnCurve_edNatSmul edNatSmul_one edNatSmul_add)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  edToMontU edToMontU_lt edToMontU_edNeg)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist1 (
  fp_ne_of_val_ne edDInv fp_edDInv_nonsquare twOnCurve twAdd twZero twNeg twNatSmul twOnCurve_x_lt
  twOnCurve_fp_eq twOnCurve_twNeg twAdd_fp_denom_sub_ne_zero twAdd_fp_y twOnCurve_twAdd
  twAdd_twZero twZero_twAdd twAdd_twNeg_self twAdd_assoc twNatSmul_succ twOnCurve_twNatSmul
  twNatSmul_one twNatSmul_add twToMontU twToMontU_lt)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Twist (
  twToMontU_twNeg edToMontU_denom_ne_zero twToMontU_denom_ne_zero twNeg_twAdd_self)

/-! ## 1. Degenerate $u_1 = 0$ Montgomery Ladder -/

theorem montDiffAddAndDouble_zero {p0 p1 : MontProjPoint}
    (hp0 : p0.U = 0 ∨ p0.W = 0) :
    (montDiffAddAndDouble 0 p0 p1).1.W = 0 ∧
    (montDiffAddAndDouble 0 p0 p1).2.W = 0 := by
  dsimp only [montDiffAddAndDouble]
  refine ⟨?_, zero_fpMul _⟩
  rcases hp0 with hU | hW
  · rw [hU, zero_fpAdd, zero_fpSub, fpSq_mod, fpSq_fpNeg, fpSub_self, zero_fpMul]
  · rw [hW, fpAdd_zero, fpSub_zero, fpSub_self, zero_fpMul]

theorem montLadderLoop_zero_aux (fuel k : Nat) :
    ∀ (x0 x1 : MontProjPoint),
      (x0.U = 0 ∨ x0.W = 0) →
      (x1.U = 0 ∨ x1.W = 0) →
      (montLadderLoop fuel k 0 x0 x1).U = 0 ∨
      (montLadderLoop fuel k 0 x0 x1).W = 0 := by
  induction fuel with
  | zero =>
    intro x0 _ hx0 _
    exact hx0
  | succ f ih =>
    intro x0 x1 hx0 hx1
    unfold montLadderLoop
    by_cases hb : ((k / 2 ^ f) % 2 == 1) = true
    · simp only [hb, ↓reduceIte]
      obtain ⟨hW0, hW1⟩ := montDiffAddAndDouble_zero (p1 := x0) hx1
      exact ih _ _ (Or.inr hW1) (Or.inr hW0)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hW0, hW1⟩ := montDiffAddAndDouble_zero (p1 := x1) hx0
      exact ih _ _ (Or.inr hW0) (Or.inr hW1)

theorem montLadderLoop_zero (fuel k : Nat) :
    let res := montLadderLoop fuel k 0 ⟨1, 0⟩ ⟨0, 1⟩
    fpMul res.U (fpInv res.W) = 0 := by
  rcases montLadderLoop_zero_aux fuel k ⟨1, 0⟩ ⟨0, 1⟩ (Or.inr rfl) (Or.inl rfl) with hU | hW
  · dsimp only; rw [hU, zero_fpMul]
  · dsimp only; rw [hW, fpInv_zero, fpMul_zero]

/-! ## 2. Universal Polynomial Ring & Field Helpers -/

private theorem fp_ofNat_a24 : Fp.ofNat a24 = (121665 : Fp) := by
  ext; unfold Fp.ofNat a24 p25519; decide

private theorem proj_ratio_cancel {lam a b : Fp} (hlam : lam ≠ 0) :
    (lam * a) * (lam * b)⁻¹ = a * b⁻¹ := by
  by_cases hb : b = 0
  · subst hb
    have h0 : (0 : Fp)⁻¹ = 0 := by rw [← Fp.ofNat_zero, ← Fp.ofNat_fpInv, fpInv_zero]
    have hl0 : lam * 0 = 0 := by grind
    rw [hl0, h0]; grind
  · grind

private theorem mul_eq_of_eq_mul_inv {a b c : Fp} (hc : c ≠ 0) (h : a = b * c⁻¹) :
    a * c = b := by
  grind

private theorem inv_ne_zero_of_ne_zero {a : Fp} (ha : a ≠ 0) :
    a⁻¹ ≠ 0 ∧ a * a⁻¹ = 1 := by
  grind

private theorem prod5_ne_zero {a b c d e : Fp}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    a * b * c * d * e ≠ 0 := by
  grind

private theorem prod4_ne_zero {a b c d : Fp}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    a * b * c * d ≠ 0 := by
  grind

private theorem prod3_ne_zero {a b c : Fp}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b * c ≠ 0 := by
  grind

private theorem sq_ne_zero {a : Fp} (ha : a ≠ 0) :
    a * a ≠ 0 := by
  grind

private theorem one_add_edD_mul_sq_ne_zero (t : Fp) :
    (1 : Fp) + Fp.ofNat edD * (t * t) ≠ 0 := by
  intro h0
  exact Fp.edD_nonsquare ⟨Fp.ofNat sqrtM1 * t⁻¹, by have := Fp.sqrtM1_sq; grind⟩

private theorem one_add_edDInv_mul_sq_ne_zero (t : Fp) :
    (1 : Fp) + Fp.ofNat edDInv * (t * t) ≠ 0 := by
  intro h0
  exact fp_edDInv_nonsquare ⟨Fp.ofNat sqrtM1 * t⁻¹, by have := Fp.sqrtM1_sq; grind⟩

private theorem x_eq_zero_of_y_neg_one {c d x y : Fp}
    (hcd : c * (1 + d) = 1)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hy : y + 1 = 0) : x = 0 := by
  grind

theorem edOnCurve_one_add_y_ne_zero {P : EdPoint} (hP : edOnCurve P = true) (hx : P.x ≠ 0) :
    (1 : Fp) + Fp.ofNat P.y ≠ 0 := by
  intro h0
  have hcd : (121666 : Fp) * (1 + Fp.ofNat edD) = 1 := by
    ext; unfold Fp.ofNat edD p25519; decide
  have hy : Fp.ofNat P.y + 1 = 0 := by grind
  have hx0 := x_eq_zero_of_y_neg_one hcd (edOnCurve_fp_eq hP) hy
  exact hx (Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos hx0)

theorem twOnCurve_y_add_one_ne_zero {P : EdPoint} (hP : twOnCurve P = true) (hx : P.x ≠ 0) :
    Fp.ofNat P.y + 1 ≠ 0 := by
  intro h0
  have hcd : (-(121665 : Fp)) * (1 + Fp.ofNat edDInv) = 1 := by
    ext; unfold Fp.ofNat edDInv p25519; decide
  have hx0 := x_eq_zero_of_y_neg_one hcd (twOnCurve_fp_eq hP) h0
  exact hx (Fp.eq_of_ofNat_eq (twOnCurve_x_lt hP) p25519_pos hx0)

/-- Universal twisted-Edwards differential-addition sum identity (pure `CommRing`). -/
private theorem universal_diffadd_plus (d x y xq yq : Fp)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hcq : -(xq * xq) + yq * yq = 1 + d * ((xq * xq) * (yq * yq))) :
    (1 + d * (y * y)) * (1 + d * (yq * yq)) *
      ((1 - d * ((xq * x) * (yq * y))) + (yq * y + xq * x)) *
      ((1 + d * ((xq * x) * (yq * y))) + (yq * y - xq * x)) =
    (1 + d) * (1 + d * ((y * yq) * (y * yq))) * ((yq + y) * (yq + y)) := by
  grind

/-- Universal twisted-Edwards differential-addition difference identity (pure `CommRing`). -/
private theorem universal_diffadd_minus (d x y xq yq : Fp)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hcq : -(xq * xq) + yq * yq = 1 + d * ((xq * xq) * (yq * yq))) :
    (1 + d * (y * y)) * (1 + d * (yq * yq)) *
      ((1 - d * ((xq * x) * (yq * y))) - (yq * y + xq * x)) *
      ((1 + d * ((xq * x) * (yq * y))) - (yq * y - xq * x)) =
    (1 + d) * (1 + d * ((y * yq) * (y * yq))) * ((yq - y) * (yq - y)) := by
  grind

private theorem aabb_kummerE (y lam2 PU PW : Fp)
    (hPU : PU = lam2 * (1 + y)) (hPW : PW = lam2 * (1 - y)) :
    ((PU + PW) * (PU + PW)) * ((PU - PW) * (PU - PW)) =
      (lam2 * lam2 * lam2 * lam2) * ((16 : Fp) * (y * y)) ∧
    ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW)) *
      ((PU + PW) * (PU + PW) + (121665 : Fp) *
        ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW))) =
      (lam2 * lam2 * lam2 * lam2) *
        ((16 : Fp) * ((1 - y * y) * ((121666 : Fp) - (121665 : Fp) * (y * y)))) := by
  subst hPU; subst hPW; grind

private theorem dbl_curve_E (d x y y2 dm : Fp)
    (hd : (121666 : Fp) * d = -121665)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hdm : dm = 1 - d * ((x * x) * (y * y)))
    (hy2 : y2 * dm = y * y + x * x) :
    (16 : Fp) * (y * y) = ((8 * 121666 : Fp) * (1 + d * (y * y)) * dm) * (1 + y2) ∧
    (16 : Fp) * ((1 - y * y) * ((121666 : Fp) - (121665 : Fp) * (y * y))) =
      ((8 * 121666 : Fp) * (1 + d * (y * y)) * dm) * (1 - y2) := by
  subst hdm; grind

private theorem dbl_kummerE_U2 (d x y y2 dm lam2 PU PW : Fp)
    (hd : (121666 : Fp) * d = -121665)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hdm : dm = 1 - d * ((x * x) * (y * y)))
    (hy2 : y2 * dm = y * y + x * x)
    (hPU : PU = lam2 * (1 + y)) (hPW : PW = lam2 * (1 - y)) :
    ((PU + PW) * (PU + PW)) * ((PU - PW) * (PU - PW)) =
      ((8 * 121666 : Fp) * (lam2 * lam2 * lam2 * lam2) * (1 + d * (y * y)) * dm) * (1 + y2) := by
  rw [(aabb_kummerE y lam2 PU PW hPU hPW).1, (dbl_curve_E d x y y2 dm hd hc hdm hy2).1]
  grind

private theorem dbl_kummerE_W2 (d x y y2 dm lam2 PU PW : Fp)
    (hd : (121666 : Fp) * d = -121665)
    (hc : -(x * x) + y * y = 1 + d * ((x * x) * (y * y)))
    (hdm : dm = 1 - d * ((x * x) * (y * y)))
    (hy2 : y2 * dm = y * y + x * x)
    (hPU : PU = lam2 * (1 + y)) (hPW : PW = lam2 * (1 - y)) :
    ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW)) *
      ((PU + PW) * (PU + PW) + (121665 : Fp) *
        ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW))) =
      ((8 * 121666 : Fp) * (lam2 * lam2 * lam2 * lam2) * (1 + d * (y * y)) * dm) * (1 - y2) := by
  rw [(aabb_kummerE y lam2 PU PW hPU hPW).2, (dbl_curve_E d x y y2 dm hd hc hdm hy2).2]
  grind

private theorem aabb_kummerTwist (y lam2 PU PW : Fp)
    (hPU : PU = lam2 * (y + 1)) (hPW : PW = lam2 * (y - 1)) :
    ((PU + PW) * (PU + PW)) * ((PU - PW) * (PU - PW)) =
      (lam2 * lam2 * lam2 * lam2) * ((16 : Fp) * (y * y)) ∧
    ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW)) *
      ((PU + PW) * (PU + PW) + (121665 : Fp) *
        ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW))) =
      (lam2 * lam2 * lam2 * lam2) *
        ((16 : Fp) * ((y * y - 1) * ((121666 : Fp) * (y * y) - (121665 : Fp)))) := by
  subst hPU; subst hPW; grind

private theorem dbl_curve_Twist (di x y y2 dm : Fp)
    (hdi : (121665 : Fp) * di = -121666)
    (hc : -(x * x) + y * y = 1 + di * ((x * x) * (y * y)))
    (hdm : dm = 1 - di * ((x * x) * (y * y)))
    (hy2 : y2 * dm = y * y + x * x) :
    (16 : Fp) * (y * y) = ((-(8 * 121665 : Fp)) * (1 + di * (y * y)) * dm) * (y2 + 1) ∧
    (16 : Fp) * ((y * y - 1) * ((121666 : Fp) * (y * y) - (121665 : Fp))) =
      ((-(8 * 121665 : Fp)) * (1 + di * (y * y)) * dm) * (y2 - 1) := by
  subst hdm; grind

private theorem dbl_kummerTwist_U2 (di x y y2 dm lam2 PU PW : Fp)
    (hdi : (121665 : Fp) * di = -121666)
    (hc : -(x * x) + y * y = 1 + di * ((x * x) * (y * y)))
    (hdm : dm = 1 - di * ((x * x) * (y * y)))
    (hy2 : y2 * dm = y * y + x * x)
    (hPU : PU = lam2 * (y + 1)) (hPW : PW = lam2 * (y - 1)) :
    ((PU + PW) * (PU + PW)) * ((PU - PW) * (PU - PW)) =
      ((-(8 * 121665 : Fp)) * (lam2 * lam2 * lam2 * lam2) *
        (1 + di * (y * y)) * dm) * (y2 + 1) := by
  rw [(aabb_kummerTwist y lam2 PU PW hPU hPW).1, (dbl_curve_Twist di x y y2 dm hdi hc hdm hy2).1]
  grind

private theorem dbl_kummerTwist_W2 (di x y y2 dm lam2 PU PW : Fp)
    (hdi : (121665 : Fp) * di = -121666)
    (hc : -(x * x) + y * y = 1 + di * ((x * x) * (y * y)))
    (hdm : dm = 1 - di * ((x * x) * (y * y)))
    (hy2 : y2 * dm = y * y + x * x)
    (hPU : PU = lam2 * (y + 1)) (hPW : PW = lam2 * (y - 1)) :
    ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW)) *
      ((PU + PW) * (PU + PW) + (121665 : Fp) *
        ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW))) =
      ((-(8 * 121665 : Fp)) * (lam2 * lam2 * lam2 * lam2) *
        (1 + di * (y * y)) * dm) * (y2 - 1) := by
  rw [(aabb_kummerTwist y lam2 PU PW hPU hPW).2, (dbl_curve_Twist di x y y2 dm hdi hc hdm hy2).2]
  grind

private theorem dacb_kummerE (y yq lam2 lam3 PU PW QU QW : Fp)
    (hPU : PU = lam2 * (1 + y)) (hPW : PW = lam2 * (1 - y))
    (hQU : QU = lam3 * (1 + yq)) (hQW : QW = lam3 * (1 - yq)) :
    ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) *
      ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) =
      (16 : Fp) * (lam2 * lam2) * (lam3 * lam3) * ((yq + y) * (yq + y)) ∧
    ((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW)) *
      ((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW)) =
      (16 : Fp) * (lam2 * lam2) * (lam3 * lam3) * ((yq - y) * (yq - y)) := by
  grind

private theorem dacb_kummerTwist (y yq lam2 lam3 PU PW QU QW : Fp)
    (hPU : PU = lam2 * (y + 1)) (hPW : PW = lam2 * (y - 1))
    (hQU : QU = lam3 * (yq + 1)) (hQW : QW = lam3 * (yq - 1)) :
    ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) *
      ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) =
      (16 : Fp) * (lam2 * lam2) * (lam3 * lam3) * ((yq + y) * (yq + y)) ∧
    ((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW)) *
      ((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW)) =
      (16 : Fp) * (lam2 * lam2) * (lam3 * lam3) * ((yq - y) * (yq - y)) := by
  grind

private theorem combine_diffadd_E
    (c d l16 f1 f2 fyy inv_yy dm dp splus sminus yr y1 u1f Splus Sminus : Fp)
    (hcd : c * (1 + d) = 1)
    (hinv : fyy * inv_yy = 1)
    (hyr : yr * dm = splus)
    (hy1 : y1 * dp = sminus)
    (hu1 : u1f * (1 - y1) = 1 + y1)
    (h1my1 : 1 - y1 ≠ 0)
    (hp : f1 * f2 * (dm + splus) * (dp + sminus) = (1 + d) * fyy * Splus)
    (hm : f1 * f2 * (dm - splus) * (dp - sminus) = (1 + d) * fyy * Sminus) :
    l16 * Splus = (l16 * c * f1 * f2 * inv_yy * (1 + y1) * dm * dp) * (1 + yr) ∧
    u1f * (l16 * Sminus) = (l16 * c * f1 * f2 * inv_yy * (1 + y1) * dm * dp) * (1 - yr) := by
  grind

private theorem combine_diffadd_Twist
    (c di l16 f1 f2 fyy inv_yy dm dp splus sminus yr y1 u1f Splus Sminus : Fp)
    (hcd : c * (1 + di) = 1)
    (hinv : fyy * inv_yy = 1)
    (hyr : yr * dm = splus)
    (hy1 : y1 * dp = sminus)
    (hu1 : u1f * (y1 - 1) = y1 + 1)
    (hy1m1 : y1 - 1 ≠ 0)
    (hp : f1 * f2 * (dm + splus) * (dp + sminus) = (1 + di) * fyy * Splus)
    (hm : f1 * f2 * (dm - splus) * (dp - sminus) = (1 + di) * fyy * Sminus) :
    l16 * Splus = (l16 * c * f1 * f2 * inv_yy * (y1 + 1) * dm * dp) * (yr + 1) ∧
    u1f * (l16 * Sminus) = (l16 * c * f1 * f2 * inv_yy * (y1 + 1) * dm * dp) * (yr - 1) := by
  grind

private theorem montDiffAddAndDouble_fp (u1 : Nat) (p0 p1 : MontProjPoint) :
    let q := montDiffAddAndDouble u1 p0 p1
    let PU := Fp.ofNat p0.U
    let PW := Fp.ofNat p0.W
    let QU := Fp.ofNat p1.U
    let QW := Fp.ofNat p1.W
    Fp.ofNat q.1.U = ((PU + PW) * (PU + PW)) * ((PU - PW) * (PU - PW)) ∧
    Fp.ofNat q.1.W = ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW)) *
      ((PU + PW) * (PU + PW) + (121665 : Fp) *
        ((PU + PW) * (PU + PW) - (PU - PW) * (PU - PW))) ∧
    Fp.ofNat q.2.U =
      ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) *
        ((QU - QW) * (PU + PW) + (QU + QW) * (PU - PW)) ∧
    Fp.ofNat q.2.W = Fp.ofNat u1 *
      (((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW)) *
        ((QU - QW) * (PU + PW) - (QU + QW) * (PU - PW))) := by
  dsimp only [montDiffAddAndDouble]
  simp [fp_ofNat_a24]

private theorem mod_pow_two_succ (k f : Nat) :
    k % 2 ^ (f + 1) = ((k / 2 ^ f) % 2) * 2 ^ f + k % 2 ^ f := by
  have hp : 2 ^ (f + 1) = 2 ^ f * 2 := Nat.pow_succ 2 f
  have hdiv := Nat.div_add_mod k (2 ^ f)
  let q := (k / 2 ^ f) / 2
  let b := (k / 2 ^ f) % 2
  have hq : 2 * q + b = k / 2 ^ f := Nat.div_add_mod (k / 2 ^ f) 2
  have hr_lt : k % 2 ^ f < 2 ^ f := Nat.mod_lt k (Nat.two_pow_pos f)
  have hb_lt : b < 2 := Nat.mod_lt _ (by decide)
  have hrem_lt : b * 2 ^ f + k % 2 ^ f < 2 ^ (f + 1) := by
    rw [hp]
    rcases (by omega : b = 0 ∨ b = 1) with hb | hb
    · rw [hb, Nat.zero_mul, Nat.zero_add]; omega
    · rw [hb, Nat.one_mul]; omega
  have hk_eq : k = 2 ^ (f + 1) * q + (b * 2 ^ f + k % 2 ^ f) := by
    calc k = 2 ^ f * (k / 2 ^ f) + k % 2 ^ f := hdiv.symm
      _ = 2 ^ f * (2 * q + b) + k % 2 ^ f := by rw [← hq]
      _ = 2 ^ (f + 1) * q + (b * 2 ^ f + k % 2 ^ f) := by
        rw [hp, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ f) b, Nat.add_assoc]
  conv => lhs; rw [hk_eq]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrem_lt]

private theorem ladder_exp_step (m b k f : Nat) (hbit : (k / 2 ^ f) % 2 = b) :
    (2 * m + b) * 2 ^ f + k % 2 ^ f = m * 2 ^ (f + 1) + k % 2 ^ (f + 1) := by
  rw [mod_pow_two_succ k f, hbit, Nat.pow_succ, Nat.add_mul,
      Nat.mul_comm 2 m, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm 2 (2 ^ f)]

private theorem montLadderLoop_zero_fuel (k u1 : Nat) (x0 x1 : MontProjPoint) :
    montLadderLoop 0 k u1 x0 x1 = x0 := rfl

/-! ## 3. Projective Kummer Representation on $E(\mathbb{F}_p)$ (`kummerE`) -/

/-- Projective Kummer-line representation on $E(\mathbb{F}_p)$:
    $(U : W) = (\lambda (1 + y) : \lambda (1 - y))$ for some $\lambda \in \mathbb{F}_p^\times$. -/
@[expose] def kummerE (P : EdPoint) (Q : MontProjPoint) : Prop :=
  ∃ lam : Fp, lam ≠ 0 ∧
    Fp.ofNat Q.U = lam * (1 + Fp.ofNat P.y) ∧
    Fp.ofNat Q.W = lam * (1 - Fp.ofNat P.y)

theorem kummerE_edZero : kummerE edZero ⟨1, 0⟩ := by
  refine ⟨(2 : Fp)⁻¹, (inv_ne_zero_of_ne_zero Fp.two_ne_zero).1, ?_, ?_⟩
  · have h2 := Fp.two_ne_zero
    dsimp only [edZero]; simp only [Fp.ofNat_one]
    grind
  · dsimp only [edZero]; simp only [Fp.ofNat_zero, Fp.ofNat_one]
    grind

theorem kummerE_init {P1 : EdPoint} (hP1 : edOnCurve P1 = true) (hx : P1.x ≠ 0) :
    kummerE P1 ⟨edToMontU P1, 1⟩ := by
  have h1my := edToMontU_denom_ne_zero hP1 hx
  refine ⟨(1 - Fp.ofNat P1.y)⁻¹, (inv_ne_zero_of_ne_zero h1my).1, ?_, ?_⟩
  · unfold edToMontU; simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpInv,
      Fp.ofNat_fpSub, Fp.ofNat_one]
    grind
  · simp only [Fp.ofNat_one]
    grind

theorem kummerE_toMontU {P : EdPoint} {Q : MontProjPoint} (hk : kummerE P Q) :
    fpMul Q.U (fpInv Q.W) = edToMontU P := by
  obtain ⟨lam, hlam, hU, hW⟩ := hk
  apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) (edToMontU_lt P)
  unfold edToMontU
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_one,
    hU, hW]
  exact proj_ratio_cancel hlam

theorem montDiffAddAndDouble_kummerE
    {u1 : Nat} {P Q Q1 : EdPoint} {p0 p1 : MontProjPoint}
    (hP : edOnCurve P = true) (hQ : edOnCurve Q = true)
    (hQ1_eq : edAdd Q (edNeg P) = Q1)
    (hQ1x : Q1.x ≠ 0) (hu1 : edToMontU Q1 = u1)
    (hk0 : kummerE P p0) (hk1 : kummerE Q p1) :
    kummerE (edAdd P P) (montDiffAddAndDouble u1 p0 p1).1 ∧
    kummerE (edAdd Q P) (montDiffAddAndDouble u1 p0 p1).2 := by
  obtain ⟨lam2, hlam2, hPU, hPW⟩ := hk0
  obtain ⟨lam3, hlam3, hQU, hQW⟩ := hk1
  obtain ⟨hfU2, hfW2, hfU3, hfW3⟩ := montDiffAddAndDouble_fp u1 p0 p1
  have hQ1 : edOnCurve Q1 = true := hQ1_eq ▸ edOnCurve_edAdd hQ (edOnCurve_edNeg hP)
  have hd_rel : (121666 : Fp) * Fp.ofNat edD = -121665 := by
    ext; unfold Fp.ofNat edD p25519; decide
  have hcd : (121666 : Fp) * (1 + Fp.ofNat edD) = 1 := by
    ext; unfold Fp.ofNat edD p25519; decide
  constructor
  · -- Doubling: q0 represents edAdd P P
    have hdm2_ne := edAdd_fp_denom_sub_ne_zero hP hP
    have hy2 := mul_eq_of_eq_mul_inv hdm2_ne (edAdd_fp_y P P)
    have h8_ne : (8 * 121666 : Fp) ≠ 0 :=
      fp_ne_of_val_ne (by change fpMul (8 % p25519) (121666 % p25519) ≠ 0; unfold fpMul p25519; decide)
    have hl4_ne : lam2 * lam2 * lam2 * lam2 ≠ 0 :=
      prod4_ne_zero hlam2 hlam2 hlam2 hlam2
    have hf1_ne := one_add_edD_mul_sq_ne_zero (Fp.ofNat P.y)
    refine ⟨(8 * 121666 : Fp) * (lam2 * lam2 * lam2 * lam2) *
        (1 + Fp.ofNat edD * (Fp.ofNat P.y * Fp.ofNat P.y)) *
        (1 - Fp.ofNat edD * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y))),
      prod4_ne_zero h8_ne hl4_ne hf1_ne hdm2_ne, ?_, ?_⟩
    · rw [hfU2]
      exact dbl_kummerE_U2 _ _ _ _ _ _ _ _ hd_rel (edOnCurve_fp_eq hP) rfl hy2 hPU hPW
    · rw [hfW2]
      exact dbl_kummerE_W2 _ _ _ _ _ _ _ _ hd_rel (edOnCurve_fp_eq hP) rfl hy2 hPU hPW
  · -- Differential addition: q1 represents edAdd Q P
    have hdm_ne := edAdd_fp_denom_sub_ne_zero hQ hP
    have hyr := mul_eq_of_eq_mul_inv hdm_ne (edAdd_fp_y Q P)
    have hneg_x : Fp.ofNat (edNeg P).x = -Fp.ofNat P.x := by
      dsimp only [edNeg]; simp
    have hneg_y : Fp.ofNat (edNeg P).y = Fp.ofNat P.y := by
      dsimp only [edNeg]; simp
    have hdp_raw := edAdd_fp_denom_sub_ne_zero hQ (edOnCurve_edNeg hP)
    have hy1_raw := hQ1_eq ▸ edAdd_fp_y Q (edNeg P)
    rw [hneg_x, hneg_y] at hdp_raw hy1_raw
    have hdp_eq : (1 : Fp) - Fp.ofNat edD *
        ((Fp.ofNat Q.x * -Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y)) =
        1 + Fp.ofNat edD * ((Fp.ofNat Q.x * Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y)) := by
      grind
    have hnum_eq : Fp.ofNat Q.y * Fp.ofNat P.y + Fp.ofNat Q.x * -Fp.ofNat P.x =
        Fp.ofNat Q.y * Fp.ofNat P.y - Fp.ofNat Q.x * Fp.ofNat P.x := by grind
    rw [hdp_eq] at hdp_raw hy1_raw
    rw [hnum_eq] at hy1_raw
    have hy1 := mul_eq_of_eq_mul_inv hdp_raw hy1_raw
    have h1my1 := edToMontU_denom_ne_zero hQ1 hQ1x
    have h1py1 := edOnCurve_one_add_y_ne_zero hQ1 hQ1x
    have hu1_fp : Fp.ofNat u1 = (1 + Fp.ofNat Q1.y) * (1 - Fp.ofNat Q1.y)⁻¹ := by
      rw [← hu1]; unfold edToMontU; simp
    have hu1_rel := mul_eq_of_eq_mul_inv h1my1 hu1_fp
    have hf1_ne := one_add_edD_mul_sq_ne_zero (Fp.ofNat P.y)
    have hf2_ne := one_add_edD_mul_sq_ne_zero (Fp.ofNat Q.y)
    have hfyy_ne := one_add_edD_mul_sq_ne_zero (Fp.ofNat P.y * Fp.ofNat Q.y)
    obtain ⟨hinv_ne, hinv_eq⟩ := inv_ne_zero_of_ne_zero hfyy_ne
    obtain ⟨hdacb_p, hdacb_m⟩ := dacb_kummerE _ _ _ _ _ _ _ _ hPU hPW hQU hQW
    have hup := universal_diffadd_plus _ _ _ _ _ (edOnCurve_fp_eq hP) (edOnCurve_fp_eq hQ)
    have hum := universal_diffadd_minus _ _ _ _ _ (edOnCurve_fp_eq hP) (edOnCurve_fp_eq hQ)
    obtain ⟨hU3_eq, hW3_eq⟩ := combine_diffadd_E
      (121666 : Fp) (Fp.ofNat edD) ((16 : Fp) * (lam2 * lam2) * (lam3 * lam3))
      _ _ _ _ _ _ _ _ _ _ _ _ _
      hcd hinv_eq hyr hy1 hu1_rel h1my1 hup hum
    have hl16_ne : (16 : Fp) * (lam2 * lam2) * (lam3 * lam3) ≠ 0 :=
      prod3_ne_zero (fp_ne_of_val_ne (by change 16 % p25519 ≠ 0; unfold p25519; decide))
        (sq_ne_zero hlam2) (sq_ne_zero hlam3)
    have hc_ne : (121666 : Fp) ≠ 0 :=
      fp_ne_of_val_ne (by change 121666 % p25519 ≠ 0; unfold p25519; decide)
    refine ⟨((16 : Fp) * (lam2 * lam2) * (lam3 * lam3)) * (121666 : Fp) *
        (1 + Fp.ofNat edD * (Fp.ofNat P.y * Fp.ofNat P.y)) *
        (1 + Fp.ofNat edD * (Fp.ofNat Q.y * Fp.ofNat Q.y)) *
        (1 + Fp.ofNat edD * ((Fp.ofNat P.y * Fp.ofNat Q.y) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ *
        (1 + Fp.ofNat Q1.y) *
        (1 - Fp.ofNat edD * ((Fp.ofNat Q.x * Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y))) *
        (1 + Fp.ofNat edD * ((Fp.ofNat Q.x * Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y))),
      prod5_ne_zero (prod4_ne_zero hl16_ne hc_ne hf1_ne hf2_ne) hinv_ne h1py1 hdm_ne hdp_raw,
      ?_, ?_⟩
    · rw [hfU3, hdacb_p]; exact hU3_eq
    · rw [hfW3, hdacb_m]; exact hW3_eq

private theorem edNeg_x_ne_zero {P : EdPoint} (hP : edOnCurve P = true) (hx : P.x ≠ 0) :
    (edNeg P).x ≠ 0 := by
  intro h0
  dsimp only [edNeg] at h0
  have h := congrArg fpNeg h0
  rw [fpNeg_fpNeg, fpNeg_zero, Nat.mod_eq_of_lt (edOnCurve_x_lt hP)] at h
  exact hx h

private theorem edAdd_succ_sub_self (m : Nat) {P1 : EdPoint} (hP1 : edOnCurve P1 = true) :
    edAdd (edNatSmul (m + 1) P1) (edNeg (edNatSmul m P1)) = P1 := by
  have hm := edOnCurve_edNatSmul m hP1
  rw [edNatSmul_succ, edAdd_assoc hP1 hm (edOnCurve_edNeg hm),
      edAdd_edNeg_self hm, edAdd_edZero hP1]

private theorem edAdd_sub_succ_self (m : Nat) {P1 : EdPoint} (hP1 : edOnCurve P1 = true) :
    edAdd (edNatSmul m P1) (edNeg (edNatSmul (m + 1) P1)) = edNeg P1 := by
  have hm := edOnCurve_edNatSmul m hP1
  rw [edNatSmul_succ, edNeg_edAdd, edAdd_comm (edNeg P1) (edNeg (edNatSmul m P1)),
      ← edAdd_assoc hm (edOnCurve_edNeg hm) (edOnCurve_edNeg hP1),
      edAdd_edNeg_self hm, edZero_edAdd (edOnCurve_edNeg hP1)]

theorem montLadderLoop_kummerE_aux (fuel k : Nat) {P1 : EdPoint}
    (hP1 : edOnCurve P1 = true) (hP1x : P1.x ≠ 0) :
    ∀ (m : Nat) (x0 x1 : MontProjPoint),
      kummerE (edNatSmul m P1) x0 →
      kummerE (edNatSmul (m + 1) P1) x1 →
      kummerE (edNatSmul (m * 2 ^ fuel + k % 2 ^ fuel) P1)
        (montLadderLoop fuel k (edToMontU P1) x0 x1) := by
  induction fuel with
  | zero =>
    intro m x0 _ hk0 _
    have hm : m * 2 ^ 0 + k % 2 ^ 0 = m := by
      rw [Nat.pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero]
    rw [montLadderLoop_zero_fuel, hm]
    exact hk0
  | succ f ih =>
    intro m x0 x1 hk0 hk1
    have hm_on := edOnCurve_edNatSmul m hP1
    have hm1_on := edOnCurve_edNatSmul (m + 1) hP1
    dsimp only [montLadderLoop]
    by_cases hb : ((k / 2 ^ f) % 2 == 1) = true
    · simp only [hb, ↓reduceIte]
      have hbit : (k / 2 ^ f) % 2 = 1 := beq_iff_eq.mp hb
      obtain ⟨hq0, hq1⟩ := montDiffAddAndDouble_kummerE
        hm1_on hm_on (edAdd_sub_succ_self m hP1)
        (edNeg_x_ne_zero hP1 hP1x) (edToMontU_edNeg P1) hk1 hk0
      have h2m1 : edAdd (edNatSmul m P1) (edNatSmul (m + 1) P1) =
          edNatSmul (2 * m + 1) P1 := by
        rw [← edNatSmul_add m (m + 1) hP1]
        exact congrArg (edNatSmul · P1) (by omega)
      have h2m2 : edAdd (edNatSmul (m + 1) P1) (edNatSmul (m + 1) P1) =
          edNatSmul ((2 * m + 1) + 1) P1 := by
        rw [← edNatSmul_add (m + 1) (m + 1) hP1]
        exact congrArg (edNatSmul · P1) (by omega)
      rw [h2m1] at hq1
      rw [h2m2] at hq0
      have hstep := ih (2 * m + 1) _ _ hq1 hq0
      rwa [ladder_exp_step m 1 k f hbit] at hstep
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hbit : (k / 2 ^ f) % 2 = 0 := by
        have hne : (k / 2 ^ f) % 2 ≠ 1 := fun h => hb (beq_iff_eq.mpr h)
        omega
      obtain ⟨hq0, hq1⟩ := montDiffAddAndDouble_kummerE
        hm_on hm1_on (edAdd_succ_sub_self m hP1) hP1x rfl hk0 hk1
      have h2m : edAdd (edNatSmul m P1) (edNatSmul m P1) = edNatSmul (2 * m) P1 := by
        rw [← edNatSmul_add m m hP1]
        exact congrArg (edNatSmul · P1) (by omega)
      have h2m1 : edAdd (edNatSmul (m + 1) P1) (edNatSmul m P1) =
          edNatSmul (2 * m + 1) P1 := by
        rw [← edNatSmul_add (m + 1) m hP1]
        exact congrArg (edNatSmul · P1) (by omega)
      rw [h2m] at hq0
      rw [h2m1] at hq1
      have hstep := ih (2 * m) _ _ hq0 hq1
      have hexp := ladder_exp_step m 0 k f hbit
      rw [Nat.add_zero] at hexp
      rwa [hexp] at hstep

/-- **Montgomery 255-Step Ladder Soundness on $E(\mathbb{F}_p)$**:
    For any $P_1 \in E(\mathbb{F}_p)$ with $P_1.x \ne 0$ and any $k < 2^{255}$,
    running `montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩` computes $u([k] P_1)$. -/
theorem montLadderLoop_255_edToMontU {k : Nat} {P1 : EdPoint}
    (hk : k < 2 ^ 255) (hP1 : edOnCurve P1 = true) (hP1x : P1.x ≠ 0) :
    let u1 := edToMontU P1
    let res := montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩
    fpMul res.U (fpInv res.W) = edToMontU (edNatSmul k P1) := by
  dsimp only
  have hk0 : kummerE (edNatSmul 0 P1) ⟨1, 0⟩ := kummerE_edZero
  have hk1 : kummerE (edNatSmul (0 + 1) P1) ⟨edToMontU P1, 1⟩ := by
    rw [Nat.zero_add, edNatSmul_one hP1]
    exact kummerE_init hP1 hP1x
  have hloop := montLadderLoop_kummerE_aux 255 k hP1 hP1x 0 _ _ hk0 hk1
  rw [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hk] at hloop
  exact kummerE_toMontU hloop

/-! ## 4. Projective Kummer Representation on $E_{\text{twist}}(\mathbb{F}_p)$ (`kummerTwist`) -/

/-- Projective Kummer-line representation on $E_{\text{twist}}(\mathbb{F}_p)$:
    $(U : W) = (\lambda (y + 1) : \lambda (y - 1))$ for some $\lambda \in \mathbb{F}_p^\times$. -/
@[expose] def kummerTwist (P : EdPoint) (Q : MontProjPoint) : Prop :=
  ∃ lam : Fp, lam ≠ 0 ∧
    Fp.ofNat Q.U = lam * (Fp.ofNat P.y + 1) ∧
    Fp.ofNat Q.W = lam * (Fp.ofNat P.y - 1)

theorem kummerTwist_twZero : kummerTwist twZero ⟨1, 0⟩ := by
  refine ⟨(2 : Fp)⁻¹, (inv_ne_zero_of_ne_zero Fp.two_ne_zero).1, ?_, ?_⟩
  · have h2 := Fp.two_ne_zero
    dsimp only [twZero, edZero]; simp only [Fp.ofNat_one]
    grind
  · dsimp only [twZero, edZero]; simp only [Fp.ofNat_zero, Fp.ofNat_one]
    grind

theorem kummerTwist_init {P1 : EdPoint} (hP1 : twOnCurve P1 = true) (hx : P1.x ≠ 0) :
    kummerTwist P1 ⟨twToMontU P1, 1⟩ := by
  have hy1 := twToMontU_denom_ne_zero hP1 hx
  refine ⟨(Fp.ofNat P1.y - 1)⁻¹, (inv_ne_zero_of_ne_zero hy1).1, ?_, ?_⟩
  · unfold twToMontU; simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpInv,
      Fp.ofNat_fpSub, Fp.ofNat_one]
    grind
  · simp only [Fp.ofNat_one]
    grind

theorem kummerTwist_toMontU {P : EdPoint} {Q : MontProjPoint} (hk : kummerTwist P Q) :
    fpMul Q.U (fpInv Q.W) = twToMontU P := by
  obtain ⟨lam, hlam, hU, hW⟩ := hk
  apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) (twToMontU_lt P)
  unfold twToMontU
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpInv, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_one,
    hU, hW]
  exact proj_ratio_cancel hlam

theorem montDiffAddAndDouble_kummerTwist
    {u1 : Nat} {P Q Q1 : EdPoint} {p0 p1 : MontProjPoint}
    (hP : twOnCurve P = true) (hQ : twOnCurve Q = true)
    (hQ1_eq : twAdd Q (twNeg P) = Q1)
    (hQ1x : Q1.x ≠ 0) (hu1 : twToMontU Q1 = u1)
    (hk0 : kummerTwist P p0) (hk1 : kummerTwist Q p1) :
    kummerTwist (twAdd P P) (montDiffAddAndDouble u1 p0 p1).1 ∧
    kummerTwist (twAdd Q P) (montDiffAddAndDouble u1 p0 p1).2 := by
  obtain ⟨lam2, hlam2, hPU, hPW⟩ := hk0
  obtain ⟨lam3, hlam3, hQU, hQW⟩ := hk1
  obtain ⟨hfU2, hfW2, hfU3, hfW3⟩ := montDiffAddAndDouble_fp u1 p0 p1
  have hQ1 : twOnCurve Q1 = true := hQ1_eq ▸ twOnCurve_twAdd hQ (twOnCurve_twNeg hP)
  have hdi_rel : (121665 : Fp) * Fp.ofNat edDInv = -121666 := by
    ext; unfold Fp.ofNat edDInv p25519; decide
  have hcd : (-(121665 : Fp)) * (1 + Fp.ofNat edDInv) = 1 := by
    ext; unfold Fp.ofNat edDInv p25519; decide
  constructor
  · -- Doubling: q0 represents twAdd P P
    have hdm2_ne := twAdd_fp_denom_sub_ne_zero hP hP
    have hy2 := mul_eq_of_eq_mul_inv hdm2_ne (twAdd_fp_y P P)
    have h8_ne : (-(8 * 121665 : Fp)) ≠ 0 :=
      fp_ne_of_val_ne (by change fpNeg (fpMul (8 % p25519) (121665 % p25519)) ≠ 0; unfold fpNeg fpMul p25519; decide)
    have hl4_ne : lam2 * lam2 * lam2 * lam2 ≠ 0 :=
      prod4_ne_zero hlam2 hlam2 hlam2 hlam2
    have hf1_ne := one_add_edDInv_mul_sq_ne_zero (Fp.ofNat P.y)
    refine ⟨(-(8 * 121665 : Fp)) * (lam2 * lam2 * lam2 * lam2) *
        (1 + Fp.ofNat edDInv * (Fp.ofNat P.y * Fp.ofNat P.y)) *
        (1 - Fp.ofNat edDInv * ((Fp.ofNat P.x * Fp.ofNat P.x) * (Fp.ofNat P.y * Fp.ofNat P.y))),
      prod4_ne_zero h8_ne hl4_ne hf1_ne hdm2_ne, ?_, ?_⟩
    · rw [hfU2]
      exact dbl_kummerTwist_U2 _ _ _ _ _ _ _ _ hdi_rel (twOnCurve_fp_eq hP) rfl hy2 hPU hPW
    · rw [hfW2]
      exact dbl_kummerTwist_W2 _ _ _ _ _ _ _ _ hdi_rel (twOnCurve_fp_eq hP) rfl hy2 hPU hPW
  · -- Differential addition: q1 represents twAdd Q P
    have hdm_ne := twAdd_fp_denom_sub_ne_zero hQ hP
    have hyr := mul_eq_of_eq_mul_inv hdm_ne (twAdd_fp_y Q P)
    have hneg_x : Fp.ofNat (twNeg P).x = -Fp.ofNat P.x := by
      dsimp only [twNeg, edNeg]; simp
    have hneg_y : Fp.ofNat (twNeg P).y = Fp.ofNat P.y := by
      dsimp only [twNeg, edNeg]; simp
    have hdp_raw := twAdd_fp_denom_sub_ne_zero hQ (twOnCurve_twNeg hP)
    have hy1_raw := hQ1_eq ▸ twAdd_fp_y Q (twNeg P)
    rw [hneg_x, hneg_y] at hdp_raw hy1_raw
    have hdp_eq : (1 : Fp) - Fp.ofNat edDInv *
        ((Fp.ofNat Q.x * -Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y)) =
        1 + Fp.ofNat edDInv *
          ((Fp.ofNat Q.x * Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y)) := by
      grind
    have hnum_eq : Fp.ofNat Q.y * Fp.ofNat P.y + Fp.ofNat Q.x * -Fp.ofNat P.x =
        Fp.ofNat Q.y * Fp.ofNat P.y - Fp.ofNat Q.x * Fp.ofNat P.x := by grind
    rw [hdp_eq] at hdp_raw hy1_raw
    rw [hnum_eq] at hy1_raw
    have hy1 := mul_eq_of_eq_mul_inv hdp_raw hy1_raw
    have hy1m1 := twToMontU_denom_ne_zero hQ1 hQ1x
    have hy1p1 := twOnCurve_y_add_one_ne_zero hQ1 hQ1x
    have hu1_fp : Fp.ofNat u1 = (Fp.ofNat Q1.y + 1) * (Fp.ofNat Q1.y - 1)⁻¹ := by
      rw [← hu1]; unfold twToMontU; simp
    have hu1_rel := mul_eq_of_eq_mul_inv hy1m1 hu1_fp
    have hf1_ne := one_add_edDInv_mul_sq_ne_zero (Fp.ofNat P.y)
    have hf2_ne := one_add_edDInv_mul_sq_ne_zero (Fp.ofNat Q.y)
    have hfyy_ne := one_add_edDInv_mul_sq_ne_zero (Fp.ofNat P.y * Fp.ofNat Q.y)
    obtain ⟨hinv_ne, hinv_eq⟩ := inv_ne_zero_of_ne_zero hfyy_ne
    obtain ⟨hdacb_p, hdacb_m⟩ := dacb_kummerTwist _ _ _ _ _ _ _ _ hPU hPW hQU hQW
    have hup := universal_diffadd_plus _ _ _ _ _ (twOnCurve_fp_eq hP) (twOnCurve_fp_eq hQ)
    have hum := universal_diffadd_minus _ _ _ _ _ (twOnCurve_fp_eq hP) (twOnCurve_fp_eq hQ)
    obtain ⟨hU3_eq, hW3_eq⟩ := combine_diffadd_Twist
      (-(121665 : Fp)) (Fp.ofNat edDInv) ((16 : Fp) * (lam2 * lam2) * (lam3 * lam3))
      _ _ _ _ _ _ _ _ _ _ _ _ _
      hcd hinv_eq hyr hy1 hu1_rel hy1m1 hup hum
    have hl16_ne : (16 : Fp) * (lam2 * lam2) * (lam3 * lam3) ≠ 0 :=
      prod3_ne_zero (fp_ne_of_val_ne (by change 16 % p25519 ≠ 0; unfold p25519; decide))
        (sq_ne_zero hlam2) (sq_ne_zero hlam3)
    have hc_ne : (-(121665 : Fp)) ≠ 0 :=
      fp_ne_of_val_ne (by change fpNeg (121665 % p25519) ≠ 0; unfold fpNeg p25519; decide)
    refine ⟨((16 : Fp) * (lam2 * lam2) * (lam3 * lam3)) * (-(121665 : Fp)) *
        (1 + Fp.ofNat edDInv * (Fp.ofNat P.y * Fp.ofNat P.y)) *
        (1 + Fp.ofNat edDInv * (Fp.ofNat Q.y * Fp.ofNat Q.y)) *
        (1 + Fp.ofNat edDInv *
          ((Fp.ofNat P.y * Fp.ofNat Q.y) * (Fp.ofNat P.y * Fp.ofNat Q.y)))⁻¹ *
        (Fp.ofNat Q1.y + 1) *
        (1 - Fp.ofNat edDInv * ((Fp.ofNat Q.x * Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y))) *
        (1 + Fp.ofNat edDInv * ((Fp.ofNat Q.x * Fp.ofNat P.x) * (Fp.ofNat Q.y * Fp.ofNat P.y))),
      prod5_ne_zero (prod4_ne_zero hl16_ne hc_ne hf1_ne hf2_ne) hinv_ne hy1p1 hdm_ne hdp_raw,
      ?_, ?_⟩
    · rw [hfU3, hdacb_p]; exact hU3_eq
    · rw [hfW3, hdacb_m]; exact hW3_eq

private theorem twNeg_x_ne_zero {P : EdPoint} (hP : twOnCurve P = true) (hx : P.x ≠ 0) :
    (twNeg P).x ≠ 0 := by
  intro h0
  dsimp only [twNeg, edNeg] at h0
  have h := congrArg fpNeg h0
  rw [fpNeg_fpNeg, fpNeg_zero, Nat.mod_eq_of_lt (twOnCurve_x_lt hP)] at h
  exact hx h

private theorem twAdd_succ_sub_self (m : Nat) {P1 : EdPoint} (hP1 : twOnCurve P1 = true) :
    twAdd (twNatSmul (m + 1) P1) (twNeg (twNatSmul m P1)) = P1 := by
  have hm := twOnCurve_twNatSmul m hP1
  rw [twNatSmul_succ, twAdd_assoc hP1 hm (twOnCurve_twNeg hm),
      twAdd_twNeg_self hm, twAdd_twZero hP1]

private theorem twAdd_sub_succ_self (m : Nat) {P1 : EdPoint} (hP1 : twOnCurve P1 = true) :
    twAdd (twNatSmul m P1) (twNeg (twNatSmul (m + 1) P1)) = twNeg P1 := by
  have hm := twOnCurve_twNatSmul m hP1
  have hm1 := twOnCurve_twNatSmul (m + 1) hP1
  have hlhs : twAdd (twAdd (twNatSmul m P1) (twNeg (twNatSmul (m + 1) P1)))
      (twNatSmul (m + 1) P1) = twNatSmul m P1 := by
    rw [twAdd_assoc hm (twOnCurve_twNeg hm1) hm1, twNeg_twAdd_self hm1, twAdd_twZero hm]
  have hrhs : twAdd (twNeg P1) (twNatSmul (m + 1) P1) = twNatSmul m P1 := by
    rw [twNatSmul_succ, ← twAdd_assoc (twOnCurve_twNeg hP1) hP1 hm,
        twNeg_twAdd_self hP1, twZero_twAdd hm]
  have heq := congrArg (fun R => twAdd R (twNeg (twNatSmul (m + 1) P1))) (hlhs.trans hrhs.symm)
  rw [twAdd_assoc (twOnCurve_twAdd hm (twOnCurve_twNeg hm1)) hm1 (twOnCurve_twNeg hm1),
      twAdd_twNeg_self hm1,
      twAdd_twZero (twOnCurve_twAdd hm (twOnCurve_twNeg hm1)),
      twAdd_assoc (twOnCurve_twNeg hP1) hm1 (twOnCurve_twNeg hm1),
      twAdd_twNeg_self hm1,
      twAdd_twZero (twOnCurve_twNeg hP1)] at heq
  exact heq

theorem montLadderLoop_kummerTwist_aux (fuel k : Nat) {P1 : EdPoint}
    (hP1 : twOnCurve P1 = true) (hP1x : P1.x ≠ 0) :
    ∀ (m : Nat) (x0 x1 : MontProjPoint),
      kummerTwist (twNatSmul m P1) x0 →
      kummerTwist (twNatSmul (m + 1) P1) x1 →
      kummerTwist (twNatSmul (m * 2 ^ fuel + k % 2 ^ fuel) P1)
        (montLadderLoop fuel k (twToMontU P1) x0 x1) := by
  induction fuel with
  | zero =>
    intro m x0 _ hk0 _
    have hm : m * 2 ^ 0 + k % 2 ^ 0 = m := by
      rw [Nat.pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero]
    rw [montLadderLoop_zero_fuel, hm]
    exact hk0
  | succ f ih =>
    intro m x0 x1 hk0 hk1
    have hm_on := twOnCurve_twNatSmul m hP1
    have hm1_on := twOnCurve_twNatSmul (m + 1) hP1
    dsimp only [montLadderLoop]
    by_cases hb : ((k / 2 ^ f) % 2 == 1) = true
    · simp only [hb, ↓reduceIte]
      have hbit : (k / 2 ^ f) % 2 = 1 := beq_iff_eq.mp hb
      obtain ⟨hq0, hq1⟩ := montDiffAddAndDouble_kummerTwist
        hm1_on hm_on (twAdd_sub_succ_self m hP1)
        (twNeg_x_ne_zero hP1 hP1x) (twToMontU_twNeg P1) hk1 hk0
      have h2m1 : twAdd (twNatSmul m P1) (twNatSmul (m + 1) P1) =
          twNatSmul (2 * m + 1) P1 := by
        rw [← twNatSmul_add m (m + 1) hP1]
        exact congrArg (twNatSmul · P1) (by omega)
      have h2m2 : twAdd (twNatSmul (m + 1) P1) (twNatSmul (m + 1) P1) =
          twNatSmul ((2 * m + 1) + 1) P1 := by
        rw [← twNatSmul_add (m + 1) (m + 1) hP1]
        exact congrArg (twNatSmul · P1) (by omega)
      rw [h2m1] at hq1
      rw [h2m2] at hq0
      have hstep := ih (2 * m + 1) _ _ hq1 hq0
      rwa [ladder_exp_step m 1 k f hbit] at hstep
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hbit : (k / 2 ^ f) % 2 = 0 := by
        have hne : (k / 2 ^ f) % 2 ≠ 1 := fun h => hb (beq_iff_eq.mpr h)
        omega
      obtain ⟨hq0, hq1⟩ := montDiffAddAndDouble_kummerTwist
        hm_on hm1_on (twAdd_succ_sub_self m hP1) hP1x rfl hk0 hk1
      have h2m : twAdd (twNatSmul m P1) (twNatSmul m P1) = twNatSmul (2 * m) P1 := by
        rw [← twNatSmul_add m m hP1]
        exact congrArg (twNatSmul · P1) (by omega)
      have h2m1 : twAdd (twNatSmul (m + 1) P1) (twNatSmul m P1) =
          twNatSmul (2 * m + 1) P1 := by
        rw [← twNatSmul_add (m + 1) m hP1]
        exact congrArg (twNatSmul · P1) (by omega)
      rw [h2m] at hq0
      rw [h2m1] at hq1
      have hstep := ih (2 * m) _ _ hq0 hq1
      have hexp := ladder_exp_step m 0 k f hbit
      rw [Nat.add_zero] at hexp
      rwa [hexp] at hstep

/-- **Montgomery 255-Step Ladder Soundness on $E_{\text{twist}}(\mathbb{F}_p)$**:
    For any $P_1' \in E_{\text{twist}}(\mathbb{F}_p)$ with $P_1'.x \ne 0$ and any $k < 2^{255}$,
    running `montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩` computes $u_{\text{twist}}([k] P_1')$. -/
theorem montLadderLoop_255_twToMontU {k : Nat} {P1 : EdPoint}
    (hk : k < 2 ^ 255) (hP1 : twOnCurve P1 = true) (hP1x : P1.x ≠ 0) :
    let u1 := twToMontU P1
    let res := montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩
    fpMul res.U (fpInv res.W) = twToMontU (twNatSmul k P1) := by
  dsimp only
  have hk0 : kummerTwist (twNatSmul 0 P1) ⟨1, 0⟩ := kummerTwist_twZero
  have hk1 : kummerTwist (twNatSmul (0 + 1) P1) ⟨twToMontU P1, 1⟩ := by
    rw [Nat.zero_add, twNatSmul_one hP1]
    exact kummerTwist_init hP1 hP1x
  have hloop := montLadderLoop_kummerTwist_aux 255 k hP1 hP1x 0 _ _ hk0 hk1
  rw [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hk] at hloop
  exact kummerTwist_toMontU hloop


end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Kummer

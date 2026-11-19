/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec -- proof-setup: allow-public-import

/-!
# Montgomery–Edwards Birational Equivalence & 8-Torsion (`LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational`)

Pure `0-sorry` mathematical proofs connecting Montgomery Curve25519 (`Spec.X25519`) and twisted
Edwards Ed25519 (`Spec.Curve25519`, `Spec.XEdDSA`):
1. Montgomery right-hand side `montRHS`, birational map `edToMontU`, explicit square root
   `montSqrtMinusAPlus2` of $-486664 \bmod p$, rootlessness of $u^2 + 486662 u + 1 \equiv 0 \pmod p$,
   and rational birational identities over `Fp`.
2. Complete characterization of `montToEdwards`, `decodeEdDalek` bridge, and XEdDSA round-trip.
3. Full 2-, 4-, and 8-torsion characterization on $E(\mathbb{F}_p)$ (`lowOrderUs` on-curve half).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational

open VerifiedLibraries.Common (
  p25519 edOrderL modPowLoop modPow fpAdd fpSub fpNeg fpMul fpSq fpPow fpInv sqrtM1 edD EdPoint
  EdExtPoint edZero edExtToAffine edBasepoint edOnCurve edAdd edNeg edSmul leBytesToNat
  natToLeBytes encodeEd recoverXEven decodeEdDalek clampScalarBytes clampScalar)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  decodeU255 montToEdwards lowOrderUs)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field (
  p25519_pos fpAdd_lt fpSub_lt fpNeg_lt fpMul_lt fpSq_lt fpSq_eq_pow2_mod fpAdd_mod_right
  fpSub_mod_right fpSq_mod fpNeg_zero fpMul_one fpNeg_fpMul_fpNeg fpSq_one fpSq_fpNeg fpSq_fpMul
  fpPow_lt IsPrime pocklington1 pocklington2 smallPrime_of_check fpMul_eq_zero_iff
  pow_p25519_sub_one_mod fpSq_eq_fpSq_iff euler_nonsquare fpSq_sqrtM1_eq_fpNeg_one
  fpAdd_one_edD_fpSq_ne_zero fpNeg_mod_two_of_ne_zero recoverXEven_of_curve_eq)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  Fp edOnCurve_x_lt edOnCurve_y_lt edOnCurve_fp_eq edOnCurve_edZero edOnCurve_edBasepoint
  edOnCurve_edNeg edAdd_y_lt edAdd_fp_x edAdd_fp_y edAdd_fp_denom_add_ne_zero
  edAdd_fp_denom_sub_ne_zero edOnCurve_edAdd edAdd_edZero edNeg_edAdd edNatSmul
  edOnCurve_edNatSmul edNatSmul_one edNatSmul_add edNatSmul_two edNatSmul_mul
  edSmul_eq_edNatSmul edOrderL_lt_two_pow_256 edNatSmul_edOrderL_edBasepoint
  edNatSmul_mul_edOrderL_edBasepoint edNatSmul_mod_edOrderL_edBasepoint)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (
  leBytesToNat_nil leBytesToNat_cons leBytesToNat_lt leBytesToNat_natToLeBytes_of_lt
  clampScalar_lt_two_pow_256 recoverXEven_some_props edOnCurve_of_curve_eq
  decodeEdDalek_encodeEd edOrderL_pos)
/-! ## 1. Montgomery Curve Definitions & Certified $\mathbb{F}_p$ Ground Facts -/

/-- Montgomery Curve25519 right-hand side $u^3 + 486662 u^2 + u \bmod p$. -/
@[expose] def montRHS (u : Nat) : Nat :=
  fpAdd (fpAdd (fpMul (fpSq u) u) (fpMul 486662 (fpSq u))) u

/-- Quadratic factor $u^2 + 486662 u + 1 \bmod p$ of `montRHS u = u (u^2 + 486662 u + 1)`. -/
@[expose] def montQuad (u : Nat) : Nat :=
  fpAdd (fpAdd (fpSq u) (fpMul 486662 u)) 1

/-- Birational map $u = (1 + y) \cdot (1 - y)^{-1} \bmod p$ from twisted Edwards to Montgomery
    (maps `edZero = (0, 1)` to `0` since `fpInv 0 = 0`). -/
@[expose] def edToMontU (P : EdPoint) : Nat :=
  fpMul (fpAdd 1 P.y) (fpInv (fpSub 1 P.y))

/-- Canonical even square root $\zeta \in \mathbb{F}_p$ of $-486664 \bmod p$
    ($\zeta^2 \equiv -486664 \pmod{p_{25519}}$). -/
@[expose] def montSqrtMinusAPlus2 : Nat :=
  6853475219497561581579357271197624642482790079785650197046958215289687604742

/-- Square root $s_0 \in \mathbb{F}_p$ of $1 + d \bmod p$ used in the 8-torsion characterization. -/
@[expose] def edSqrtOneAddD : Nat :=
  29211135797516667952872944588131720012451054005016861071534465705161565118763

/-- Positive $y$-coordinate $y_0 \in \mathbb{F}_p$ of order-8 points on $E(\mathbb{F}_p)$. -/
@[expose] def edOrder8Y0 : Nat :=
  2707385501144840649318225287225658788936804267575313519463743609750303402022

/-- Smaller order-8 Montgomery $u$-coordinate on $E(\mathbb{F}_p)[8]$. -/
abbrev montLowOrderU2 : Nat :=
  325606250916557431795983626356110631294008115727848805560023387167927233504

/-- Larger order-8 Montgomery $u$-coordinate on $E(\mathbb{F}_p)[8]$. -/
abbrev montLowOrderU3 : Nat :=
  39382357235489614581723060781553021112529911719440698176882885853963445705823

theorem montSqrtMinusAPlus2_lt : montSqrtMinusAPlus2 < p25519 := by
  unfold montSqrtMinusAPlus2 p25519; decide +kernel
theorem montSqrtMinusAPlus2_ne_zero : montSqrtMinusAPlus2 ≠ 0 := by unfold montSqrtMinusAPlus2; decide +kernel
theorem fpSq_montSqrtMinusAPlus2 : fpSq montSqrtMinusAPlus2 = fpNeg 486664 := by
  unfold fpSq fpMul fpNeg montSqrtMinusAPlus2 p25519; decide +kernel
private theorem fpMul_486664_edD : fpMul 486664 edD = fpNeg 486660 := by
  unfold fpMul fpNeg edD p25519; decide +kernel
theorem fpSq_edSqrtOneAddD : fpSq edSqrtOneAddD = fpAdd 1 edD := by
  unfold fpSq fpMul fpAdd edSqrtOneAddD edD p25519; decide +kernel
theorem edOrder8Y0_lt : edOrder8Y0 < p25519 := by unfold edOrder8Y0 p25519; decide +kernel
theorem edOrder8Y0_sq_eq : fpAdd (fpMul edD (fpSq edOrder8Y0)) 1 = edSqrtOneAddD := by
  unfold fpAdd fpMul fpSq edOrder8Y0 edSqrtOneAddD edD p25519; decide +kernel

section
set_option maxRecDepth 20000
private theorem montQuadDisc_euler : fpPow 59209975560 ((p25519 - 1) / 2) = p25519 - 1 := by
  unfold fpPow modPow p25519; decide +kernel
private theorem fpPow_zero_half : fpPow 0 ((p25519 - 1) / 2) = 0 := by
  unfold fpPow modPow p25519; decide +kernel
theorem edToMontU_edBasepoint : edToMontU edBasepoint = 9 := by
  unfold edToMontU edBasepoint fpMul fpAdd fpSub fpInv fpPow modPow p25519; decide +kernel
@[simp] theorem edToMontU_edZero : edToMontU edZero = 0 := by
  unfold edToMontU edZero fpMul fpAdd fpSub fpInv fpPow modPow p25519; decide +kernel
theorem recoverXEven_p25519_sub_one : recoverXEven (p25519 - 1) = some 0 := by
  unfold recoverXEven fpSq fpSub fpAdd fpMul fpPow modPow fpNeg edD sqrtM1 p25519; decide +kernel
theorem edTorsion8BadY2_euler :
    fpPow (fpMul (fpSub (fpNeg edSqrtOneAddD) 1) (fpInv edD)) ((p25519 - 1) / 2) = p25519 - 1 := by
  unfold fpPow modPow fpMul fpSub fpNeg fpInv edSqrtOneAddD edD p25519; decide +kernel
theorem edOrder8Y0_edToMontU_pos : fpMul (fpAdd 1 edOrder8Y0) (fpInv (fpSub 1 edOrder8Y0)) = montLowOrderU3 := by
  unfold fpMul fpAdd fpSub fpInv fpPow modPow edOrder8Y0 montLowOrderU3 p25519; decide +kernel
theorem edOrder8Y0_edToMontU_neg :
    fpMul (fpAdd 1 (fpNeg edOrder8Y0)) (fpInv (fpSub 1 (fpNeg edOrder8Y0))) = montLowOrderU2 := by
  unfold fpMul fpAdd fpSub fpInv fpPow modPow fpNeg edOrder8Y0 montLowOrderU2 p25519; decide +kernel
private theorem edAdd_order2_self : edAdd { x := 0, y := p25519 - 1 } { x := 0, y := p25519 - 1 } = edZero := by
  unfold edAdd fpAdd fpSub fpMul fpInv fpPow modPow edD edZero p25519; decide +kernel
theorem edToMontU_order2 : edToMontU { x := 0, y := p25519 - 1 } = 0 := by
  unfold edToMontU fpMul fpAdd fpSub fpInv fpPow modPow p25519; decide +kernel
private theorem edToMontU_zero_y_val : fpMul (fpAdd 1 0) (fpInv (fpSub 1 0)) = 1 := by
  unfold fpMul fpAdd fpSub fpInv fpPow modPow p25519; decide +kernel
private theorem edAdd_order4_pos_self :
    edAdd { x := sqrtM1, y := 0 } { x := sqrtM1, y := 0 } = { x := 0, y := p25519 - 1 } := by
  unfold edAdd fpAdd fpSub fpMul fpInv fpPow modPow sqrtM1 edD p25519; decide +kernel
end

private theorem modPowLoop_eq (fuel : Nat) :
    ∀ (base exp m acc : Nat), exp < 2 ^ fuel → modPowLoop fuel base exp m acc = (acc * base ^ exp) % m := by
  induction fuel with
  | zero => intro base exp m acc hexp; (have h0 : exp = 0 := by omega); subst h0; simp [modPowLoop]
  | succ fuel ih =>
    intro base exp m acc hexp; unfold modPowLoop; by_cases h0 : exp = 0
    · subst h0; simp
    · have hne : (exp == 0) = false := Bool.eq_false_iff.mpr (fun heq => h0 (beq_iff_eq.mp heq))
      have hdiv : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hexp; omega
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hsq : ((base * base) % m) ^ (exp / 2) % m = base ^ (2 * (exp / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rcases Nat.mod_two_eq_zero_or_one exp with heven | hodd
      · have hmod : (exp % 2 == 1) = false := by rw [heven]; rfl
        rw [hmod]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod, hsq, show 2 * (exp / 2) = exp by omega, ← Nat.mul_mod]
      · have hmod : (exp % 2 == 1) = true := by rw [hodd]; rfl
        rw [hmod]; simp only [↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod ((acc * base) % m), Nat.mod_mod, hsq, ← Nat.mul_mod,
            Nat.mul_assoc acc, ← Nat.pow_succ', show (2 * (exp / 2)).succ = exp by omega]

private theorem fpPow_eq_pow_mod (a e : Nat) (he : e < 2 ^ 256) : fpPow a e = a ^ e % p25519 := by
  unfold fpPow modPow; rw [modPowLoop_eq 256 (a % p25519) e p25519 1 he, Nat.one_mul, ← Nat.pow_mod a e p25519]

attribute [local irreducible] fpInv fpPow

/-! ## 2. Quadratic Non-Vanishing & Rational Birational Identities over `Fp` -/

theorem montRHS_lt (u : Nat) : montRHS u < p25519 := fpAdd_lt _ _
theorem montQuad_lt (u : Nat) : montQuad u < p25519 := fpAdd_lt _ _
theorem edToMontU_lt (P : EdPoint) : edToMontU P < p25519 := fpMul_lt _ _

@[simp] theorem montRHS_mod (u : Nat) : montRHS (u % p25519) = montRHS u := by
  apply Fp.eq_of_ofNat_eq (montRHS_lt _) (montRHS_lt _); unfold montRHS; simp

@[simp] theorem montQuad_mod (u : Nat) : montQuad (u % p25519) = montQuad u := by
  apply Fp.eq_of_ofNat_eq (montQuad_lt _) (montQuad_lt _); unfold montQuad; simp

@[simp] theorem Fp.ofNat_montRHS (u : Nat) :
    Fp.ofNat (montRHS u) = Fp.ofNat u * Fp.ofNat u * Fp.ofNat u + 486662 * (Fp.ofNat u * Fp.ofNat u) + Fp.ofNat u := by
  unfold montRHS; simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpSq]; rfl

@[simp] theorem Fp.ofNat_montQuad (u : Nat) :
    Fp.ofNat (montQuad u) = Fp.ofNat u * Fp.ofNat u + 486662 * Fp.ofNat u + 1 := by
  unfold montQuad; simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpSq, Fp.ofNat_one]; rfl

theorem Fp.montSqrtMinusAPlus2_sq : Fp.ofNat montSqrtMinusAPlus2 * Fp.ofNat montSqrtMinusAPlus2 = -486664 := by
  have h := congrArg Fp.ofNat fpSq_montSqrtMinusAPlus2; rw [Fp.ofNat_fpSq, Fp.ofNat_fpNeg] at h; exact h

theorem Fp.montSqrtMinusAPlus2_ne_zero : Fp.ofNat montSqrtMinusAPlus2 ≠ 0 := by
  rw [Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt montSqrtMinusAPlus2_lt]
  exact LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational.montSqrtMinusAPlus2_ne_zero

private theorem Fp.edD_mul_486664 : (486664 : Fp) * Fp.ofNat edD = -486660 := by
  have h := congrArg Fp.ofNat fpMul_486664_edD; rw [Fp.ofNat_fpMul, Fp.ofNat_fpNeg] at h; exact h

private theorem Fp.edD_ne_zero : Fp.ofNat edD ≠ 0 := by
  intro h; have hval := congrArg Fp.val h; revert hval; change edD % p25519 = 0 → False
  unfold edD p25519; decide +kernel

private theorem Fp.one_add_edD_ne_zero : (1 : Fp) + Fp.ofNat edD ≠ 0 := by
  intro h; have hval := congrArg Fp.val h; revert hval; change fpAdd 1 edD = 0 → False
  unfold fpAdd edD p25519; decide +kernel

private theorem Fp.four_ne_zero : (4 : Fp) ≠ 0 := by
  intro h; have hval := congrArg Fp.val h; revert hval; change 4 % p25519 = 0 → False; unfold p25519; decide +kernel

private theorem Fp.c486664_ne_zero : (486664 : Fp) ≠ 0 := by
  intro h; have hval := congrArg Fp.val h; revert hval; change 486664 % p25519 = 0 → False; unfold p25519; decide +kernel

/-- Over $\mathbb{F}_{p_{25519}}$, $u^2 + 486662 u + 1$ has no roots: completing the square gives
    $(u + 243331)^2 = 59209975560$, a quadratic non-residue by Euler's criterion. -/
theorem Fp.montQuad_ne_zero (u : Fp) : u * u + 486662 * u + 1 ≠ 0 := by
  intro h; have hcomplete : (u + 243331) * (u + 243331) = (59209975560 : Fp) := by
    have h1 : (243331 : Fp) * 243331 - 1 = 59209975560 := by
      ext; change fpSub (fpMul 243331 243331) 1 = 59209975560 % p25519; unfold fpSub fpMul p25519; decide +kernel
    grind
  have hval := congrArg Fp.val hcomplete; rw [Fp.val_mul] at hval
  exact euler_nonsquare montQuadDisc_euler ⟨(u + 243331).val, hval⟩

theorem montQuad_ne_zero (u : Nat) : montQuad u ≠ 0 := by
  intro h; have hfp : Fp.ofNat (montQuad u) = 0 := by rw [h, Fp.ofNat_zero]
  rw [Fp.ofNat_montQuad] at hfp; exact Fp.montQuad_ne_zero (Fp.ofNat u) hfp

/-- The quadratic $u^2 + 486662 u + 1 \equiv 0 \pmod{p_{25519}}$ has no roots in $\mathbb{F}_p$. -/
theorem montQuad_nat_mod_ne_zero (u : Nat) : (u ^ 2 + 486662 * u + 1) % p25519 ≠ 0 := by
  intro h; have hfp : Fp.ofNat (u ^ 2 + 486662 * u + 1) = 0 := Fp.ext h
  have heq : Fp.ofNat (u ^ 2 + 486662 * u + 1) = Fp.ofNat (montQuad u) := by
    ext; change (u ^ 2 + 486662 * u + 1) % p25519 = montQuad u % p25519
    rw [Nat.mod_eq_of_lt (montQuad_lt u)]; unfold montQuad fpAdd fpSq fpMul; simp [Nat.pow_two, Nat.add_mod, Nat.mul_mod]
  rw [heq, Fp.ofNat_montQuad] at hfp; exact Fp.montQuad_ne_zero (Fp.ofNat u) hfp

theorem montRHS_eq_mul_montQuad (u : Nat) : montRHS u = fpMul u (montQuad u) := by
  apply Fp.eq_of_ofNat_eq (montRHS_lt u) (fpMul_lt _ _)
  rw [Fp.ofNat_montRHS, Fp.ofNat_fpMul, Fp.ofNat_montQuad]; grind

/-- Because $u^2 + 486662 u + 1 \not\equiv 0 \pmod p$, `montRHS u = 0` iff `u % p25519 = 0`. -/
theorem montRHS_eq_zero_iff (u : Nat) : montRHS u = 0 ↔ u % p25519 = 0 := by
  rw [montRHS_eq_mul_montQuad, fpMul_eq_zero_iff]; constructor
  · rintro (hu | hq); · exact hu
    · rw [Nat.mod_eq_of_lt (montQuad_lt u)] at hq; exact absurd hq (montQuad_ne_zero u)
  · intro hu; left; exact hu

/-- Constructive Euler's Criterion in $\mathbb{F}_{p_{25519}}$: for $a \not\equiv 0 \pmod p$,
    $a$ is a non-square iff $a^{(p - 1)/2} \equiv p - 1 \pmod p$. -/
theorem euler_nonsquare_iff {a : Nat} (ha : a % p25519 ≠ 0) :
    (¬ ∃ r : Nat, fpSq r = a % p25519) ↔ fpPow a ((p25519 - 1) / 2) = p25519 - 1 := by
  refine ⟨?_, euler_nonsquare⟩; intro hnsq; let s := fpPow a ((p25519 - 1) / 2)
  have he1_lt : (p25519 - 1) / 2 < 2 ^ 256 := by unfold p25519; decide +kernel
  have he2_lt : (p25519 + 3) / 8 < 2 ^ 256 := by unfold p25519; decide +kernel
  have hexp_pm1 : (p25519 - 1) / 2 * 2 = p25519 - 1 := by unfold p25519; decide +kernel
  have hexp_p3 : (p25519 + 3) / 8 * (2 * 2) = 2 + (p25519 - 1) / 2 := by unfold p25519; decide +kernel
  have hs_lt : s < p25519 := fpPow_lt a ((p25519 - 1) / 2)
  have hs_pow : s = a ^ ((p25519 - 1) / 2) % p25519 := fpPow_eq_pow_mod a _ he1_lt
  have hs_sq : fpSq s = fpSq 1 := by
    rw [hs_pow, fpSq_mod, fpSq_eq_pow2_mod, ← Nat.pow_mul, hexp_pm1, pow_p25519_sub_one_mod ha, fpSq_one]
  rcases (fpSq_eq_fpSq_iff s 1).mp hs_sq with hs1 | hs_neg1
  · exfalso; rw [Nat.mod_eq_of_lt hs_lt, show 1 % p25519 = 1 from by unfold p25519; decide +kernel] at hs1
    let r := fpPow a ((p25519 + 3) / 8)
    have hr_pow : r = a ^ ((p25519 + 3) / 8) % p25519 := fpPow_eq_pow_mod a _ he2_lt
    have hr4 : fpSq (fpSq r) = fpSq a := by
      rw [hr_pow, fpSq_mod, fpSq_eq_pow2_mod, fpSq_eq_pow2_mod, ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.pow_mul,
          hexp_p3, Nat.pow_add, Nat.mul_mod, ← hs_pow, hs1, Nat.mul_one, Nat.mod_mod, fpSq_eq_pow2_mod]
    rcases (fpSq_eq_fpSq_iff (fpSq r) a).mp hr4 with hr_pos | hr_neg
    · rw [Nat.mod_eq_of_lt (fpSq_lt r)] at hr_pos; exact hnsq ⟨r, hr_pos⟩
    · rw [Nat.mod_eq_of_lt (fpSq_lt r)] at hr_neg; refine hnsq ⟨fpMul r sqrtM1, ?_⟩
      rw [fpSq_fpMul, hr_neg, fpSq_sqrtM1_eq_fpNeg_one, fpNeg_fpMul_fpNeg, fpMul_one]
  · rw [Nat.mod_eq_of_lt hs_lt] at hs_neg1; exact hs_neg1.trans (by unfold fpNeg p25519; decide +kernel)

theorem edToMontU_edNeg (P : EdPoint) : edToMontU (edNeg P) = edToMontU P := by
  unfold edToMontU edNeg; rw [fpAdd_mod_right, fpSub_mod_right]

theorem edToMontU_edExtToAffine {Q : EdExtPoint} (hZ : Q.Z % p25519 ≠ 0) :
    edToMontU (edExtToAffine Q) = fpMul (fpAdd Q.Z Q.Y) (fpInv (fpSub Q.Z Q.Y)) := by
  apply Fp.eq_of_ofNat_eq (edToMontU_lt _) (fpMul_lt _ _); unfold edToMontU edExtToAffine
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpInv, Fp.ofNat_one]
  have hz : Fp.ofNat Q.Z ≠ 0 := (Fp.ofNat_ne_zero_iff Q.Z).mpr hZ
  by_cases hzy : Fp.ofNat Q.Z - Fp.ofNat Q.Y = 0
  · (have h1 : (1 : Fp) - Fp.ofNat Q.Y * (Fp.ofNat Q.Z)⁻¹ = 0 := by grind); rw [hzy, h1, Lean.Grind.Field.inv_zero]; grind
  · grind

theorem edToMontU_ne_p25519_sub_one (P : EdPoint) : edToMontU P ≠ p25519 - 1 := by
  intro h; have hfp := congrArg Fp.ofNat h
  have hneg1 : Fp.ofNat (p25519 - 1) = -1 := by ext; change (p25519 - 1) % p25519 = fpNeg 1; unfold fpNeg p25519; decide +kernel
  unfold edToMontU at hfp; rw [hneg1, Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpInv, Fp.ofNat_fpSub, Fp.ofNat_one] at hfp
  have h2 := Fp.two_ne_zero
  by_cases hy : (1 : Fp) - Fp.ofNat P.y = 0
  · rw [hy, Lean.Grind.Field.inv_zero] at hfp; grind
  · grind

theorem edOnCurve_eq_edZero_iff_y_eq_one {P : EdPoint} (hP : edOnCurve P = true) : P = edZero ↔ P.y = 1 := by
  refine ⟨fun h => by subst h; rfl, fun hy => ?_⟩
  have hfp := edOnCurve_fp_eq hP; have h1d := Fp.one_add_edD_ne_zero; rw [hy, Fp.ofNat_one] at hfp
  exact LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards.EdPoint.ext (Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos
    (by rw [show edZero.x = 0 from rfl, Fp.ofNat_zero]; grind)) hy

theorem fpAdd_one_ne_zero_of_ne_sub_one {u : Nat} (hu_lt : u < p25519) (hu_ne : u ≠ p25519 - 1) :
    fpAdd u 1 ≠ 0 := by unfold fpAdd p25519 at *; omega

/-- For $u < p$ with $u \ne p - 1$, $y = (u - 1)/(u + 1) \bmod p$ satisfies $y \ne 1$. -/
theorem birational_y_ne_one {u : Nat} (hu_lt : u < p25519) (hu_ne : u ≠ p25519 - 1) :
    fpMul (fpSub u 1) (fpInv (fpAdd u 1)) ≠ 1 := by
  intro hy1; have hfp := congrArg Fp.ofNat hy1; have h2 := Fp.two_ne_zero
  have hu1_fp : Fp.ofNat u + 1 ≠ 0 := by
    rw [← Fp.ofNat_one, ← Fp.ofNat_fpAdd, Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt (fpAdd_lt _ _)]
    exact fpAdd_one_ne_zero_of_ne_sub_one hu_lt hu_ne
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpSub, Fp.ofNat_fpInv, Fp.ofNat_fpAdd, Fp.ofNat_one] at hfp; grind

/-- For $u < p$ with $u \ne p - 1$ and $y = (u - 1)/(u + 1) \bmod p$, $(1 + y)/(1 - y) \bmod p = u$. -/
theorem birational_u_of_y {u : Nat} (hu_lt : u < p25519) (hu_ne : u ≠ p25519 - 1) :
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    fpMul (fpAdd 1 y) (fpInv (fpSub 1 y)) = u := by
  dsimp only []; apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) hu_lt; have h2 := Fp.two_ne_zero
  have hu1_fp : Fp.ofNat u + 1 ≠ 0 := by
    rw [← Fp.ofNat_one, ← Fp.ofNat_fpAdd, Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt (fpAdd_lt _ _)]
    exact fpAdd_one_ne_zero_of_ne_sub_one hu_lt hu_ne
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpInv, Fp.ofNat_one]; grind

/-- Inverse Möbius map: for $y < p$ with $y \ne 1$ and $u = (1 + y)/(1 - y) \bmod p$, $(u - 1)/(u + 1) \bmod p = y$. -/
theorem birational_y_of_u {y : Nat} (hy_lt : y < p25519) (hy_ne : y ≠ 1) :
    let u := fpMul (fpAdd 1 y) (fpInv (fpSub 1 y))
    fpMul (fpSub u 1) (fpInv (fpAdd u 1)) = y := by
  dsimp only []; apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) hy_lt; have h2 := Fp.two_ne_zero
  have hy1_fp : (1 : Fp) - Fp.ofNat y ≠ 0 := fun h =>
    hy_ne (Fp.eq_of_ofNat_eq hy_lt (by unfold p25519; decide +kernel) (by rw [Fp.ofNat_one]; grind))
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpInv, Fp.ofNat_one]; grind

/-- For $u < p$ with $u \ne p - 1$ and $y = (u - 1)/(u + 1) \bmod p$,
    $1 + d y^2 \equiv \frac{4(u^2 + 486662 u + 1)}{486664 (u + 1)^2} \pmod p$. -/
theorem birational_one_add_edD_sq {u : Nat} (hu_lt : u < p25519) (hu_ne : u ≠ p25519 - 1) :
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    fpAdd 1 (fpMul edD (fpSq y)) = fpMul (fpMul 4 (montQuad u)) (fpInv (fpMul 486664 (fpSq (fpAdd u 1)))) := by
  dsimp only []; apply Fp.eq_of_ofNat_eq (fpAdd_lt _ _) (fpMul_lt _ _)
  have hu1_fp : Fp.ofNat u + 1 ≠ 0 := by
    rw [← Fp.ofNat_one, ← Fp.ofNat_fpAdd, Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt (fpAdd_lt _ _)]
    exact fpAdd_one_ne_zero_of_ne_sub_one hu_lt hu_ne
  have hc := Fp.c486664_ne_zero; have hd := Fp.edD_mul_486664
  have hden : (486664 : Fp) * ((Fp.ofNat u + 1) * (Fp.ofNat u + 1)) ≠ 0 := Fp.mul_ne_zero hc (Fp.mul_ne_zero hu1_fp hu1_fp)
  simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpSub, Fp.ofNat_fpSq, Fp.ofNat_fpInv, Fp.ofNat_montQuad, Fp.ofNat_one]
  change (1 : Fp) + Fp.ofNat edD * (((Fp.ofNat u - 1) * (Fp.ofNat u + 1)⁻¹) * ((Fp.ofNat u - 1) * (Fp.ofNat u + 1)⁻¹)) =
    ((4 : Fp) * (Fp.ofNat u * Fp.ofNat u + 486662 * Fp.ofNat u + 1)) * ((486664 : Fp) * ((Fp.ofNat u + 1) * (Fp.ofNat u + 1)))⁻¹
  grind

/-- Fundamental rational birational identity over $\mathbb{F}_p$:
    $(y^2 - 1) \cdot (1 + d y^2)^{-1} \equiv (-486664) \cdot u^2 \cdot (u^3 + 486662 u^2 + u)^{-1} \pmod p$. -/
theorem birational_ed_lhs_eq_mont_rhs {u : Nat} (hu_lt : u < p25519) (hu_ne : u ≠ p25519 - 1) :
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    fpMul (fpSub (fpSq y) 1) (fpInv (fpAdd 1 (fpMul edD (fpSq y)))) =
      fpMul (fpNeg 486664) (fpMul (fpSq u) (fpInv (montRHS u))) := by
  dsimp only []
  have hden_eq := congrArg Fp.ofNat (birational_one_add_edD_sq hu_lt hu_ne)
  have hrhs_eq := congrArg Fp.ofNat (montRHS_eq_mul_montQuad u)
  generalize hy : fpMul (fpSub u 1) (fpInv (fpAdd u 1)) = y at hden_eq ⊢
  apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) (fpMul_lt _ _)
  have hu1_fp : Fp.ofNat u + 1 ≠ 0 := by
    rw [← Fp.ofNat_one, ← Fp.ofNat_fpAdd, Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt (fpAdd_lt _ _)]
    exact fpAdd_one_ne_zero_of_ne_sub_one hu_lt hu_ne
  have hq_fp : Fp.ofNat (montQuad u) ≠ 0 := by rw [Fp.ofNat_montQuad]; exact Fp.montQuad_ne_zero (Fp.ofNat u)
  have h4 := Fp.four_ne_zero; have hc := Fp.c486664_ne_zero
  have hy_fp : Fp.ofNat y = (Fp.ofNat u - 1) * (Fp.ofNat u + 1)⁻¹ := by
    rw [← hy]; simp [Fp.ofNat_fpMul, Fp.ofNat_fpSub, Fp.ofNat_fpInv, Fp.ofNat_fpAdd]
  have hsq1 : (Fp.ofNat u + 1) * (Fp.ofNat u + 1) ≠ 0 := Fp.mul_ne_zero hu1_fp hu1_fp
  have hnum_eq : Fp.ofNat y * Fp.ofNat y - 1 = (-(4 : Fp) * Fp.ofNat u) * ((Fp.ofNat u + 1) * (Fp.ofNat u + 1))⁻¹ := by
    rw [hy_fp]; grind
  simp only [Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpSq, Fp.ofNat_fpInv, Fp.ofNat_one] at hden_eq
  rw [Fp.ofNat_fpMul] at hrhs_eq
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpSq, Fp.ofNat_fpInv, Fp.ofNat_fpNeg, Fp.ofNat_one]
  rw [hnum_eq, hden_eq, hrhs_eq]
  change (-(4 : Fp) * Fp.ofNat u * ((Fp.ofNat u + 1) * (Fp.ofNat u + 1))⁻¹) *
      (((4 : Fp) * Fp.ofNat (montQuad u)) * ((486664 : Fp) * ((Fp.ofNat u + 1) * (Fp.ofNat u + 1)))⁻¹)⁻¹ =
    -(486664 : Fp) * ((Fp.ofNat u * Fp.ofNat u) * (Fp.ofNat u * Fp.ofNat (montQuad u))⁻¹)
  have hden_c := Fp.mul_ne_zero hc hsq1; have hnum_c := Fp.mul_ne_zero h4 hq_fp
  have hfrac_ne : ((4 : Fp) * Fp.ofNat (montQuad u)) * ((486664 : Fp) * ((Fp.ofNat u + 1) * (Fp.ofNat u + 1)))⁻¹ ≠ 0 :=
    fun h0 => hnum_c (by grind)
  by_cases hu0 : Fp.ofNat u = 0
  · rw [hu0]; grind
  · have hmul_ne := Fp.mul_ne_zero hu0 hq_fp; grind

/-- For $0 < u < p$ with $u \ne p - 1$ and $y = (u - 1)/(u + 1) \bmod p$, $(d y^2 + 1) x^2 = y^2 - 1$
    is solvable in $\mathbb{F}_p$ iff `montRHS u` is a square in $\mathbb{F}_p$. -/
theorem birational_curve_eq_iff_montRHS_sq {u : Nat} (hu_pos : 0 < u) (hu_lt : u < p25519) (hu_ne : u ≠ p25519 - 1) :
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    (∃ x : Nat, fpMul (fpAdd (fpMul edD (fpSq y)) 1) (fpSq x) = fpSub (fpSq y) 1) ↔
      (∃ v : Nat, fpSq v = montRHS u) := by
  dsimp only []; have hrat := congrArg Fp.ofNat (birational_ed_lhs_eq_mont_rhs hu_lt hu_ne)
  generalize fpMul (fpSub u 1) (fpInv (fpAdd u 1)) = y at hrat ⊢
  simp only [Fp.ofNat_fpMul, Fp.ofNat_fpSub, Fp.ofNat_fpAdd, Fp.ofNat_fpSq, Fp.ofNat_fpInv, Fp.ofNat_fpNeg, Fp.ofNat_one] at hrat
  change ((Fp.ofNat y * Fp.ofNat y - 1) * (1 + Fp.ofNat edD * (Fp.ofNat y * Fp.ofNat y))⁻¹) =
    (-(486664 : Fp)) * ((Fp.ofNat u * Fp.ofNat u) * (Fp.ofNat (montRHS u))⁻¹) at hrat
  rw [← Fp.montSqrtMinusAPlus2_sq] at hrat
  have hu_fp : Fp.ofNat u ≠ 0 := by rw [Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt hu_lt]; omega
  have hm_fp : Fp.ofNat (montRHS u) ≠ 0 := by
    rw [Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt (montRHS_lt u), ne_eq, montRHS_eq_zero_iff, Nat.mod_eq_of_lt hu_lt]; omega
  have hvden_fp : (1 : Fp) + Fp.ofNat edD * (Fp.ofNat y * Fp.ofNat y) ≠ 0 := by
    rw [← Fp.ofNat_fpSq, ← Fp.ofNat_fpMul, ← Fp.ofNat_one, ← Fp.ofNat_fpAdd, Fp.ofNat_ne_zero_iff, Nat.mod_eq_of_lt (fpAdd_lt _ _)]
    exact fpAdd_one_edD_fpSq_ne_zero y
  have hz_fp := Fp.montSqrtMinusAPlus2_ne_zero; constructor
  · rintro ⟨x, hx⟩; have hxfp := congrArg Fp.ofNat hx
    simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpSq, Fp.ofNat_one] at hxfp
    have hx_ne : Fp.ofNat x ≠ 0 := fun hx0 => by rw [hx0] at hxfp; grind
    let V : Fp := (Fp.ofNat montSqrtMinusAPlus2 * Fp.ofNat u) * (Fp.ofNat x)⁻¹
    have hVsq : V * V = Fp.ofNat (montRHS u) := by dsimp only [V]; grind
    exact ⟨V.val, Fp.eq_of_ofNat_eq (fpSq_lt _) (montRHS_lt u) (by simpa [Fp.ofNat_fpSq] using hVsq)⟩
  · rintro ⟨v, hv⟩; have hvfp := congrArg Fp.ofNat hv; rw [Fp.ofNat_fpSq] at hvfp
    have hv_ne : Fp.ofNat v ≠ 0 := fun hv0 => by rw [hv0] at hvfp; grind
    let X : Fp := (Fp.ofNat montSqrtMinusAPlus2 * Fp.ofNat u) * (Fp.ofNat v)⁻¹
    have hXsq : (Fp.ofNat edD * (Fp.ofNat y * Fp.ofNat y) + 1) * (X * X) = Fp.ofNat y * Fp.ofNat y - 1 := by
      dsimp only [X]; grind
    refine ⟨X.val, Fp.eq_of_ofNat_eq (fpMul_lt _ _) (fpSub_lt _ _) ?_⟩
    simpa [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpSub, Fp.ofNat_fpSq] using hXsq

/-! ## 3. Complete Characterization of `montToEdwards`, XEdDSA Bridge, & `decodeEdDalek` -/

theorem recoverXEven_eq_none_iff (y : Nat) :
    recoverXEven y = none ↔ ¬ ∃ x : Nat, fpMul (fpAdd (fpMul edD (fpSq y)) 1) (fpSq x) = fpSub (fpSq y) 1 := by
  constructor
  · intro hnone ⟨x, hx⟩; rw [recoverXEven_of_curve_eq hx] at hnone; cases hnone
  · intro hno; cases h : recoverXEven y with
    | none => rfl
    | some xEven => exact absurd ⟨xEven, (recoverXEven_some_props h).2.2⟩ hno

attribute [local irreducible] recoverXEven

private def montLiftWith (recFn : Nat → Option Nat) (u p1 sign : Nat) : Option EdPoint :=
  if u == p1 then none
  else
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    montToEdwards.match_1 (fun _ => Option EdPoint) (recFn y) (fun _ => none)
      (fun xEven => let x := if sign % 2 == 1 then fpNeg xEven else xEven; some ⟨x, y⟩)

private theorem montToEdwards_eq_liftWith (bs : List (BitVec 8)) (sign : Nat) :
    montToEdwards bs sign = montLiftWith recoverXEven (decodeU255 bs % p25519) (p25519 - 1) sign := rfl

private theorem montLiftWith_eq_some_iff (recFn : Nat → Option Nat) (u p1 sign : Nat) (P : EdPoint) :
    montLiftWith recFn u p1 sign = some P ↔ u ≠ p1 ∧ ∃ xEven,
      recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) = some xEven ∧
      P = ⟨if sign % 2 == 1 then fpNeg xEven else xEven, fpMul (fpSub u 1) (fpInv (fpAdd u 1))⟩ := by
  unfold montLiftWith; by_cases hup : u = p1
  · subst hup; simp
  · have hb : (u == p1) = false := Bool.eq_false_iff.mpr (fun heq => hup (beq_iff_eq.mp heq))
    rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, hup, not_false_eq_true, true_and]
    cases hrec : recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) with
    | none => dsimp only [montToEdwards.match_1]; simp
    | some xEven =>
      dsimp only [montToEdwards.match_1]; constructor
      · intro h; injection h with hP; exact ⟨xEven, rfl, hP.symm⟩
      · rintro ⟨x', hx', rfl⟩; injection hx' with hx'; subst hx'; rfl

private theorem montLiftWith_eq_none_iff (recFn : Nat → Option Nat) (u p1 sign : Nat) :
    montLiftWith recFn u p1 sign = none ↔
      u = p1 ∨ (u ≠ p1 ∧ recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) = none) := by
  unfold montLiftWith; by_cases hup : u = p1
  · subst hup; simp
  · have hb : (u == p1) = false := Bool.eq_false_iff.mpr (fun heq => hup (beq_iff_eq.mp heq))
    rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte, hup, ne_eq, not_false_eq_true, true_and, false_or]
    cases hrec : recFn (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) <;> dsimp only [montToEdwards.match_1] <;> simp

theorem montToEdwards_eq_some_iff (bs : List (BitVec 8)) (sign : Nat) (P : EdPoint) :
    montToEdwards bs sign = some P ↔
      let u := decodeU255 bs % p25519; let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
      u ≠ p25519 - 1 ∧ ∃ xEven, recoverXEven y = some xEven ∧
        P = ⟨if sign % 2 == 1 then fpNeg xEven else xEven, y⟩ := by
  rw [montToEdwards_eq_liftWith]; exact montLiftWith_eq_some_iff recoverXEven (decodeU255 bs % p25519) (p25519 - 1) sign P

theorem montToEdwards_eq_none_iff_raw (bs : List (BitVec 8)) (sign : Nat) :
    montToEdwards bs sign = none ↔
      let u := decodeU255 bs % p25519
      u = p25519 - 1 ∨ (u ≠ p25519 - 1 ∧ recoverXEven (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) = none) := by
  rw [montToEdwards_eq_liftWith]; exact montLiftWith_eq_none_iff recoverXEven (decodeU255 bs % p25519) (p25519 - 1) sign

attribute [local irreducible] montToEdwards

theorem montToEdwards_some_onCurve {bs : List (BitVec 8)} {sign : Nat} {P : EdPoint}
    (h : montToEdwards bs sign = some P) : edOnCurve P = true := by
  rcases (montToEdwards_eq_some_iff bs sign P).mp h with ⟨_, xEven, hrec, rfl⟩
  generalize hy : fpMul (fpSub (decodeU255 bs % p25519) 1) (fpInv (fpAdd (decodeU255 bs % p25519) 1)) = y at hrec ⊢
  have hy_lt : y < p25519 := by rw [← hy]; exact fpMul_lt _ _
  rcases recoverXEven_some_props hrec with ⟨hx_lt, _, hcurve⟩
  cases (sign % 2 == 1)
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact edOnCurve_of_curve_eq hx_lt hy_lt hcurve
  · simp only [↓reduceIte]; exact edOnCurve_of_curve_eq (fpNeg_lt xEven) hy_lt (by rw [fpSq_fpNeg]; exact hcurve)

theorem montToEdwards_some_y_ne_one {bs : List (BitVec 8)} {sign : Nat} {P : EdPoint}
    (h : montToEdwards bs sign = some P) : P.y ≠ 1 := by
  rcases (montToEdwards_eq_some_iff bs sign P).mp h with ⟨hne, _, _, rfl⟩
  exact birational_y_ne_one (Nat.mod_lt _ p25519_pos) hne

theorem montToEdwards_some_ne_edZero {bs : List (BitVec 8)} {sign : Nat} {P : EdPoint}
    (h : montToEdwards bs sign = some P) : P ≠ edZero :=
  fun h0 => montToEdwards_some_y_ne_one h (by rw [h0]; rfl)

theorem montToEdwards_some_edToMontU {bs : List (BitVec 8)} {sign : Nat} {P : EdPoint}
    (h : montToEdwards bs sign = some P) : edToMontU P = decodeU255 bs % p25519 := by
  rcases (montToEdwards_eq_some_iff bs sign P).mp h with ⟨hne, _, _, rfl⟩
  exact birational_u_of_y (Nat.mod_lt _ p25519_pos) hne

theorem montToEdwards_some_x_eq_zero_iff {bs : List (BitVec 8)} {sign : Nat} {P : EdPoint}
    (h : montToEdwards bs sign = some P) : P.x = 0 ↔ decodeU255 bs % p25519 = 0 := by
  have hP := montToEdwards_some_onCurve h; have hy1 := montToEdwards_some_y_ne_one h
  rw [← montToEdwards_some_edToMontU h]; constructor
  · intro hx0; have hfp := edOnCurve_fp_eq hP; rw [hx0, Fp.ofNat_zero] at hfp
    have hy_pm : Fp.ofNat P.y = 1 ∨ Fp.ofNat P.y = -1 := by
      have : (Fp.ofNat P.y - 1) * (Fp.ofNat P.y + 1) = 0 := by grind
      by_cases h1 : Fp.ofNat P.y - 1 = 0
      · left; grind
      · right; grind
    rcases hy_pm with h1 | hm1
    · exact absurd (Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) (by unfold p25519; decide +kernel) h1) hy1
    · apply Fp.eq_of_ofNat_eq (edToMontU_lt P) p25519_pos; unfold edToMontU
      simp only [Fp.ofNat_fpMul, Fp.ofNat_fpAdd, Fp.ofNat_fpInv, Fp.ofNat_fpSub, Fp.ofNat_one, Fp.ofNat_zero, hm1]
      grind
  · intro hu0
    have hy_eq : P.y = fpMul (fpSub 0 1) (fpInv (fpAdd 0 1)) := by
      have := birational_y_of_u (edOnCurve_y_lt hP) hy1; dsimp only [] at this
      change fpMul (fpSub (edToMontU P) 1) (fpInv (fpAdd (edToMontU P) 1)) = P.y at this
      rw [hu0] at this; exact this.symm
    have hy_fp : Fp.ofNat P.y = -1 := by
      rw [hy_eq]; simp only [Fp.ofNat_fpMul, Fp.ofNat_fpSub, Fp.ofNat_fpInv, Fp.ofNat_fpAdd, Fp.ofNat_zero, Fp.ofNat_one]
      grind
    have hfp := edOnCurve_fp_eq hP; have h1d := Fp.one_add_edD_ne_zero; rw [hy_fp] at hfp
    exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos (by rw [Fp.ofNat_zero]; grind)

theorem montToEdwards_some_sign_of_x_ne_zero {bs : List (BitVec 8)} {sign : Nat} {P : EdPoint}
    (h : montToEdwards bs sign = some P) (hx : P.x ≠ 0) : P.x % 2 = sign % 2 := by
  rcases (montToEdwards_eq_some_iff bs sign P).mp h with ⟨_, xEven, hrec, hP⟩
  rcases recoverXEven_some_props hrec with ⟨hx_lt, hxe2, _⟩
  have hxe_ne0 : xEven ≠ 0 := by rintro rfl; rw [hP] at hx; cases sign % 2 == 1 <;> simp [fpNeg_zero] at hx
  have hxe_mod_ne : xEven % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hx_lt]; exact hxe_ne0
  rw [hP]; rcases Nat.mod_two_eq_zero_or_one sign with hs0 | hs1
  · have hb : (sign % 2 == 1) = false := by rw [hs0]; rfl
    rw [hb, hs0]; exact hxe2
  · have hb : (sign % 2 == 1) = true := by rw [hs1]; rfl
    rw [hb, hs1]; simp only [↓reduceIte]; rw [fpNeg_mod_two_of_ne_zero hxe_mod_ne, Nat.mod_eq_of_lt hx_lt, hxe2]

theorem montToEdwards_some_sign_of_u_ne_zero {bs : List (BitVec 8)} {sign : Nat} {P : EdPoint}
    (h : montToEdwards bs sign = some P) (hu : decodeU255 bs % p25519 ≠ 0) : P.x % 2 = sign % 2 :=
  montToEdwards_some_sign_of_x_ne_zero h (fun hx0 => hu ((montToEdwards_some_x_eq_zero_iff h).mp hx0))

theorem montToEdwards_some_sign {bs : List (BitVec 8)} {sign : Nat} {P : EdPoint}
    (h : montToEdwards bs sign = some P) (h0 : P.x = 0 → sign % 2 = 0) : P.x % 2 = sign % 2 := by
  by_cases hx : P.x = 0
  · rw [hx, h0 hx]
  · exact montToEdwards_some_sign_of_x_ne_zero h hx

theorem montToEdwards_some_sign_zero {bs : List (BitVec 8)} {P : EdPoint}
    (h : montToEdwards bs 0 = some P) : P.x % 2 = 0 := montToEdwards_some_sign h (fun _ => rfl)

/-- Complete characterization of `montToEdwards bs sign = none`: either $u = p - 1$, or
    $0 < u < p - 1$ and `montRHS u` is a quadratic non-residue in $\mathbb{F}_p$. -/
theorem montToEdwards_none_iff (bs : List (BitVec 8)) (sign : Nat) :
    let u := decodeU255 bs % p25519
    montToEdwards bs sign = none ↔
      u = p25519 - 1 ∨ (u ≠ 0 ∧ u ≠ p25519 - 1 ∧ fpPow (montRHS u) ((p25519 - 1) / 2) = p25519 - 1) := by
  dsimp only []; rw [montToEdwards_eq_none_iff_raw]; dsimp only []
  have hu_lt : decodeU255 bs % p25519 < p25519 := Nat.mod_lt _ p25519_pos
  generalize decodeU255 bs % p25519 = u at hu_lt ⊢
  by_cases hup : u = p25519 - 1
  · simp [hup]
  · simp only [hup, false_or, ne_eq, not_false_eq_true, true_and]; by_cases hu0 : u = 0
    · subst hu0
      have hy_pm1 : fpMul (fpSub 0 1) (fpInv (fpAdd 0 1)) = p25519 - 1 := by
        apply Fp.eq_of_ofNat_eq (fpMul_lt _ _) (by unfold p25519; decide +kernel)
        have hneg1 : Fp.ofNat (p25519 - 1) = -1 := by
          ext; change (p25519 - 1) % p25519 = fpNeg 1; unfold fpNeg p25519; decide +kernel
        rw [hneg1]; simp only [Fp.ofNat_fpMul, Fp.ofNat_fpSub, Fp.ofNat_fpInv, Fp.ofNat_fpAdd, Fp.ofNat_zero, Fp.ofNat_one]
        grind
      rw [hy_pm1, recoverXEven_p25519_sub_one]; simp
    · simp only [hu0, not_false_eq_true, true_and]
      have hm_ne : montRHS u % p25519 ≠ 0 := by
        rw [Nat.mod_eq_of_lt (montRHS_lt u), ne_eq, montRHS_eq_zero_iff, Nat.mod_eq_of_lt hu_lt]; exact hu0
      have hbir : (∃ x, fpMul (fpAdd (fpMul edD (fpSq (fpMul (fpSub u 1) (fpInv (fpAdd u 1))))) 1) (fpSq x) =
            fpSub (fpSq (fpMul (fpSub u 1) (fpInv (fpAdd u 1)))) 1) ↔ ∃ v, fpSq v = montRHS u :=
        birational_curve_eq_iff_montRHS_sq (Nat.pos_of_ne_zero hu0) hu_lt hup
      rw [recoverXEven_eq_none_iff, hbir, ← euler_nonsquare_iff hm_ne, Nat.mod_eq_of_lt (montRHS_lt u)]

theorem montToEdwards_none_iff_short (bs : List (BitVec 8)) (sign : Nat) :
    let u := decodeU255 bs % p25519
    montToEdwards bs sign = none ↔ u = p25519 - 1 ∨ fpPow (montRHS u) ((p25519 - 1) / 2) = p25519 - 1 := by
  dsimp only []
  have hnone : montToEdwards bs sign = none ↔ decodeU255 bs % p25519 = p25519 - 1 ∨
      (decodeU255 bs % p25519 ≠ 0 ∧ decodeU255 bs % p25519 ≠ p25519 - 1 ∧
        fpPow (montRHS (decodeU255 bs % p25519)) ((p25519 - 1) / 2) = p25519 - 1) := montToEdwards_none_iff bs sign
  rw [hnone]; generalize decodeU255 bs % p25519 = u; constructor
  · rintro (h | ⟨_, _, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hup : u = p25519 - 1
      · exact Or.inl hup
      · refine Or.inr ⟨?_, hup, h⟩; rintro rfl
        have hm0 : montRHS 0 = 0 := (montRHS_eq_zero_iff 0).mpr (Nat.zero_mod _)
        rw [hm0, fpPow_zero_half] at h; revert h; unfold p25519; decide +kernel

/-! ## 4. Bridge to `decodeEdDalek` (`MontgomeryPoint::to_edwards`) -/

/-- Set bit 255 (bit 7 of byte 31) of a 32-byte little-endian buffer to bit 0 of `sign`. -/
@[expose] def setSignBit (bs : List (BitVec 8)) (sign : BitVec 8) : List (BitVec 8) :=
  bs.take 31 ++ [((bs.getD 31 0#8) &&& 0x7f#8) ||| ((sign &&& 1#8) <<< 7)]

/-- Clear bit 255 (bit 7 of byte 31) of a 32-byte little-endian buffer. -/
@[expose] def clearSignBit (bs : List (BitVec 8)) : List (BitVec 8) := bs.take 31 ++ [(bs.getD 31 0#8) &&& 0x7f#8]

private theorem p25519_lt_two_pow_255 : p25519 < 2 ^ 255 := by unfold p25519; decide +kernel
private theorem bv8_ofNat_toNat (b : BitVec 8) : BitVec.ofNat 8 b.toNat = b :=
  BitVec.eq_of_toNat_eq (by simp)
private theorem bv8_mask1_shl7 : ∀ x : Fin 256,
    ((BitVec.ofNat 8 x.val &&& 1#8) <<< 7) = (BitVec.ofNat 8 x.val <<< 7) := by decide +kernel
private theorem bv8_shl7_eq : ∀ x : Fin 256,
    (BitVec.ofNat 8 x.val <<< 7) = BitVec.ofNat 8 ((x.val % 2) * 128) := by decide +kernel
private theorem bv8_and_7f_eq : ∀ x : Fin 256,
    (BitVec.ofNat 8 x.val &&& 0x7f#8) = BitVec.ofNat 8 (x.val % 128) := by decide +kernel
private theorem bv8_or_sign_eq : ∀ x : Fin 128, ∀ s : Fin 2,
    (BitVec.ofNat 8 x.val ||| BitVec.ofNat 8 (s.val * 128)) = BitVec.ofNat 8 (x.val + s.val * 128) := by decide +kernel
private theorem bv8_and_one_toNat : ∀ x : Fin 256, (BitVec.ofNat 8 x.val).toNat &&& 1 = x.val % 2 := by decide +kernel

theorem sign_toNat_and_one (sign : BitVec 8) : sign.toNat &&& 1 = sign.toNat % 2 := by
  have h := bv8_and_one_toNat ⟨sign.toNat, sign.isLt⟩; rwa [bv8_ofNat_toNat] at h

private theorem natToLeBytes_32_split (n : Nat) :
    natToLeBytes 32 n = (List.range 31).map (fun i => BitVec.ofNat 8 ((n / 256 ^ i) % 256)) ++
      [BitVec.ofNat 8 ((n / 256 ^ 31) % 256)] := by
  unfold natToLeBytes; rw [show (32 : Nat) = 31 + 1 from rfl, List.range_succ, List.map_append, List.map_singleton]

private theorem low_byte_add_two_pow_255 (y s i : Nat) (hi : i < 31) :
    ((y + s * 2 ^ 255) / 256 ^ i) % 256 = (y / 256 ^ i) % 256 := by
  have hpow : 2 ^ 255 = (2 ^ (255 - 8 * (i + 1)) * 256) * 256 ^ i := by
    rw [show 256 ^ i = 2 ^ (8 * i) by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul],
        show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add, ← Nat.pow_add]
    congr 1; omega
  rw [hpow, ← Nat.mul_assoc s, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
      Nat.add_mul_mod_self_right]

private theorem top_byte_add_two_pow_255 {y s : Nat} (hy : y < 2 ^ 255) (hs : s < 2) :
    ((y + s * 2 ^ 255) / 256 ^ 31) % 256 = y / 256 ^ 31 + s * 128 := by
  (have h31 : 256 ^ 31 = 2 ^ 248 := by decide +kernel); (have h255 : 2 ^ 255 = 128 * 2 ^ 248 := by decide +kernel)
  rw [h31, h255]; omega

theorem setSignBit_eq_or_of_lt {bs : List (BitVec 8)} (sign : BitVec 8) (hb : (bs.getD 31 0#8).toNat < 128) :
    setSignBit bs sign = bs.take 31 ++ [(bs.getD 31 0#8) ||| (sign <<< 7)] := by
  unfold setSignBit; congr 2; congr 1
  · have h := bv8_and_7f_eq ⟨(bs.getD 31 0#8).toNat, (bs.getD 31 0#8).isLt⟩
    rw [bv8_ofNat_toNat, Nat.mod_eq_of_lt hb, bv8_ofNat_toNat] at h; exact h
  · have h1 := bv8_mask1_shl7 ⟨sign.toNat, sign.isLt⟩; rwa [bv8_ofNat_toNat] at h1

theorem setSignBit_natToLeBytes_eq {y : Nat} (hy : y < 2 ^ 255) (sign : BitVec 8) :
    setSignBit (natToLeBytes 32 y) sign = natToLeBytes 32 (y + (sign.toNat % 2) * 2 ^ 255) := by
  unfold setSignBit; rw [natToLeBytes_32_split y, natToLeBytes_32_split (y + (sign.toNat % 2) * 2 ^ 255)]
  have hlen : ((List.range 31).map (fun i => BitVec.ofNat 8 ((y / 256 ^ i) % 256))).length = 31 := by simp
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hget : ((List.range 31).map (fun i => BitVec.ofNat 8 ((y / 256 ^ i) % 256)) ++
      [BitVec.ofNat 8 ((y / 256 ^ 31) % 256)]).getD 31 0#8 = BitVec.ofNat 8 ((y / 256 ^ 31) % 256) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp [hlen]
  rw [hget]; congr 1
  · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi
    rw [low_byte_add_two_pow_255 y (sign.toNat % 2) i hi]
  · congr 1; have hy_div : y / 256 ^ 31 < 128 := by (have : 2 ^ 255 = 128 * 256 ^ 31 := by decide +kernel); omega
    rw [show (y / 256 ^ 31) % 256 = y / 256 ^ 31 by omega, top_byte_add_two_pow_255 hy (Nat.mod_lt _ (by decide))]
    have h1 := bv8_and_7f_eq ⟨y / 256 ^ 31, by omega⟩
    have h2 := bv8_mask1_shl7 ⟨sign.toNat, sign.isLt⟩; have h3 := bv8_shl7_eq ⟨sign.toNat, sign.isLt⟩
    rw [bv8_ofNat_toNat] at h2 h3; rw [h1, Nat.mod_eq_of_lt hy_div, h2, h3]
    exact bv8_or_sign_eq ⟨y / 256 ^ 31, hy_div⟩ ⟨sign.toNat % 2, Nat.mod_lt _ (by decide)⟩

private def decodeDalekWith2 (recFn : Nat → Option Nat) (p : Nat) (bs : List (BitVec 8)) : Option EdPoint :=
  if bs.length != 32 then none
  else
    let n := leBytesToNat bs; let yRaw := n % (2 ^ 255); let sign := (n / (2 ^ 255)) % 2; let y := yRaw % p
    decodeEdDalek.match_1 (fun _ => Option EdPoint) (recFn y) (fun _ => none)
      (fun xEven => let x := if sign == 1 then fpNeg xEven else xEven; some ⟨x, y⟩)

private theorem decodeEdDalek_eq_with2 (bs : List (BitVec 8)) :
    decodeEdDalek bs = decodeDalekWith2 recoverXEven p25519 bs := rfl

private theorem decodeDalekWith2_natToLeBytes (recFn : Nat → Option Nat) (p y s : Nat)
    (hy_p : y < p) (hy_255 : y < 2 ^ 255) (hs : s < 2) :
    decodeDalekWith2 recFn p (natToLeBytes 32 (y + s * 2 ^ 255)) =
      decodeEdDalek.match_1 (fun _ => Option EdPoint) (recFn y) (fun _ => none)
        (fun xEven => let x := if s == 1 then fpNeg xEven else xEven; some ⟨x, y⟩) := by
  unfold decodeDalekWith2
  have hlen : (natToLeBytes 32 (y + s * 2 ^ 255)).length = 32 := by simp [natToLeBytes]
  have hlt256 : y + s * 2 ^ 255 < 256 ^ 32 := by (have : 256 ^ 32 = 2 * 2 ^ 255 := by decide +kernel); omega
  have hleb := leBytesToNat_natToLeBytes_of_lt hlt256
  have hyraw : (y + s * 2 ^ 255) % 2 ^ 255 = y := by omega
  have hsign : ((y + s * 2 ^ 255) / 2 ^ 255) % 2 = s := by omega
  rw [show ((natToLeBytes 32 (y + s * 2 ^ 255)).length != 32) = false by simp [hlen]]
  simp only [Bool.false_eq_true, ↓reduceIte, hleb, hyraw, Nat.mod_eq_of_lt hy_p, hsign]

private def montLiftBody (recFn : Nat → Option Nat) (b : Bool) (y sign : Nat) : Option EdPoint :=
  if b then none
  else montToEdwards.match_1 (fun _ => Option EdPoint) (recFn y) (fun _ => none)
    (fun xEven => let x := if sign % 2 == 1 then fpNeg xEven else xEven; some ⟨x, y⟩)

private theorem montLiftWith_eq_body (recFn : Nat → Option Nat) (u p1 sign : Nat) :
    montLiftWith recFn u p1 sign = montLiftBody recFn (u == p1) (fpMul (fpSub u 1) (fpInv (fpAdd u 1))) sign := rfl

attribute [local irreducible] decodeEdDalek

private theorem montMatch_eq_decodeDalekWith2 (recFn : Nat → Option Nat) (p y : Nat) (sign : BitVec 8)
    (hy_p : y < p) (hy_255 : y < 2 ^ 255) :
    montToEdwards.match_1 (fun _ => Option EdPoint) (recFn y) (fun _ => none)
      (fun xEven => let x := if (sign.toNat &&& 1) % 2 == 1 then fpNeg xEven else xEven; some ⟨x, y⟩) =
      decodeDalekWith2 recFn p (setSignBit (natToLeBytes 32 y) sign) := by
  have hs : sign.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  have hand : (sign.toNat &&& 1) % 2 = sign.toNat % 2 := by rw [sign_toNat_and_one, Nat.mod_mod]
  refine Eq.trans ?_ (Eq.symm (Eq.trans (congrArg (decodeDalekWith2 recFn p) (setSignBit_natToLeBytes_eq hy_255 sign))
    (decodeDalekWith2_natToLeBytes recFn p y (sign.toNat % 2) hy_p hy_255 hs)))
  rw [hand]; cases recFn y <;> rfl

private theorem montLiftBody_eq_decodeDalekWith2 (recFn : Nat → Option Nat) (b : Bool) (p y : Nat) (sign : BitVec 8)
    (hy_p : y < p) (hy_255 : y < 2 ^ 255) :
    montLiftBody recFn b y (sign.toNat &&& 1) =
      if b then none else decodeDalekWith2 recFn p (setSignBit (natToLeBytes 32 y) sign) := by
  cases b with
  | true => rfl
  | false => exact montMatch_eq_decodeDalekWith2 recFn p y sign hy_p hy_255

/-- Exact operational equivalence between `montToEdwards` and `MontgomeryPoint::to_edwards`. -/
theorem montToEdwards_eq_decodeEdDalek (bs : List (BitVec 8)) (sign : BitVec 8) :
    let u := decodeU255 bs % p25519
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    montToEdwards bs (sign.toNat &&& 1) =
      if u == p25519 - 1 then none else decodeEdDalek (setSignBit (natToLeBytes 32 y) sign) := by
  let u := decodeU255 bs % p25519; let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
  have hy_p : y < p25519 := fpMul_lt _ _; have hy_255 : y < 2 ^ 255 := Nat.lt_trans hy_p p25519_lt_two_pow_255
  refine Eq.trans (montToEdwards_eq_liftWith bs (sign.toNat &&& 1)) ?_
  refine Eq.trans (montLiftWith_eq_body recoverXEven u (p25519 - 1) (sign.toNat &&& 1)) ?_
  refine Eq.trans (montLiftBody_eq_decodeDalekWith2 recoverXEven (u == p25519 - 1) p25519 y sign hy_p hy_255) ?_
  exact congrArg (fun z => if u == p25519 - 1 then none else z)
    (Eq.symm (decodeEdDalek_eq_with2 (setSignBit (natToLeBytes 32 y) sign)))

/-! ## 5. XEdDSA Round-Trip Bridge & Clamped Basepoint Non-Zero -/

private theorem montLiftBody_sign_mod_two (recFn : Nat → Option Nat) (b : Bool) (y sign : Nat) :
    montLiftBody recFn b y (sign % 2) = montLiftBody recFn b y sign := by
  cases b with
  | true => rfl
  | false => unfold montLiftBody; dsimp only [Bool.false_eq_true, ↓reduceIte]; rw [Nat.mod_mod]

theorem montToEdwards_sign_mod_two (bs : List (BitVec 8)) (sign : Nat) :
    montToEdwards bs (sign % 2) = montToEdwards bs sign := by
  let u := decodeU255 bs % p25519; let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
  refine Eq.trans (montToEdwards_eq_liftWith bs (sign % 2)) ?_
  refine Eq.trans (montLiftWith_eq_body recoverXEven u (p25519 - 1) (sign % 2)) ?_
  refine Eq.trans (montLiftBody_sign_mod_two recoverXEven (u == p25519 - 1) y sign) ?_
  exact Eq.symm (Eq.trans (montToEdwards_eq_liftWith bs sign) (montLiftWith_eq_body recoverXEven u (p25519 - 1) sign))

theorem decodeU255_natToLeBytes_of_lt {u : Nat} (hu : u < 2 ^ 255) : decodeU255 (natToLeBytes 32 u) = u := by
  unfold decodeU255
  have htake : (natToLeBytes 32 u).take 32 = natToLeBytes 32 u := List.take_of_length_le (by simp [natToLeBytes])
  have hlt : u < 256 ^ 32 := by (have : 256 ^ 32 = 2 * 2 ^ 255 := by decide +kernel); omega
  exact Eq.trans (congrArg (fun l => leBytesToNat l % 2 ^ 255) htake)
    (Eq.trans (congrArg (· % 2 ^ 255) (leBytesToNat_natToLeBytes_of_lt hlt)) (Nat.mod_eq_of_lt hu))

theorem decodeU255_natToLeBytes_edToMontU (P : EdPoint) :
    decodeU255 (natToLeBytes 32 (edToMontU P)) % p25519 = edToMontU P :=
  Eq.trans (congrArg (· % p25519)
    (decodeU255_natToLeBytes_of_lt (Nat.lt_trans (edToMontU_lt P) p25519_lt_two_pow_255)))
    (Nat.mod_eq_of_lt (edToMontU_lt P))

private theorem bv8_shr7_sign : ∀ x : Fin 128, ∀ s : Fin 2,
    (BitVec.ofNat 8 (x.val + s.val * 128) >>> 7).toNat = s.val := by decide +kernel
private theorem bv8_and80_shr7_sign : ∀ x : Fin 128, ∀ s : Fin 2,
    ((BitVec.ofNat 8 (x.val + s.val * 128) &&& 0x80#8) >>> 7).toNat = s.val := by decide +kernel

private theorem natToLeBytes_32_getD_31_add {y s : Nat} (hy : y < 2 ^ 255) (hs : s < 2) :
    (natToLeBytes 32 (y + s * 2 ^ 255)).getD 31 0#8 = BitVec.ofNat 8 (y / 256 ^ 31 + s * 128) := by
  rw [natToLeBytes_32_split]
  have hlen : ((List.range 31).map (fun i => BitVec.ofNat 8 (((y + s * 2 ^ 255) / 256 ^ i) % 256))).length = 31 := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, top_byte_add_two_pow_255 hy hs]

theorem encodeEd_eq_of_onCurve {A : EdPoint} (hA : edOnCurve A = true) :
    encodeEd A = natToLeBytes 32 (A.y + (A.x % 2) * 2 ^ 255) := by
  unfold encodeEd; dsimp only []
  exact congrArg (natToLeBytes 32) (by rw [Nat.mod_eq_of_lt (edOnCurve_y_lt hA), Nat.mod_eq_of_lt (edOnCurve_x_lt hA)])

theorem encodeEd_getD_31_shr7 {A : EdPoint} (hA : edOnCurve A = true) :
    ((encodeEd A).getD 31 0#8 >>> 7).toNat = A.x % 2 := by
  have hy_255 := Nat.lt_trans (edOnCurve_y_lt hA) p25519_lt_two_pow_255
  have hy_div : A.y / 256 ^ 31 < 128 := by (have : 2 ^ 255 = 128 * 256 ^ 31 := by decide +kernel); omega
  have hs : A.x % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [encodeEd_eq_of_onCurve hA, natToLeBytes_32_getD_31_add hy_255 hs]
  exact bv8_shr7_sign ⟨A.y / 256 ^ 31, hy_div⟩ ⟨A.x % 2, hs⟩

theorem encodeEd_getD_31_and80_shr7 {A : EdPoint} (hA : edOnCurve A = true) :
    (((encodeEd A).getD 31 0#8 &&& 0x80#8) >>> 7).toNat = A.x % 2 := by
  have hy_255 := Nat.lt_trans (edOnCurve_y_lt hA) p25519_lt_two_pow_255
  have hy_div : A.y / 256 ^ 31 < 128 := by (have : 2 ^ 255 = 128 * 256 ^ 31 := by decide +kernel); omega
  have hs : A.x % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [encodeEd_eq_of_onCurve hA, natToLeBytes_32_getD_31_add hy_255 hs]
  exact bv8_and80_shr7_sign ⟨A.y / 256 ^ 31, hy_div⟩ ⟨A.x % 2, hs⟩

theorem clearSignBit_natToLeBytes_add {y s : Nat} (hy : y < 2 ^ 255) (hs : s < 2) :
    clearSignBit (natToLeBytes 32 (y + s * 2 ^ 255)) = natToLeBytes 32 y := by
  unfold clearSignBit
  rw [natToLeBytes_32_getD_31_add hy hs, natToLeBytes_32_split (y + s * 2 ^ 255), natToLeBytes_32_split y]
  have hlen : ((List.range 31).map (fun i => BitVec.ofNat 8 (((y + s * 2 ^ 255) / 256 ^ i) % 256))).length = 31 := by simp
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]; congr 1
  · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi
    exact congrArg (BitVec.ofNat 8) (low_byte_add_two_pow_255 y s i hi)
  · congr 1; have hy_div : y / 256 ^ 31 < 128 := by (have : 2 ^ 255 = 128 * 256 ^ 31 := by decide +kernel); omega
    rw [bv8_and_7f_eq ⟨y / 256 ^ 31 + s * 128, by omega⟩,
        show (y / 256 ^ 31 + s * 128) % 128 = y / 256 ^ 31 by omega, show (y / 256 ^ 31) % 256 = y / 256 ^ 31 by omega]

theorem clearSignBit_encodeEd {A : EdPoint} (hA : edOnCurve A = true) :
    clearSignBit (encodeEd A) = encodeEd (if A.x % 2 == 1 then edNeg A else A) := by
  have hy_p := edOnCurve_y_lt hA; have hx_p := edOnCurve_x_lt hA
  have hy_255 := Nat.lt_trans hy_p p25519_lt_two_pow_255; have hs : A.x % 2 < 2 := Nat.mod_lt _ (by decide)
  refine Eq.trans (congrArg clearSignBit (encodeEd_eq_of_onCurve hA)) (Eq.trans (clearSignBit_natToLeBytes_add hy_255 hs) ?_)
  rcases Nat.mod_two_eq_zero_or_one A.x with hx0 | hx1
  · have hb : (A.x % 2 == 1) = false := by rw [hx0]; rfl
    rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact Eq.symm (Eq.trans (encodeEd_eq_of_onCurve hA) (by rw [hx0]; simp))
  · have hb : (A.x % 2 == 1) = true := by rw [hx1]; rfl
    rw [hb]; simp only [↓reduceIte]; have hx_ne : A.x % p25519 ≠ 0 := by rw [Nat.mod_eq_of_lt hx_p]; omega
    have hneg_even : (edNeg A).x % 2 = 0 := by dsimp only [edNeg]; rw [fpNeg_mod_two_of_ne_zero hx_ne, Nat.mod_eq_of_lt hx_p, hx1]
    have hneg_y : (edNeg A).y = A.y := by dsimp only [edNeg]; exact Nat.mod_eq_of_lt hy_p
    exact Eq.symm (Eq.trans (encodeEd_eq_of_onCurve (edOnCurve_edNeg hA)) (by rw [hneg_even, hneg_y]; simp))

/-- XEdDSA inverse round-trip: lifting `edToMontU A` with sign `A.x % 2` recovers `A`. -/
theorem montToEdwards_edToMontU {A : EdPoint} (hA : edOnCurve A = true) (hne : A ≠ edZero) :
    montToEdwards (natToLeBytes 32 (edToMontU A)) (A.x % 2) = some A := by
  have hy_p := edOnCurve_y_lt hA; have hy_255 := Nat.lt_trans hy_p p25519_lt_two_pow_255
  have hy1 : A.y ≠ 1 := fun h1 => hne ((edOnCurve_eq_edZero_iff_y_eq_one hA).mpr h1)
  let sign : BitVec 8 := BitVec.ofNat 8 (A.x % 2)
  have hs_mod : sign.toNat % 2 = A.x % 2 := by
    have : A.x % 2 < 2 := Nat.mod_lt _ (by decide); dsimp only [sign]; rw [BitVec.toNat_ofNat]; omega
  have hs_and : sign.toNat &&& 1 = A.x % 2 := by rw [sign_toNat_and_one, hs_mod]
  have hbridge : montToEdwards (natToLeBytes 32 (edToMontU A)) (sign.toNat &&& 1) =
      if decodeU255 (natToLeBytes 32 (edToMontU A)) % p25519 == p25519 - 1 then none
      else decodeEdDalek (setSignBit (natToLeBytes 32
        (fpMul (fpSub (decodeU255 (natToLeBytes 32 (edToMontU A)) % p25519) 1)
          (fpInv (fpAdd (decodeU255 (natToLeBytes 32 (edToMontU A)) % p25519) 1)))) sign) :=
    montToEdwards_eq_decodeEdDalek (natToLeBytes 32 (edToMontU A)) sign
  have hu := decodeU255_natToLeBytes_edToMontU A
  have hb : (edToMontU A == p25519 - 1) = false :=
    Bool.eq_false_iff.mpr (fun heq => edToMontU_ne_p25519_sub_one A (beq_iff_eq.mp heq))
  have hy_rec := birational_y_of_u hy_p hy1
  have hset : setSignBit (natToLeBytes 32 A.y) sign = encodeEd A :=
    Eq.trans (setSignBit_natToLeBytes_eq hy_255 sign)
      (Eq.trans (congrArg (fun k => natToLeBytes 32 (A.y + k * 2 ^ 255)) hs_mod) (Eq.symm (encodeEd_eq_of_onCurve hA)))
  have hite : ∀ {c : Bool} {x y : Option EdPoint}, c = false → x = y → (if c then none else x) = y := by
    rintro _ _ _ rfl rfl; rfl
  refine Eq.trans (congrArg (montToEdwards (natToLeBytes 32 (edToMontU A))) hs_and.symm) (Eq.trans hbridge ?_)
  have hcond := Eq.trans (congrArg (· == p25519 - 1) hu) hb
  have hy_full := Eq.trans (congrArg (fun z => fpMul (fpSub z 1) (fpInv (fpAdd z 1))) hu) hy_rec
  exact Eq.trans (hite hcond (congrArg (fun z => decodeEdDalek (setSignBit (natToLeBytes 32 z) sign)) hy_full))
    (Eq.trans (congrArg decodeEdDalek hset) (decodeEdDalek_encodeEd hA))

theorem montToEdwards_edToMontU_encodeSign {A : EdPoint} (hA : edOnCurve A = true) (hne : A ≠ edZero) :
    montToEdwards (natToLeBytes 32 (edToMontU A)) (((encodeEd A).getD 31 0#8 &&& 0x80#8) >>> 7).toNat = some A := by
  rw [encodeEd_getD_31_and80_shr7 hA]; exact montToEdwards_edToMontU hA hne

section
set_option maxRecDepth 20000
private theorem w4_prime_2551 : IsPrime 2551 := smallPrime_of_check (B := 51) (by decide +kernel)
private theorem w4_prime_531581 : IsPrime 531581 := smallPrime_of_check (B := 730) (by decide +kernel)
private theorem w4_prime_ed_q1 : IsPrime 1224481 := pocklington1 w4_prime_2551 (a := 2) (by decide +kernel)
private theorem w4_prime_ed_q2 : IsPrime 1257559732178653 :=
  pocklington2 w4_prime_ed_q1 w4_prime_531581 (a := 2) (by decide +kernel)
private theorem w4_prime_ed_q3 : IsPrime 4434155615661930479 := pocklington1 w4_prime_ed_q2 (a := 2) (by decide +kernel)
private theorem w4_prime_ed_q4 : IsPrime 172054593956031949258510691 :=
  pocklington1 w4_prime_ed_q3 (a := 2) (by decide +kernel)
private theorem w4_prime_ed_q5 : IsPrime 19757330305831588566944191468367130476339 :=
  pocklington1 w4_prime_ed_q4 (a := 2) (by decide +kernel)
private theorem w4_prime_ed_q6 : IsPrime 276602624281642239937218680557139826668747 :=
  pocklington1 w4_prime_ed_q5 (a := 2) (by decide +kernel)
private theorem w4_edOrderL_prime : IsPrime edOrderL :=
  pocklington1 w4_prime_ed_q6 (a := 2) (by unfold edOrderL; decide +kernel)
end

theorem edBasepoint_ne_edZero : edBasepoint ≠ edZero := by unfold edBasepoint edZero; decide +kernel

private theorem edNatSmul_edBasepoint_mod (a : Nat) (ha : edNatSmul a edBasepoint = edZero) :
    ∀ b, edNatSmul b edBasepoint = edZero → edNatSmul (b % a) edBasepoint = edZero := by
  intro b; induction b using Nat.strongRecOn with
  | ind b ih =>
    intro hb; by_cases ha0 : a = 0
    · subst ha0; simpa using hb
    · by_cases hlt : b < a
      · rwa [Nat.mod_eq_of_lt hlt]
      · have hle : a ≤ b := by omega
        rw [Nat.mod_eq_sub_mod hle]; apply ih (b - a) (by omega)
        have hadd := edNatSmul_add (b - a) a edOnCurve_edBasepoint
        rw [Nat.sub_add_cancel hle, hb, ha, edAdd_edZero (edOnCurve_edNatSmul (b - a) edOnCurve_edBasepoint)] at hadd
        exact hadd.symm

private theorem edNatSmul_edBasepoint_gcd :
    ∀ a b, edNatSmul a edBasepoint = edZero → edNatSmul b edBasepoint = edZero →
      edNatSmul (Nat.gcd a b) edBasepoint = edZero := by
  intro a; induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b ha hb; by_cases ha0 : a = 0
    · subst ha0; simpa using hb
    · rw [Nat.gcd_rec a b]; exact ih (b % a) (Nat.mod_lt b (by omega)) a (edNatSmul_edBasepoint_mod a ha b hb) ha

theorem edNatSmul_edBasepoint_eq_edZero_iff (n : Nat) : edNatSmul n edBasepoint = edZero ↔ edOrderL ∣ n := by
  refine ⟨fun hn => ?_, fun ⟨q, hq⟩ => hq ▸ edNatSmul_mul_edOrderL_edBasepoint q⟩
  have hg := edNatSmul_edBasepoint_gcd n edOrderL hn edNatSmul_edOrderL_edBasepoint
  rcases w4_edOrderL_prime.2 _ (Nat.gcd_dvd_right n edOrderL) with h1 | hL
  · rw [h1, edNatSmul_one edOnCurve_edBasepoint] at hg; exact absurd hg edBasepoint_ne_edZero
  · exact hL ▸ Nat.gcd_dvd_left n edOrderL

theorem edSmul_edBasepoint_eq_edZero_iff {n : Nat} (hn : n < 2 ^ 256) :
    edSmul n edBasepoint = edZero ↔ edOrderL ∣ n := by
  rw [edSmul_eq_edNatSmul hn edOnCurve_edBasepoint]; exact edNatSmul_edBasepoint_eq_edZero_iff n

private theorem leBytesToNat_append (xs ys : List (BitVec 8)) :
    leBytesToNat (xs ++ ys) = leBytesToNat ys * 256 ^ xs.length + leBytesToNat xs := by
  induction xs with
  | nil => simp [leBytesToNat_nil]
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, leBytesToNat_cons, ih, Nat.pow_succ]
    rw [← Nat.mul_assoc (leBytesToNat ys) (256 ^ xs.length) 256]; omega

private theorem bv8_clamp_b0 : ∀ x : Fin 256, (BitVec.ofNat 8 x.val &&& 0xf8#8).toNat % 8 = 0 := by decide +kernel
private theorem bv8_clamp_b31 : ∀ x : Fin 256,
    64 ≤ ((BitVec.ofNat 8 x.val &&& 0x7f#8) ||| 0x40#8).toNat ∧
    ((BitVec.ofNat 8 x.val &&& 0x7f#8) ||| 0x40#8).toNat < 128 := by decide +kernel

theorem clampScalar_props (bs : List (BitVec 8)) :
    0 < clampScalar bs ∧ clampScalar bs < 2 ^ 255 ∧ clampScalar bs % 8 = 0 := by
  unfold clampScalar clampScalarBytes; dsimp only []
  let b0 := ((bs.take 32).getD 0 0#8) &&& 0xf8#8; let mid := ((bs.take 32).drop 1).take 30
  let b31 := (((bs.take 32).getD 31 0#8) &&& 0x7f#8) ||| 0x40#8
  have hb0 : b0.toNat % 8 = 0 := by
    have h := bv8_clamp_b0 ⟨((bs.take 32).getD 0 0#8).toNat, ((bs.take 32).getD 0 0#8).isLt⟩
    rwa [bv8_ofNat_toNat] at h
  have hb31 : 64 ≤ b31.toNat ∧ b31.toNat < 128 := by
    have h := bv8_clamp_b31 ⟨((bs.take 32).getD 31 0#8).toNat, ((bs.take 32).getD 31 0#8).isLt⟩
    rwa [bv8_ofNat_toNat] at h
  have hmod8 : leBytesToNat ([b0] ++ mid ++ [b31]) % 8 = 0 := by
    change leBytesToNat (b0 :: (mid ++ [b31])) % 8 = 0; rw [leBytesToNat_cons]; omega
  have hlen : ([b0] ++ mid).length ≤ 31 := by simp [mid]; omega
  have hpow_pos : 1 ≤ 256 ^ ([b0] ++ mid).length := Nat.pow_pos (by decide)
  have hpow_le : 256 ^ ([b0] ++ mid).length ≤ 256 ^ 31 := Nat.pow_le_pow_right (by decide) hlen
  have hxs_lt : leBytesToNat ([b0] ++ mid) < 256 ^ ([b0] ++ mid).length := leBytesToNat_lt _
  have happ : leBytesToNat ([b0] ++ mid ++ [b31]) = b31.toNat * 256 ^ ([b0] ++ mid).length + leBytesToNat ([b0] ++ mid) := by
    rw [leBytesToNat_append ([b0] ++ mid) [b31], leBytesToNat_cons, leBytesToNat_nil]; simp
  have hpos : 0 < leBytesToNat ([b0] ++ mid ++ [b31]) := by
    have := Nat.mul_le_mul hb31.1 hpow_pos; omega
  have hlt255 : leBytesToNat ([b0] ++ mid ++ [b31]) < 2 ^ 255 := by
    have h1 : b31.toNat * 256 ^ ([b0] ++ mid).length + leBytesToNat ([b0] ++ mid) < 128 * 256 ^ ([b0] ++ mid).length := by
      have hmul := Nat.mul_le_mul_right (256 ^ ([b0] ++ mid).length) (show b31.toNat + 1 ≤ 128 by omega)
      rw [Nat.add_mul, Nat.one_mul] at hmul; omega
    have h2 := Nat.mul_le_mul_left 128 hpow_le; (have h3 : 128 * 256 ^ 31 = 2 ^ 255 := by decide +kernel); omega
  exact ⟨hpos, hlt255, hmod8⟩

theorem not_edOrderL_dvd_clampScalar (priv : List (BitVec 8)) : ¬ (edOrderL ∣ clampScalar priv) := by
  rcases clampScalar_props priv with ⟨hpos, hlt255, hmod8⟩
  have hdiv : clampScalar priv = 8 * (clampScalar priv / 8) := by omega
  have hm_pos : 0 < clampScalar priv / 8 := by omega
  have hm_lt : clampScalar priv / 8 < edOrderL := by (have : 2 ^ 255 < 8 * edOrderL := by unfold edOrderL; decide +kernel); omega
  intro hdvd; rw [hdiv] at hdvd; rcases w4_edOrderL_prime.dvd_mul hdvd with h8 | hm
  · have := Nat.le_of_dvd (by decide) h8; (have : 8 < edOrderL := by unfold edOrderL; decide +kernel); omega
  · have := Nat.le_of_dvd hm_pos hm; omega

theorem edSmul_clampScalar_edBasepoint_ne_edZero (priv : List (BitVec 8)) :
    edSmul (clampScalar priv) edBasepoint ≠ edZero := by
  rw [ne_eq, edSmul_edBasepoint_eq_edZero_iff (clampScalar_lt_two_pow_256 priv)]; exact not_edOrderL_dvd_clampScalar priv

theorem edSmul_clampScalar_mod_edOrderL_edBasepoint (priv : List (BitVec 8)) :
    edSmul (clampScalar priv % edOrderL) edBasepoint = edSmul (clampScalar priv) edBasepoint := by
  have h1 := Nat.lt_trans (Nat.mod_lt (clampScalar priv) edOrderL_pos) edOrderL_lt_two_pow_256
  rw [edSmul_eq_edNatSmul h1 edOnCurve_edBasepoint,
      edSmul_eq_edNatSmul (clampScalar_lt_two_pow_256 priv) edOnCurve_edBasepoint, edNatSmul_mod_edOrderL_edBasepoint]

theorem edSmul_clampScalar_mod_edOrderL_ne_edZero (priv : List (BitVec 8)) :
    edSmul (clampScalar priv % edOrderL) edBasepoint ≠ edZero := by
  rw [edSmul_clampScalar_mod_edOrderL_edBasepoint]; exact edSmul_clampScalar_edBasepoint_ne_edZero priv

/-! ## 6. Full 2-, 4-, and 8-Torsion Characterization on $E(\mathbb{F}_p)$ -/

private theorem fp_two_ne_zero : (2 : Fp) ≠ 0 := by
  intro h; have hval := congrArg Fp.val h; revert hval; change 2 % p25519 = 0 → False; unfold p25519; decide +kernel

private theorem fp_edSqrtOneAddD_ne_zero : Fp.ofNat edSqrtOneAddD ≠ 0 := by
  intro h; have := Fp.eq_of_ofNat_eq (by unfold edSqrtOneAddD p25519; decide +kernel) p25519_pos h
  revert this; unfold edSqrtOneAddD; decide +kernel

private theorem fp_ofNat_p25519_sub_one : Fp.ofNat (p25519 - 1) = -1 := by
  ext; change (p25519 - 1) % p25519 = fpNeg 1; unfold fpNeg p25519; decide +kernel

private theorem fp_sqrtM1_sq : Fp.ofNat sqrtM1 * Fp.ofNat sqrtM1 = -1 := by
  have h := congrArg Fp.ofNat (by unfold fpSq fpMul fpNeg sqrtM1 p25519; decide +kernel : fpSq sqrtM1 = fpNeg 1)
  rwa [Fp.ofNat_fpSq, Fp.ofNat_fpNeg, Fp.ofNat_one] at h

theorem edOnCurve_order2 : edOnCurve { x := 0, y := p25519 - 1 } = true := by
  unfold edOnCurve fpAdd fpMul fpSq fpNeg edD p25519; decide +kernel

theorem edOnCurve_order4_pos : edOnCurve { x := sqrtM1, y := 0 } = true := by
  unfold edOnCurve fpAdd fpMul fpSq fpNeg sqrtM1 edD p25519; decide +kernel

theorem edOnCurve_order4_neg : edOnCurve { x := fpNeg sqrtM1, y := 0 } = true := by
  have hneg : edNeg { x := sqrtM1, y := 0 } = { x := fpNeg sqrtM1, y := 0 } := by unfold edNeg; simp
  rw [← hneg]
  exact edOnCurve_edNeg edOnCurve_order4_pos

private theorem edAdd_order4_neg_self :
    edAdd { x := fpNeg sqrtM1, y := 0 } { x := fpNeg sqrtM1, y := 0 } = { x := 0, y := p25519 - 1 } := by
  have hneg : edNeg { x := sqrtM1, y := 0 } = { x := fpNeg sqrtM1, y := 0 } := by unfold edNeg; simp
  rw [← hneg, ← edNeg_edAdd, edAdd_order4_pos_self]; unfold edNeg fpNeg p25519; decide +kernel

theorem edSmul_two_eq_edAdd {P : EdPoint} (hP : edOnCurve P = true) : edSmul 2 P = edAdd P P := by
  rw [edSmul_eq_edNatSmul (by decide) hP, edNatSmul_two hP]

theorem edSmul_four_eq_edSmul_two_edAdd {P : EdPoint} (hP : edOnCurve P = true) :
    edSmul 4 P = edSmul 2 (edAdd P P) := by
  rw [edSmul_eq_edNatSmul (by decide) hP, show (4 : Nat) = 2 * 2 from rfl, edNatSmul_mul 2 2 hP,
      edNatSmul_two hP, ← edSmul_eq_edNatSmul (by decide) (edOnCurve_edAdd hP hP)]

theorem edSmul_eight_eq_edSmul_four_edAdd {P : EdPoint} (hP : edOnCurve P = true) :
    edSmul 8 P = edSmul 4 (edAdd P P) := by
  rw [edSmul_eq_edNatSmul (by decide) hP, show (8 : Nat) = 4 * 2 from rfl, edNatSmul_mul 4 2 hP,
      edNatSmul_two hP, ← edSmul_eq_edNatSmul (by decide) (edOnCurve_edAdd hP hP)]

/-- Complete 2-torsion characterization on $E(\mathbb{F}_p)$. -/
theorem edSmul_two_eq_edZero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edSmul 2 P = edZero ↔ P = edZero ∨ P = { x := 0, y := p25519 - 1 } := by
  rw [edSmul_two_eq_edAdd hP]; constructor
  · intro h2
    have hx2 := congrArg Fp.ofNat (congrArg EdPoint.x h2); have hy2 := congrArg Fp.ofNat (congrArg EdPoint.y h2)
    rw [edAdd_fp_x P P] at hx2; rw [edAdd_fp_y P P] at hy2
    change _ = (0 : Fp) at hx2; change _ = (1 : Fp) at hy2
    have hcurve := edOnCurve_fp_eq hP; have hdp := edAdd_fp_denom_add_ne_zero hP hP
    have hdm := edAdd_fp_denom_sub_ne_zero hP hP; have h2ne := fp_two_ne_zero
    have hPx : P.x = 0 := Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos (by rw [Fp.ofNat_zero]; grind)
    have hy_prod : (Fp.ofNat P.y - 1) * (Fp.ofNat P.y + 1) = 0 := by grind
    by_cases hy1 : Fp.ofNat P.y - 1 = 0
    · left; have hPy : P.y = 1 := Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) (by unfold p25519; decide +kernel)
        (by rw [Fp.ofNat_one]; grind)
      cases P; simp_all [edZero]
    · right; have hy_neg1 : Fp.ofNat P.y = Fp.ofNat (p25519 - 1) := by rw [fp_ofNat_p25519_sub_one]; grind
      have hPy : P.y = p25519 - 1 := Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) (by unfold p25519; decide +kernel) hy_neg1
      cases P; simp_all
  · rintro (rfl | rfl)
    · exact edAdd_edZero edOnCurve_edZero
    · exact edAdd_order2_self

theorem edOnCurve_y_eq_zero_x {Q : EdPoint} (hQ : edOnCurve Q = true) (hy0 : Q.y = 0) :
    Q.x = sqrtM1 ∨ Q.x = fpNeg sqrtM1 := by
  have hcurve := edOnCurve_fp_eq hQ; rw [hy0, Fp.ofNat_zero] at hcurve; have hi2 := fp_sqrtM1_sq
  have hprod : (Fp.ofNat Q.x - Fp.ofNat sqrtM1) * (Fp.ofNat Q.x + Fp.ofNat sqrtM1) = 0 := by grind
  by_cases hpos : Fp.ofNat Q.x - Fp.ofNat sqrtM1 = 0
  · left; exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hQ) (by unfold sqrtM1 p25519; decide +kernel) (by grind)
  · right; have hneg : Fp.ofNat Q.x = Fp.ofNat (fpNeg sqrtM1) := by rw [Fp.ofNat_fpNeg]; grind
    exact Fp.eq_of_ofNat_eq (edOnCurve_x_lt hQ) (fpNeg_lt _) hneg

theorem edAdd_self_eq_order2_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edAdd P P = { x := 0, y := p25519 - 1 } ↔ P.y = 0 ∧ (P.x = sqrtM1 ∨ P.x = fpNeg sqrtM1) := by
  constructor
  · intro h2
    have hx2 := congrArg Fp.ofNat (congrArg EdPoint.x h2); have hy2 := congrArg Fp.ofNat (congrArg EdPoint.y h2)
    rw [edAdd_fp_x P P] at hx2; rw [edAdd_fp_y P P, fp_ofNat_p25519_sub_one] at hy2
    change _ = (0 : Fp) at hx2
    have hcurve := edOnCurve_fp_eq hP; have hdp := edAdd_fp_denom_add_ne_zero hP hP
    have hdm := edAdd_fp_denom_sub_ne_zero hP hP; have h2ne := fp_two_ne_zero
    have hy0 : P.y = 0 := Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) p25519_pos (by rw [Fp.ofNat_zero]; grind)
    exact ⟨hy0, edOnCurve_y_eq_zero_x hP hy0⟩
  · rintro ⟨hy0, hx | hx⟩
    · (have hPeq : P = { x := sqrtM1, y := 0 } := by cases P; simp_all); rw [hPeq]; exact edAdd_order4_pos_self
    · (have hPeq : P = { x := fpNeg sqrtM1, y := 0 } := by cases P; simp_all); rw [hPeq]; exact edAdd_order4_neg_self

/-- Complete 4-torsion characterization on $E(\mathbb{F}_p)$. -/
theorem edSmul_four_eq_edZero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edSmul 4 P = edZero ↔ edSmul 2 P = edZero ∨ (P.y = 0 ∧ (P.x = sqrtM1 ∨ P.x = fpNeg sqrtM1)) := by
  rw [edSmul_four_eq_edSmul_two_edAdd hP, edSmul_two_eq_edZero_iff (edOnCurve_edAdd hP hP),
      edAdd_self_eq_order2_iff hP, ← edSmul_two_eq_edAdd hP]

theorem edAdd_self_y_eq_zero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    (edAdd P P).y = 0 ↔ P.y = edOrder8Y0 ∨ P.y = fpNeg edOrder8Y0 := by
  have hcurve := edOnCurve_fp_eq hP; have hdm := edAdd_fp_denom_sub_ne_zero hP hP
  have hd_ne := Fp.edD_ne_zero; have hs0_ne := fp_edSqrtOneAddD_ne_zero
  have hs0_sq : Fp.ofNat edSqrtOneAddD * Fp.ofNat edSqrtOneAddD = 1 + Fp.ofNat edD := by
    have h := congrArg Fp.ofNat fpSq_edSqrtOneAddD; rwa [Fp.ofNat_fpSq, Fp.ofNat_fpAdd, Fp.ofNat_one] at h
  have hy0_sq : Fp.ofNat edD * (Fp.ofNat edOrder8Y0 * Fp.ofNat edOrder8Y0) + 1 = Fp.ofNat edSqrtOneAddD := by
    have h := congrArg Fp.ofNat edOrder8Y0_sq_eq
    rwa [Fp.ofNat_fpAdd, Fp.ofNat_fpMul, Fp.ofNat_fpSq, Fp.ofNat_one] at h
  constructor
  · intro hy2_0
    have hy2_fp : Fp.ofNat (edAdd P P).y = 0 := by rw [hy2_0, Fp.ofNat_zero]
    rw [edAdd_fp_y P P] at hy2_fp
    have hprod : (Fp.ofNat edD * (Fp.ofNat P.y * Fp.ofNat P.y) + 1 - Fp.ofNat edSqrtOneAddD) *
        (Fp.ofNat edD * (Fp.ofNat P.y * Fp.ofNat P.y) + 1 + Fp.ofNat edSqrtOneAddD) = 0 := by grind
    by_cases hplus : Fp.ofNat edD * (Fp.ofNat P.y * Fp.ofNat P.y) + 1 + Fp.ofNat edSqrtOneAddD = 0
    · exfalso
      have hbad_fp : Fp.ofNat (fpSq P.y) = Fp.ofNat (fpMul (fpSub (fpNeg edSqrtOneAddD) 1) (fpInv edD)) := by
        simp only [Fp.ofNat_fpSq, Fp.ofNat_fpMul, Fp.ofNat_fpSub, Fp.ofNat_fpNeg, Fp.ofNat_fpInv, Fp.ofNat_one]
        grind
      have hbad_eq := Fp.eq_of_ofNat_eq (fpSq_lt _) (fpMul_lt _ _) hbad_fp
      have hns := euler_nonsquare edTorsion8BadY2_euler
      rw [Nat.mod_eq_of_lt (fpMul_lt _ _)] at hns; exact hns ⟨P.y, hbad_eq⟩
    · have hy_diff : (Fp.ofNat P.y - Fp.ofNat edOrder8Y0) * (Fp.ofNat P.y + Fp.ofNat edOrder8Y0) = 0 := by grind
      by_cases hy_pos : Fp.ofNat P.y - Fp.ofNat edOrder8Y0 = 0
      · left; exact Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) edOrder8Y0_lt (by grind)
      · right; have hneg : Fp.ofNat P.y = Fp.ofNat (fpNeg edOrder8Y0) := by rw [Fp.ofNat_fpNeg]; grind
        exact Fp.eq_of_ofNat_eq (edOnCurve_y_lt hP) (fpNeg_lt _) hneg
  · intro hy_cases
    have hy_sq_eq : Fp.ofNat P.y * Fp.ofNat P.y = Fp.ofNat edOrder8Y0 * Fp.ofNat edOrder8Y0 := by
      rcases hy_cases with hy | hy
      · rw [hy]
      · rw [hy, Fp.ofNat_fpNeg]; grind
    apply Fp.eq_of_ofNat_eq (edAdd_y_lt P P) p25519_pos; rw [edAdd_fp_y P P, Fp.ofNat_zero]; grind

private theorem edOnCurve_y_eq_sub_one_eq_order2 {P : EdPoint}
    (hP : edOnCurve P = true) (hy : P.y = p25519 - 1) : P = { x := 0, y := p25519 - 1 } := by
  have hcurve := edOnCurve_fp_eq hP; have h1d := Fp.one_add_edD_ne_zero
  rw [hy, fp_ofNat_p25519_sub_one] at hcurve
  have hx0 : P.x = 0 := Fp.eq_of_ofNat_eq (edOnCurve_x_lt hP) p25519_pos (by rw [Fp.ofNat_zero]; grind)
  cases P; simp_all

/-- Complete 8-torsion characterization on $E(\mathbb{F}_p)$ in terms of the 4 Montgomery $u$-coordinates. -/
theorem edSmul_eight_eq_edZero_iff {P : EdPoint} (hP : edOnCurve P = true) :
    edSmul 8 P = edZero ↔
      edToMontU P ∈ [0, 1,
        325606250916557431795983626356110631294008115727848805560023387167927233504,
        39382357235489614581723060781553021112529911719440698176882885853963445705823] := by
  have h2P : edOnCurve (edAdd P P) = true := edOnCurve_edAdd hP hP
  have h8 : edSmul 8 P = edZero ↔ (P = edZero ∨ P = { x := 0, y := p25519 - 1 }) ∨
      P.y = 0 ∨ (P.y = edOrder8Y0 ∨ P.y = fpNeg edOrder8Y0) := by
    rw [edSmul_eight_eq_edSmul_four_edAdd hP, edSmul_four_eq_edZero_iff h2P,
        ← edSmul_four_eq_edSmul_two_edAdd hP, edSmul_four_eq_edZero_iff hP, edSmul_two_eq_edZero_iff hP]
    have h4y : (P.y = 0 ∧ (P.x = sqrtM1 ∨ P.x = fpNeg sqrtM1)) ↔ P.y = 0 :=
      ⟨fun h => h.1, fun hy0 => ⟨hy0, edOnCurve_y_eq_zero_x hP hy0⟩⟩
    have h8y : ((edAdd P P).y = 0 ∧ ((edAdd P P).x = sqrtM1 ∨ (edAdd P P).x = fpNeg sqrtM1)) ↔
        (P.y = edOrder8Y0 ∨ P.y = fpNeg edOrder8Y0) :=
      Iff.trans ⟨fun h => h.1, fun hy0 => ⟨hy0, edOnCurve_y_eq_zero_x h2P hy0⟩⟩ (edAdd_self_y_eq_zero_iff hP)
    rw [h4y, h8y, or_assoc]
  rw [h8]; change _ ↔ edToMontU P ∈ [0, 1, montLowOrderU2, montLowOrderU3]
  constructor
  · rintro ((rfl | rfl) | hy0 | (hy_pos | hy_neg))
    · rw [edToMontU_edZero]; simp
    · rw [edToMontU_order2]; simp
    · have hu1 : edToMontU P = 1 := by unfold edToMontU; rw [hy0]; exact edToMontU_zero_y_val
      rw [hu1]; simp
    · have hu3 : edToMontU P = montLowOrderU3 := by unfold edToMontU; rw [hy_pos]; exact edOrder8Y0_edToMontU_pos
      rw [hu3]; simp
    · have hu2 : edToMontU P = montLowOrderU2 := by unfold edToMontU; rw [hy_neg]; exact edOrder8Y0_edToMontU_neg
      rw [hu2]; simp
  · intro hmem; by_cases hy1 : P.y = 1
    · exact Or.inl (Or.inl ((edOnCurve_eq_edZero_iff_y_eq_one hP).mpr hy1))
    · have hy_inv : fpMul (fpSub (edToMontU P) 1) (fpInv (fpAdd (edToMontU P) 1)) = P.y :=
        birational_y_of_u (edOnCurve_y_lt hP) hy1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hu0 | hu1 | hu2 | hu3
      · rw [hu0] at hy_inv
        have h0_inv : fpMul (fpSub 0 1) (fpInv (fpAdd 0 1)) = p25519 - 1 := by
          have := birational_y_of_u (y := p25519 - 1) (by unfold p25519; decide +kernel) (by unfold p25519; decide +kernel)
          dsimp only [] at this; have hu_ord2 : fpMul (fpAdd 1 (p25519 - 1)) (fpInv (fpSub 1 (p25519 - 1))) = 0 := edToMontU_order2
          rwa [hu_ord2] at this
        exact Or.inl (Or.inr (edOnCurve_y_eq_sub_one_eq_order2 hP (hy_inv.symm.trans h0_inv)))
      · rw [hu1] at hy_inv
        have h1_inv : fpMul (fpSub 1 1) (fpInv (fpAdd 1 1)) = 0 := by
          have := birational_y_of_u (y := 0) p25519_pos (by decide); dsimp only [] at this; rwa [edToMontU_zero_y_val] at this
        exact Or.inr (Or.inl (hy_inv.symm.trans h1_inv))
      · rw [hu2] at hy_inv
        have hu2_inv : fpMul (fpSub montLowOrderU2 1) (fpInv (fpAdd montLowOrderU2 1)) = fpNeg edOrder8Y0 := by
          have := birational_y_of_u (y := fpNeg edOrder8Y0) (fpNeg_lt _) (by unfold fpNeg edOrder8Y0 p25519; decide +kernel)
          dsimp only [] at this; rwa [edOrder8Y0_edToMontU_neg] at this
        exact Or.inr (Or.inr (Or.inr (hy_inv.symm.trans hu2_inv)))
      · rw [hu3] at hy_inv
        have hu3_inv : fpMul (fpSub montLowOrderU3 1) (fpInv (fpAdd montLowOrderU3 1)) = edOrder8Y0 := by
          have := birational_y_of_u (y := edOrder8Y0) edOrder8Y0_lt (by unfold edOrder8Y0; decide +kernel)
          dsimp only [] at this; rwa [edOrder8Y0_edToMontU_pos] at this
        exact Or.inr (Or.inr (Or.inl (hy_inv.symm.trans hu3_inv)))

/-- On-curve half of `X25519ZeroIffLowOrderStmt`: for $P \in E(\mathbb{F}_p)$, $[8]P = \mathcal{O}$
    iff `edToMontU P ∈ lowOrderUs`. -/
theorem edSmul_eight_eq_edZero_iff_lowOrderUs {P : EdPoint} (hP : edOnCurve P = true) :
    edSmul 8 P = edZero ↔ edToMontU P ∈ lowOrderUs := by
  rw [edSmul_eight_eq_edZero_iff hP]; unfold lowOrderUs
  have hne : edToMontU P ≠ p25519 - 1 := edToMontU_ne_p25519_sub_one P
  simp only [List.mem_cons, List.not_mem_nil, or_false, hne]

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational

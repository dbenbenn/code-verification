/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith -- proof-setup: allow-public-import

/-!
# NEON NTT base-case multiplication and dot-product soundness

1. `PolyBounded16` and `PolyRepresents` / `PolyRepresentsMontInv` predicates connecting
   signed `Poly16` (`256 × BitVec 16`) to canonical `Spec.Poly` (`256 × Nat`).
2. Soundness and signed bound (`≤ 2176 ≤ 3328`) of `Spec.neonPolyNttMul16` against
   `Spec.polyNttMul` (producing `R⁻¹`-scaled Montgomery outputs where `out * 65536 ≡ polyNttMul (mod 3329)`),
   plus `RoTables.zetaTableAt` table lookup equivalence.
3. `to_standard_domain` (`neonMontgomeryMul16 · 1353#16` + `toUnsignedRep16`) recovery of
   `Spec.polyNttMul` (used in `KeyGen` `Â ◦ ŝ + ê`).
4. `K`-way (`K = 3` and `K = 4`) NTT dot-product accumulation without `i16` overflow (`≤ 8704 < 32768`)
   matching `Spec.vecDotNtt`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 mlkemQ zeroPoly fipsZetas zetasTimesMontgomeryR
  polyAdd polyNttMul vecDotNtt sqdmulh16
  neonMontgomeryReduce16 neonMontgomeryMul16 neonPolyNttMul16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  zetaTableAt_eq_zetasTimesMontgomeryR
  zetasTimesMontgomeryR_bounds zetasTimesMontgomeryR_neg_toInt
  zetasTimesMontgomeryR_mod_3329 zetasTimesMontgomeryR_neg_mod_3329
  toInt_emod_65536 toInt_mul_emod_65536
  toInt_add_of_bounds toInt_sshiftRight_16 sqdmulh16_toInt prod32_low_high_toInt
  neonMontgomeryReduce16_prod32 neonMontgomeryMul16_spec neonMontgomeryMul16_1353
  toUnsignedRep16 toUnsignedRep16_spec
)

/-! ## 1. Polynomial Representation & Signed Bound Predicates -/

/-- Every lane of `p : Poly16` has signed magnitude `≤ B`, and `p.size = 256`. -/
@[expose] def PolyBounded16 (B : Int) (p : Poly16) : Prop :=
  p.size = 256 ∧ ∀ i < 256, -B ≤ (p.getD i 0#16).toInt ∧ (p.getD i 0#16).toInt ≤ B

/-- `p : Poly16` represents `f : Poly` in the standard domain modulo `3329`. -/
@[expose] def PolyRepresents (p : Poly16) (f : Poly) : Prop :=
  p.size = 256 ∧ ∀ i < 256, (p.getD i 0#16).toInt % 3329 = ((f.getD i 0 : Int) % 3329)

/-- `p : Poly16` represents `f : Poly` in the `R⁻¹` (`2⁻¹⁶`) domain: `p[i] * 65536 ≡ f[i] (mod 3329)`. -/
@[expose] def PolyRepresentsMontInv (p : Poly16) (f : Poly) : Prop :=
  p.size = 256 ∧ ∀ i < 256, ((p.getD i 0#16).toInt * 65536) % 3329 = ((f.getD i 0 : Int) % 3329)

private theorem abs_mul_le_nonneg {a b A B : Int}
    (ha0 : 0 ≤ a) (ha2 : a ≤ A) (hb1 : -B ≤ b) (hb2 : b ≤ B) (hB : 0 ≤ B) :
    -(A * B) ≤ a * b ∧ a * b ≤ A * B := by
  have h_aB : a * B ≤ A * B := Int.mul_le_mul_of_nonneg_right ha2 hB
  constructor
  · calc -(A * B)
        ≤ -(a * B) := Int.neg_le_neg h_aB
      _ = a * (-B) := (Int.mul_neg a B).symm
      _ ≤ a * b := Int.mul_le_mul_of_nonneg_left hb1 ha0
  · exact Int.le_trans (Int.mul_le_mul_of_nonneg_left hb2 ha0) h_aB

private theorem abs_mul_le {a b A B : Int}
    (ha1 : -A ≤ a) (ha2 : a ≤ A) (hb1 : -B ≤ b) (hb2 : b ≤ B)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) :
    -(A * B) ≤ a * b ∧ a * b ≤ A * B := by
  by_cases ha0 : 0 ≤ a
  · exact abs_mul_le_nonneg ha0 ha2 hb1 hb2 hB
  · have h := abs_mul_le_nonneg (a := -a) (b := -b) (A := A) (B := B)
      (by omega) (by omega) (by omega) (by omega) hB
    have hmul : (-a) * (-b) = a * b := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [hmul] at h
    exact h

private theorem getD_ofFn_256 {α : Type} (g : Fin 256 → α) (i : Nat) (d : α) (hi : i < 256) :
    (Array.ofFn g).getD i d = g ⟨i, hi⟩ := by
  simp [Array.getD, hi]

/-! ## 2. Exact `neonPolyNttMul16` Soundness & Signed Bound (`≤ 2176`) -/

/-- When `a1, b1` have signed magnitude `≤ 4095`, `neonMontgomeryMul16 a1 b1` has magnitude `≤ 1920`
    and satisfies `(r * 65536) % 3329 = (a1 * b1) % 3329`. -/
theorem neonMontgomeryMul16_bounded_4095 {a b : BitVec 16}
    (ha1 : -4095 ≤ a.toInt) (ha2 : a.toInt ≤ 4095)
    (hb1 : -4095 ≤ b.toInt) (hb2 : b.toInt ≤ 4095) :
    ((neonMontgomeryMul16 a b).toInt * 65536) % 3329 = (a.toInt * b.toInt) % 3329 ∧
    -1920 ≤ (neonMontgomeryMul16 a b).toInt ∧
    (neonMontgomeryMul16 a b).toInt ≤ 1920 := by
  have hne : b ≠ 0x8000#16 := by
    intro h; subst h; change -4095 ≤ -32768 at hb1; omega
  have hmod := (neonMontgomeryMul16_spec a b hne).1
  let prod32 : BitVec 32 := a.signExtend 32 * b.signExtend 32
  have hab := abs_mul_le ha1 ha2 hb1 hb2 (by omega) (by omega)
  have hp_int : prod32.toInt = a.toInt * b.toInt := by
    dsimp [prod32]
    rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
      BitVec.toInt_signExtend_of_le (by omega), Int.bmod_eq_of_le] <;> omega
  have hlow : a * b = prod32.truncate 16 := by
    apply BitVec.eq_of_toNat_eq
    have h1 := toInt_emod_65536 (a * b)
    have h2 := toInt_mul_emod_65536 a b
    have hdec := prod32_low_high_toInt prod32
    have hlo_lt := (prod32.truncate 16).isLt
    rw [hp_int] at hdec
    omega
  have hhigh : (sqdmulh16 a b).sshiftRight 1 = (prod32 >>> 16).truncate 16 := by
    apply BitVec.eq_of_toInt_eq
    rw [toInt_sshiftRight_16 _ 1 (by omega), sqdmulh16_toInt (fun h => hne h.2)]
    have hdec := prod32_low_high_toInt prod32
    have hlo_lt := (prod32.truncate 16).isLt
    rw [hp_int] at hdec; omega
  have heq : neonMontgomeryMul16 a b =
      neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16) := by
    unfold neonMontgomeryMul16; rw [hlow, hhigh]
  have hred := neonMontgomeryReduce16_prod32 prod32 (B := 16769025)
    (by rw [hp_int]; omega) (by rw [hp_int]; omega) (by omega)
  rw [← heq] at hred
  exact ⟨hmod, by have := hred.2.1; omega, by have := hred.2.2; omega⟩

/-- Table lookup bridge: `zetasTimesMontgomeryR.getD (64 + p / 2) 0#16 = zetaTableAt (64 + p / 2)`. -/
theorem nttMul_zeta_eq_zetaTableAt {p : Nat} (hp : p < 128) :
    zetasTimesMontgomeryR.getD (64 + p / 2) 0#16 = zetaTableAt (64 + p / 2) :=
  (zetaTableAt_eq_zetasTimesMontgomeryR (by omega)).symm

private theorem nat_mul_mod_cast (u v g : Nat) :
    (((((u : Int) % 3329) * ((v : Int) % 3329)) % 3329) * ((g : Int) % 3329)) % 3329 =
      ((((u * v) % mlkemQ) * g : Nat) : Int) % 3329 := by
  rw [← Int.mul_emod (u : Int) (v : Int) 3329, ← Int.mul_emod]
  simp only [mlkemQ, Int.natCast_mul, Int.natCast_emod, Nat.cast_ofNat]
  conv => rhs; rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

/-- Main soundness and range theorem for `Spec.neonPolyNttMul16`:
    for inputs bounded by `4095` representing `f` and `g` mod `3329`, `neonPolyNttMul16 lhs rhs`
    is bounded by `2176` (`≤ 3328`) and represents `Spec.polyNttMul f g` in the `R⁻¹` domain. -/
theorem neonPolyNttMul16_spec {lhs rhs : Poly16} {f g : Poly}
    (hlhs_b : PolyBounded16 4095 lhs) (hrhs_b : PolyBounded16 4095 rhs)
    (hlhs_r : PolyRepresents lhs f) (hrhs_r : PolyRepresents rhs g) :
    PolyBounded16 2176 (neonPolyNttMul16 lhs rhs) ∧
    PolyRepresentsMontInv (neonPolyNttMul16 lhs rhs) (polyNttMul f g) := by
  have hsize : (neonPolyNttMul16 lhs rhs).size = 256 := by simp [neonPolyNttMul16]
  suffices hlane : ∀ idx < 256,
      let out := (neonPolyNttMul16 lhs rhs).getD idx 0#16
      (-2176 ≤ out.toInt ∧ out.toInt ≤ 2176) ∧
      (out.toInt * 65536) % 3329 = (((polyNttMul f g).getD idx 0 : Nat) : Int) % 3329 by
    refine ⟨⟨hsize, fun i hi => (hlane i hi).1⟩, ⟨hsize, fun i hi => (hlane i hi).2⟩⟩
  intro idx hidx
  dsimp only
  rw [neonPolyNttMul16, getD_ofFn_256 _ _ _ hidx, polyNttMul, getD_ofFn_256 _ _ _ hidx]
  dsimp only
  let p := idx / 2
  have hp0 : 2 * p < 256 := by omega
  have hp1 : 2 * p + 1 < 256 := by omega
  have hzk : 64 + p / 2 < 128 := by omega
  let a0 := lhs.getD (2 * p) 0#16
  let a1 := lhs.getD (2 * p + 1) 0#16
  let b0 := rhs.getD (2 * p) 0#16
  let b1 := rhs.getD (2 * p + 1) 0#16
  have ha0 := hlhs_b.2 (2 * p) hp0
  have ha1 := hlhs_b.2 (2 * p + 1) hp1
  have hb0 := hrhs_b.2 (2 * p) hp0
  have hb1 := hrhs_b.2 (2 * p + 1) hp1
  have hra0 := hlhs_r.2 (2 * p) hp0
  have hra1 := hlhs_r.2 (2 * p + 1) hp1
  have hrb0 := hrhs_r.2 (2 * p) hp0
  have hrb1 := hrhs_r.2 (2 * p + 1) hp1
  by_cases heven : idx % 2 == 0
  · simp only [heven, ↓reduceIte]
    let baseZ := zetasTimesMontgomeryR.getD (64 + p / 2) 0#16
    let z : BitVec 16 := if p % 2 == 0 then baseZ else -baseZ
    let baseZeta := fipsZetas.getD (64 + p / 2) 0
    let gamma : Nat := if p % 2 == 0 then baseZeta else (mlkemQ - baseZeta) % mlkemQ
    have hz_bounds : -1664 ≤ z.toInt ∧ z.toInt ≤ 1664 := by
      have hzb := zetasTimesMontgomeryR_bounds hzk
      have hzn := zetasTimesMontgomeryR_neg_toInt hzk
      dsimp [z, baseZ]
      cases p % 2 == 0 <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    have hz_mod : z.toInt % 3329 = ((gamma : Int) * 65536) % 3329 := by
      dsimp [z, baseZ, gamma, baseZeta]
      by_cases hp_even : p % 2 == 0
      · simp only [hp_even, ↓reduceIte]; exact zetasTimesMontgomeryR_mod_3329 hzk
      · simp only [hp_even, Bool.false_eq_true, ↓reduceIte]
        exact zetasTimesMontgomeryR_neg_mod_3329 hzk
    obtain ⟨hm_a1b1, hlo_a1b1, hhi_a1b1⟩ :=
      neonMontgomeryMul16_bounded_4095 ha1.1 ha1.2 hb1.1 hb1.2
    let a1b1 := neonMontgomeryMul16 a1 b1
    change -1920 ≤ a1b1.toInt at hlo_a1b1
    change a1b1.toInt ≤ 1920 at hhi_a1b1
    change (a1b1.toInt * 65536) % 3329 = (a1.toInt * b1.toInt) % 3329 at hm_a1b1
    change -4095 ≤ a0.toInt ∧ a0.toInt ≤ 4095 at ha0
    change -4095 ≤ b0.toInt ∧ b0.toInt ≤ 4095 at hb0
    let prod32 : BitVec 32 :=
      a1b1.signExtend 32 * z.signExtend 32 + a0.signExtend 32 * b0.signExtend 32
    have ht1_b := abs_mul_le hlo_a1b1 hhi_a1b1 hz_bounds.1 hz_bounds.2 (by omega) (by omega)
    have ht2_b := abs_mul_le ha0.1 ha0.2 hb0.1 hb0.2 (by omega) (by omega)
    have hprod32_int : prod32.toInt = a1b1.toInt * z.toInt + a0.toInt * b0.toInt := by
      dsimp [prod32]
      have hm1 : (a1b1.signExtend 32 * z.signExtend 32).toInt = a1b1.toInt * z.toInt := by
        rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
          BitVec.toInt_signExtend_of_le (by omega), Int.bmod_eq_of_le] <;> omega
      have hm2 : (a0.signExtend 32 * b0.signExtend 32).toInt = a0.toInt * b0.toInt := by
        rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
          BitVec.toInt_signExtend_of_le (by omega), Int.bmod_eq_of_le] <;> omega
      rw [BitVec.toInt_add, hm1, hm2, Int.bmod_eq_of_le] <;> omega
    have hred := neonMontgomeryReduce16_prod32 prod32 (B := 19963905)
      (by rw [hprod32_int]; omega) (by rw [hprod32_int]; omega) (by omega)
    have hred_b : -1969 ≤ (neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)).toInt ∧
        (neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)).toInt ≤ 1969 := hred.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change -2176 ≤ (neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)).toInt
      omega
    · change (neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)).toInt ≤ 2176
      omega
    change ((neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)).toInt *
      65536) % 3329 = _
    rw [hred.1, hprod32_int]
    have hterm1 : (a1b1.toInt * z.toInt) % 3329 =
        ((((f.getD (2 * p + 1) 0 * g.getD (2 * p + 1) 0) % mlkemQ) * gamma : Nat) : Int) % 3329 := by
      calc (a1b1.toInt * z.toInt) % 3329
          = ((a1b1.toInt % 3329) * (z.toInt % 3329)) % 3329 := Int.mul_emod _ _ _
        _ = ((a1b1.toInt % 3329) * (((gamma : Int) * 65536) % 3329)) % 3329 := by rw [hz_mod]
        _ = (a1b1.toInt * ((gamma : Int) * 65536)) % 3329 := (Int.mul_emod _ _ _).symm
        _ = ((a1b1.toInt * 65536) * (gamma : Int)) % 3329 := by
            apply congrArg (· % 3329); rw [← Int.mul_assoc, Int.mul_right_comm]
        _ = (((a1b1.toInt * 65536) % 3329) * ((gamma : Int) % 3329)) % 3329 := Int.mul_emod _ _ _
        _ = (((a1.toInt * b1.toInt) % 3329) * ((gamma : Int) % 3329)) % 3329 := by rw [hm_a1b1]
        _ = ((((a1.toInt % 3329) * (b1.toInt % 3329)) % 3329) * ((gamma : Int) % 3329)) % 3329 := by
            rw [← Int.mul_emod a1.toInt b1.toInt]
        _ = (((((f.getD (2 * p + 1) 0 : Int) % 3329) *
              ((g.getD (2 * p + 1) 0 : Int) % 3329)) % 3329) * ((gamma : Int) % 3329)) % 3329 := by
            change a1.toInt % 3329 = _ at hra1
            change b1.toInt % 3329 = _ at hrb1
            rw [hra1, hrb1]
        _ = ((((f.getD (2 * p + 1) 0 * g.getD (2 * p + 1) 0) % mlkemQ) * gamma : Nat) : Int) % 3329 :=
            nat_mul_mod_cast (f.getD (2 * p + 1) 0) (g.getD (2 * p + 1) 0) gamma
    have hterm2 : (a0.toInt * b0.toInt) % 3329 =
        ((f.getD (2 * p) 0 : Int) * (g.getD (2 * p) 0 : Int)) % 3329 := by
      change a0.toInt % 3329 = _ at hra0
      change b0.toInt % 3329 = _ at hrb0
      rw [Int.mul_emod, hra0, hrb0, ← Int.mul_emod]
    rw [Int.add_emod, hterm1, hterm2, ← Int.add_emod]
    dsimp [mlkemQ, p, gamma, baseZeta]
    rw [Int.emod_emod, Int.add_comm]
  · simp only [heven, Bool.false_eq_true, ↓reduceIte]
    change -4095 ≤ a0.toInt ∧ a0.toInt ≤ 4095 at ha0
    change -4095 ≤ a1.toInt ∧ a1.toInt ≤ 4095 at ha1
    change -4095 ≤ b0.toInt ∧ b0.toInt ≤ 4095 at hb0
    change -4095 ≤ b1.toInt ∧ b1.toInt ≤ 4095 at hb1
    change a0.toInt % 3329 = _ at hra0
    change a1.toInt % 3329 = _ at hra1
    change b0.toInt % 3329 = _ at hrb0
    change b1.toInt % 3329 = _ at hrb1
    let prod32 : BitVec 32 :=
      a0.signExtend 32 * b1.signExtend 32 + a1.signExtend 32 * b0.signExtend 32
    have ht1_b := abs_mul_le ha0.1 ha0.2 hb1.1 hb1.2 (by omega) (by omega)
    have ht2_b := abs_mul_le ha1.1 ha1.2 hb0.1 hb0.2 (by omega) (by omega)
    have hprod32_int : prod32.toInt = a0.toInt * b1.toInt + a1.toInt * b0.toInt := by
      dsimp [prod32]
      have hm1 : (a0.signExtend 32 * b1.signExtend 32).toInt = a0.toInt * b1.toInt := by
        rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
          BitVec.toInt_signExtend_of_le (by omega), Int.bmod_eq_of_le] <;> omega
      have hm2 : (a1.signExtend 32 * b0.signExtend 32).toInt = a1.toInt * b0.toInt := by
        rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
          BitVec.toInt_signExtend_of_le (by omega), Int.bmod_eq_of_le] <;> omega
      rw [BitVec.toInt_add, hm1, hm2, Int.bmod_eq_of_le] <;> omega
    have hred := neonMontgomeryReduce16_prod32 prod32 (B := 33538050)
      (by rw [hprod32_int]; omega) (by rw [hprod32_int]; omega) (by omega)
    have hred_b : -2176 ≤ (neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)).toInt ∧
        (neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)).toInt ≤ 2176 := hred.2
    refine ⟨hred_b, ?_⟩
    change ((neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)).toInt *
      65536) % 3329 = _
    have ht1_mod : (a0.toInt * b1.toInt) % 3329 =
        ((f.getD (2 * p) 0 : Int) * (g.getD (2 * p + 1) 0 : Int)) % 3329 := by
      rw [Int.mul_emod, hra0, hrb1, ← Int.mul_emod]
    have ht2_mod : (a1.toInt * b0.toInt) % 3329 =
        ((f.getD (2 * p + 1) 0 : Int) * (g.getD (2 * p) 0 : Int)) % 3329 := by
      rw [Int.mul_emod, hra1, hrb0, ← Int.mul_emod]
    rw [hred.1, hprod32_int, Int.add_emod, ht1_mod, ht2_mod, ← Int.add_emod]
    dsimp [mlkemQ, p]
    rw [Int.emod_emod]

/-! ## 3. `to_standard_domain` (`1353#16`) & `K`-Way NTT Dot Product (`vecDotNtt`) -/

private theorem getD_map_16 (arr : Array (BitVec 16)) (g : BitVec 16 → BitVec 16)
    (i : Nat) (hi : i < arr.size) :
    (arr.map g).getD i 0#16 = g (arr.getD i 0#16) := by
  simp [Array.getD, hi]

/-- `to_standard_domain` converts any `R⁻¹`-domain `Poly16` into standard domain with bound `2496`. -/
theorem polyToStandardDomain_spec {p : Poly16} {f : Poly} (hr : PolyRepresentsMontInv p f) :
    let out := p.map fun v => neonMontgomeryMul16 v 1353#16
    PolyBounded16 2496 out ∧ PolyRepresents out f := by
  dsimp only
  have hsize_p : p.size = 256 := hr.1
  have hsize : (p.map fun v => neonMontgomeryMul16 v 1353#16).size = 256 := by simp [hsize_p]
  refine ⟨⟨hsize, ?_⟩, ⟨hsize, ?_⟩⟩
  · intro i hi
    have hip : i < p.size := by omega
    rw [getD_map_16 p _ i hip]
    obtain ⟨_, hlo, hhi⟩ := neonMontgomeryMul16_1353 (p.getD i 0#16)
    exact ⟨hlo, hhi⟩
  · intro i hi
    have hip : i < p.size := by omega
    have hri := hr.2 i hi
    rw [getD_map_16 p _ i hip]
    obtain ⟨hm, _, _⟩ := neonMontgomeryMul16_1353 (p.getD i 0#16)
    rw [hm, hri]

/-- Lane-wise `Poly16` addition. -/
@[expose] def polyAdd16 (a b : Poly16) : Poly16 :=
  Array.ofFn (n := 256) fun k => a.getD k.val 0#16 + b.getD k.val 0#16

/-- Lane-wise `Poly16` addition preserves standard-domain `PolyRepresents` and adds bounds when `A + B < 32768`. -/
theorem polyAdd16_spec {a b : Poly16} {fa fb : Poly} {A B : Int}
    (ha_b : PolyBounded16 A a) (hb_b : PolyBounded16 B b) (hsum : A + B < 32768)
    (ha_r : PolyRepresents a fa) (hb_r : PolyRepresents b fb) :
    PolyBounded16 (A + B) (polyAdd16 a b) ∧ PolyRepresents (polyAdd16 a b) (polyAdd fa fb) := by
  have hsize : (polyAdd16 a b).size = 256 := by simp [polyAdd16]
  refine ⟨⟨hsize, ?_⟩, ⟨hsize, ?_⟩⟩
  · intro i hi
    rw [polyAdd16, getD_ofFn_256 _ _ _ hi]
    dsimp only
    have ha := ha_b.2 i hi; have hb := hb_b.2 i hi
    rw [toInt_add_of_bounds (by omega) (by omega)]
    omega
  · intro i hi
    rw [polyAdd16, getD_ofFn_256 _ _ _ hi, polyAdd, getD_ofFn_256 _ _ _ hi]
    dsimp only
    have ha := ha_b.2 i hi; have hb := hb_b.2 i hi
    have hra := ha_r.2 i hi; have hrb := hb_r.2 i hi
    rw [toInt_add_of_bounds (by omega) (by omega), Int.add_emod, hra, hrb, ← Int.add_emod]
    dsimp [mlkemQ]
    rw [Int.emod_emod]

/-- Lane-wise `Poly16` addition preserves `R⁻¹`-domain representation and adds bounds when `A + B < 32768`. -/
theorem polyAdd16_montInv_spec {a b : Poly16} {fa fb : Poly} {A B : Int}
    (ha_b : PolyBounded16 A a) (hb_b : PolyBounded16 B b) (hsum : A + B < 32768)
    (ha_r : PolyRepresentsMontInv a fa) (hb_r : PolyRepresentsMontInv b fb) :
    PolyBounded16 (A + B) (polyAdd16 a b) ∧ PolyRepresentsMontInv (polyAdd16 a b) (polyAdd fa fb) := by
  have hsize : (polyAdd16 a b).size = 256 := by simp [polyAdd16]
  refine ⟨⟨hsize, ?_⟩, ⟨hsize, ?_⟩⟩
  · intro i hi
    rw [polyAdd16, getD_ofFn_256 _ _ _ hi]
    dsimp only
    have ha := ha_b.2 i hi; have hb := hb_b.2 i hi
    rw [toInt_add_of_bounds (by omega) (by omega)]
    omega
  · intro i hi
    rw [polyAdd16, getD_ofFn_256 _ _ _ hi, polyAdd, getD_ofFn_256 _ _ _ hi]
    dsimp only
    have ha := ha_b.2 i hi; have hb := hb_b.2 i hi
    have hra := ha_r.2 i hi; have hrb := hb_r.2 i hi
    rw [toInt_add_of_bounds (by omega) (by omega)]
    have hmul : ((a.getD i 0#16).toInt + (b.getD i 0#16).toInt) * 65536 =
        (a.getD i 0#16).toInt * 65536 + (b.getD i 0#16).toInt * 65536 := Int.add_mul _ _ _
    rw [hmul, Int.add_emod, hra, hrb, ← Int.add_emod]
    dsimp [mlkemQ]
    rw [Int.emod_emod]

/-- Rank-3 (`ML-KEM-768`) NTT dot product of `≤ 4095`-bounded `Poly16`s has bound `≤ 6528 < 32768`
    and represents `Spec.vecDotNtt 3 fVec gVec` in the `R⁻¹` domain. -/
theorem neonVecDotNtt3_spec {a0 a1 a2 b0 b1 b2 : Poly16} {fa fb : Array Poly}
    (ha0_b : PolyBounded16 4095 a0) (ha1_b : PolyBounded16 4095 a1) (ha2_b : PolyBounded16 4095 a2)
    (hb0_b : PolyBounded16 4095 b0) (hb1_b : PolyBounded16 4095 b1) (hb2_b : PolyBounded16 4095 b2)
    (ha0_r : PolyRepresents a0 (fa.getD 0 zeroPoly))
    (ha1_r : PolyRepresents a1 (fa.getD 1 zeroPoly))
    (ha2_r : PolyRepresents a2 (fa.getD 2 zeroPoly))
    (hb0_r : PolyRepresents b0 (fb.getD 0 zeroPoly))
    (hb1_r : PolyRepresents b1 (fb.getD 1 zeroPoly))
    (hb2_r : PolyRepresents b2 (fb.getD 2 zeroPoly)) :
    let m0 := neonPolyNttMul16 a0 b0
    let m1 := neonPolyNttMul16 a1 b1
    let m2 := neonPolyNttMul16 a2 b2
    let s01 := polyAdd16 m0 m1
    let dot := polyAdd16 s01 m2
    PolyBounded16 6528 dot ∧ PolyRepresentsMontInv dot (vecDotNtt 3 fa fb) := by
  dsimp only
  obtain ⟨hm0_b, hm0_r⟩ := neonPolyNttMul16_spec ha0_b hb0_b ha0_r hb0_r
  obtain ⟨hm1_b, hm1_r⟩ := neonPolyNttMul16_spec ha1_b hb1_b ha1_r hb1_r
  obtain ⟨hm2_b, hm2_r⟩ := neonPolyNttMul16_spec ha2_b hb2_b ha2_r hb2_r
  obtain ⟨hs01_b, hs01_r⟩ := polyAdd16_montInv_spec hm0_b hm1_b (by omega) hm0_r hm1_r
  obtain ⟨hdot_b, hdot_r⟩ := polyAdd16_montInv_spec hs01_b hm2_b (by omega) hs01_r hm2_r
  refine ⟨⟨hdot_b.1, fun i hi => by have := hdot_b.2 i hi; omega⟩, ⟨hdot_r.1, fun i hi => ?_⟩⟩
  rw [hdot_r.2 i hi]
  unfold vecDotNtt
  have hrange : List.range 3 = [0, 1, 2] := rfl
  rw [hrange, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  have hzero : zeroPoly.getD i 0 = 0 := by simp [zeroPoly, Array.getD, hi]
  have hpA : ∀ x y : Poly, (polyAdd x y).getD i 0 = (x.getD i 0 + y.getD i 0) % mlkemQ := by
    intro x y; rw [polyAdd, getD_ofFn_256 _ _ _ hi]
  have heq_nat :
      (polyAdd (polyAdd (polyNttMul (fa.getD 0 zeroPoly) (fb.getD 0 zeroPoly))
          (polyNttMul (fa.getD 1 zeroPoly) (fb.getD 1 zeroPoly)))
        (polyNttMul (fa.getD 2 zeroPoly) (fb.getD 2 zeroPoly))).getD i 0 =
      (polyAdd (polyAdd (polyAdd zeroPoly (polyNttMul (fa.getD 0 zeroPoly) (fb.getD 0 zeroPoly)))
          (polyNttMul (fa.getD 1 zeroPoly) (fb.getD 1 zeroPoly)))
        (polyNttMul (fa.getD 2 zeroPoly) (fb.getD 2 zeroPoly))).getD i 0 := by
    rw [hpA, hpA, hpA, hpA, hpA, hzero, Nat.zero_add]
    dsimp [mlkemQ]
    omega
  rw [heq_nat]

/-- Rank-4 (`Kyber-1024`) NTT dot product of `≤ 4095`-bounded `Poly16`s has bound `≤ 8704 < 32768`
    and represents `Spec.vecDotNtt 4 fa fb` in the `R⁻¹` domain. -/
theorem neonVecDotNtt4_spec {a0 a1 a2 a3 b0 b1 b2 b3 : Poly16} {fa fb : Array Poly}
    (ha0_b : PolyBounded16 4095 a0) (ha1_b : PolyBounded16 4095 a1)
    (ha2_b : PolyBounded16 4095 a2) (ha3_b : PolyBounded16 4095 a3)
    (hb0_b : PolyBounded16 4095 b0) (hb1_b : PolyBounded16 4095 b1)
    (hb2_b : PolyBounded16 4095 b2) (hb3_b : PolyBounded16 4095 b3)
    (ha0_r : PolyRepresents a0 (fa.getD 0 zeroPoly))
    (ha1_r : PolyRepresents a1 (fa.getD 1 zeroPoly))
    (ha2_r : PolyRepresents a2 (fa.getD 2 zeroPoly))
    (ha3_r : PolyRepresents a3 (fa.getD 3 zeroPoly))
    (hb0_r : PolyRepresents b0 (fb.getD 0 zeroPoly))
    (hb1_r : PolyRepresents b1 (fb.getD 1 zeroPoly))
    (hb2_r : PolyRepresents b2 (fb.getD 2 zeroPoly))
    (hb3_r : PolyRepresents b3 (fb.getD 3 zeroPoly)) :
    let m0 := neonPolyNttMul16 a0 b0
    let m1 := neonPolyNttMul16 a1 b1
    let m2 := neonPolyNttMul16 a2 b2
    let m3 := neonPolyNttMul16 a3 b3
    let s01 := polyAdd16 m0 m1
    let s012 := polyAdd16 s01 m2
    let dot := polyAdd16 s012 m3
    PolyBounded16 8704 dot ∧ PolyRepresentsMontInv dot (vecDotNtt 4 fa fb) := by
  dsimp only
  obtain ⟨hs012_b, hs012_r⟩ :=
    neonVecDotNtt3_spec ha0_b ha1_b ha2_b hb0_b hb1_b hb2_b ha0_r ha1_r ha2_r hb0_r hb1_r hb2_r
  obtain ⟨hm3_b, hm3_r⟩ := neonPolyNttMul16_spec ha3_b hb3_b ha3_r hb3_r
  obtain ⟨hdot_b, hdot_r⟩ := polyAdd16_montInv_spec hs012_b hm3_b (by omega) hs012_r hm3_r
  refine ⟨⟨hdot_b.1, fun i hi => by have := hdot_b.2 i hi; omega⟩, ⟨hdot_r.1, fun i hi => ?_⟩⟩
  rw [hdot_r.2 i hi]
  unfold vecDotNtt
  have hrange : List.range 4 = List.range 3 ++ [3] := rfl
  rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_nil]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul

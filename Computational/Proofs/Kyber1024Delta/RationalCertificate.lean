/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Kyber1024Delta.Common -- proof-setup: allow-public-import
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact-Rational W2 Chernoff Certificate (`Kyber1024Delta.RationalCertificate`)

Exact rational MGF definitions (`λ = 5/4`), residue-wise upper bounds across all `3329` elements of
`ZMod 3329`, and the headline W2 Chernoff numerical certificate `< 2^-112` for Kyber-1024.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.Kyber1024Delta.RationalCertificate

open CryptoGames.MLKEM (
  compressCoeff
  decompressCoeff
  mlkemQ
)
open Computational.Proofs.Kyber1024Delta.Common (
  cbd2Support
  cbd2WeightQ
  centeredZMod
  centeredZMod_cast_eq
  centeredZMod_of_int_bounds
  compressErrZMod
)

/-- Rational Chernoff base `λ = 5 / 4` for the W2 Kyber-1024 certificate. -/
@[expose] def lamW2 : Rat := 5 / 4

/-- Rational MGF `E_{x ← CBD_2}[λ^{t x}]` of `CBD_2` at base `lamW2 = 5 / 4`. -/
@[expose] def cbd2Mgf (t : Int) : Rat :=
  (cbd2Support.map fun x => cbd2WeightQ x * lamW2 ^ (t * x)).sum

/-- Exact expected product `E_{x, y ← CBD_2}[λ^{x y}]`. -/
@[expose] def termA : Rat :=
  (cbd2Support.map fun x => cbd2WeightQ x * cbd2Mgf x).sum

/-- Residue-conditioned `d = 11` ciphertext term `E_{e ← CBD_2}[cbd2Mgf(e + compressErr_11(w + e))]`. -/
@[expose] def termGAt (w : ZMod mlkemQ) : Rat :=
  (cbd2Support.map fun e =>
    cbd2WeightQ e * cbd2Mgf (e + compressErrZMod 11 (w + (e : ZMod mlkemQ)))).sum

/-- Residue-conditioned `d = 5` ciphertext term `E_{e ← CBD_2}[λ^{σ · centered(Decompress_5(Compress_5(v0 + e)) - v0)}]`. -/
@[expose] def termHAt (v0 : ZMod mlkemQ) (σ : Int) : Rat :=
  (cbd2Support.map fun e =>
    cbd2WeightQ e *
      lamW2 ^ (σ * centeredZMod
        ((decompressCoeff 5 (compressCoeff 5 (v0 + (e : ZMod mlkemQ)).val) : ZMod mlkemQ) - v0))).sum

/-- Exact closed-form constant for `termA`. -/
@[expose] def constA : Rat := 21003361 / 20480000

/-- Exact uniform upper bound across `ZMod 3329` for `termGAt`. -/
@[expose] def constG : Rat := 4361761 / 4096000

/-- Clean rational upper bound (`⌈H⌉ = 82108`, vs. `H ≈ 82107.331894`) across `ZMod 3329` for `termHAt`. -/
@[expose] def constH : Rat := 82108

theorem lamW2_pos : (0 : Rat) < lamW2 := by
  unfold lamW2
  norm_num

theorem cbd2WeightQ_nonneg (k : Int) : 0 ≤ cbd2WeightQ k := by
  unfold cbd2WeightQ
  split_ifs <;> norm_num

theorem cbd2Mgf_nonneg (t : Int) : 0 ≤ cbd2Mgf t := by
  simp only [cbd2Mgf, cbd2Support, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h0 : 0 ≤ lamW2 := le_of_lt lamW2_pos
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) ?_
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) ?_
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) ?_
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) ?_
  exact add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) le_rfl

theorem termA_eq : termA = constA := by
  simp only [termA, cbd2Mgf, cbd2Support, cbd2WeightQ, lamW2, constA,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

theorem termGAt_nonneg (w : ZMod mlkemQ) : 0 ≤ termGAt w := by
  simp only [termGAt, cbd2Support, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (cbd2Mgf_nonneg _)) ?_
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (cbd2Mgf_nonneg _)) ?_
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (cbd2Mgf_nonneg _)) ?_
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (cbd2Mgf_nonneg _)) ?_
  exact add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (cbd2Mgf_nonneg _)) le_rfl

theorem termHAt_nonneg (v0 : ZMod mlkemQ) (σ : Int) : 0 ≤ termHAt v0 σ := by
  simp only [termHAt, cbd2Support, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h0 : 0 ≤ lamW2 := le_of_lt lamW2_pos
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) ?_
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) ?_
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) ?_
  refine add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) ?_
  exact add_nonneg (mul_nonneg (cbd2WeightQ_nonneg _) (zpow_nonneg h0 _)) le_rfl

/-! ### Step-by-`1` Residue Helper in `ZMod 3329` -/

private theorem val_add_one (x : ZMod mlkemQ) :
    (x.val = 3328 ∧ (x + 1).val = 0) ∨ (x.val < 3328 ∧ (x + 1).val = x.val + 1) := by
  have hx : x.val < 3329 := ZMod.val_lt x
  by_cases h3328 : x.val = 3328
  · left
    refine ⟨h3328, ?_⟩
    have hxeq : x = (3328 : ZMod mlkemQ) := by
      rw [← ZMod.natCast_zmod_val x, h3328]
      rfl
    rw [hxeq]
    decide
  · right
    have hlt : x.val < 3328 := by omega
    refine ⟨hlt, ?_⟩
    have hcast : x + 1 = ((x.val + 1 : Nat) : ZMod mlkemQ) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hcast]
    exact ZMod.val_cast_of_lt (by dsimp [mlkemQ]; omega)

/-! ### Uniform Bound `termGAt w ≤ constG` -/

private def err11Int (u : Nat) : Int :=
  (((((u * 2048 + 1664) / 3329) * 3329 + 1024) / 2048 : Nat) : Int) - (u : Int)

private theorem err11Int_bounds (u : Nat) :
    -1 ≤ err11Int u ∧ err11Int u ≤ 1 := by
  unfold err11Int
  set q0 : Nat := (u * 2048 + 1664) / 3329
  set rem0 : Nat := (u * 2048 + 1664) % 3329
  have hdiv0 : 3329 * q0 + rem0 = u * 2048 + 1664 := Nat.div_add_mod _ 3329
  have hrem0 : rem0 < 3329 := Nat.mod_lt _ (by omega)
  clear_value q0 rem0
  set d0 : Nat := (q0 * 3329 + 1024) / 2048
  set rem1 : Nat := (q0 * 3329 + 1024) % 2048
  have hdiv1 : 2048 * d0 + rem1 = q0 * 3329 + 1024 := Nat.div_add_mod _ 2048
  have hrem1 : rem1 < 2048 := Nat.mod_lt _ (by omega)
  clear_value d0 rem1
  omega

private theorem compressErrZMod_11_eq (x : ZMod mlkemQ) :
    compressErrZMod 11 x = err11Int x.val := by
  have hu : x.val < 3329 := ZMod.val_lt x
  have hdec : decompressCoeff 11 (compressCoeff 11 x.val) =
      (((x.val * 2048 + 1664) / 3329) * 3329 + 1024) / 2048 := by
    unfold decompressCoeff compressCoeff mlkemQ
    have h0 : (11 == 0) = false := rfl
    rw [h0]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mod_eq_of_lt hu,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, one_mul]
    have hp11 : (2 : Nat) ^ 11 = 2048 := rfl
    have hp10 : (2 : Nat) ^ (11 - 1) = 1024 := rfl
    rw [hp11, hp10]
    have hq_lt : (x.val * 2048 + 1664) / 3329 < 2048 := by omega
    rw [Nat.mod_eq_of_lt hq_lt]
  unfold compressErrZMod
  rw [hdec]
  have hb := err11Int_bounds x.val
  have hcast :
      ((((((x.val * 2048 + 1664) / 3329) * 3329 + 1024) / 2048 : Nat) : ZMod mlkemQ) - x) =
        (err11Int x.val : ZMod mlkemQ) := by
    unfold err11Int
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hcast]
  exact centeredZMod_of_int_bounds (by omega) (by omega)

private theorem nat_div_eq {a b k : Nat} (hb : 0 < b) (hlo : k * b ≤ a) (hhi : a < (k + 1) * b) :
    a / b = k :=
  le_antisymm
    (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hb).mpr hhi))
    ((Nat.le_div_iff_mul_le hb).mpr hlo)

private theorem err11Int_adj (u : Nat) :
    err11Int u = 0 ∨ err11Int (u + 1) = 0 := by
  unfold err11Int
  set q0 : Nat := (u * 2048 + 1664) / 3329
  set rem : Nat := (u * 2048 + 1664) % 3329
  have hdiv : 3329 * q0 + rem = u * 2048 + 1664 := Nat.div_add_mod (u * 2048 + 1664) 3329
  have hrem : rem < 3329 := Nat.mod_lt _ (by omega)
  clear_value q0 rem
  have hq1 : ((u + 1) * 2048 + 1664) / 3329 = q0 + (rem + 2048) / 3329 := by
    have heq : (u + 1) * 2048 + 1664 = (rem + 2048) + q0 * 3329 := by omega
    rw [heq, Nat.add_mul_div_right _ _ (by omega), Nat.add_comm]
  rw [hq1]
  by_cases hwrap : rem + 2048 < 3329
  · have hq1_0 : (rem + 2048) / 3329 = 0 := Nat.div_eq_of_lt hwrap
    rw [hq1_0]
    simp only [Nat.add_zero]
    by_cases h640 : rem ≤ 640
    · right
      have hd : (q0 * 3329 + 1024) / 2048 = u + 1 :=
        nat_div_eq (by omega) (by omega) (by omega)
      rw [hd]; exact sub_self _
    · left
      have hd : (q0 * 3329 + 1024) / 2048 = u :=
        nat_div_eq (by omega) (by omega) (by omega)
      rw [hd]; exact sub_self _
  · have hq1_1 : (rem + 2048) / 3329 = 1 :=
      nat_div_eq (by omega) (by omega) (by omega)
    rw [hq1_1]
    by_cases h2688 : rem ≤ 2688
    · left
      have hd : (q0 * 3329 + 1024) / 2048 = u :=
        nat_div_eq (by omega) (by omega) (by omega)
      rw [hd]; exact sub_self _
    · right
      have hd : ((q0 + 1) * 3329 + 1024) / 2048 = u + 1 :=
        nat_div_eq (by omega) (by omega) (by omega)
      rw [hd]; exact sub_self _

private theorem compressErrZMod_11_adj (x : ZMod mlkemQ) :
    compressErrZMod 11 x = 0 ∨ compressErrZMod 11 (x + 1) = 0 := by
  rw [compressErrZMod_11_eq x, compressErrZMod_11_eq (x + 1)]
  rcases val_add_one x with ⟨_, h0⟩ | ⟨_, hsucc⟩
  · right
    rw [h0]
    unfold err11Int
    omega
  · rw [hsucc]
    exact err11Int_adj x.val

private def mgfScaled (t : Int) : Int :=
  if t = 0 then 1024000000
  else if t = 1 ∨ t = -1 then 1049760000
  else if t = 2 ∨ t = -2 then 1130304400
  else 1275989841

private theorem cbd2Mgf_eq_scaled {t : Int} (hlo : -3 ≤ t) (hhi : t ≤ 3) :
    cbd2Mgf t = (mgfScaled t : Rat) / 1024000000 := by
  have ht : t = -3 ∨ t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [cbd2Mgf, cbd2Support, cbd2WeightQ, lamW2, mgfScaled,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; norm_num)

private theorem mgfScaled_le_max {t : Int} (hlo : -3 ≤ t) (hhi : t ≤ 3) :
    mgfScaled t ≤ 1275989841 := by
  have ht : t = -3 ∨ t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold mgfScaled; decide)

private theorem g_pair_left_le {a0 a1 : Int}
    (hb0 : -1 ≤ a0 ∧ a0 ≤ 1) (hb1 : -1 ≤ a1 ∧ a1 ≤ 1) (h01 : a0 = 0 ∨ a1 = 0) :
    1 * mgfScaled (-2 + a0) + 4 * mgfScaled (-1 + a1) ≤ 5651522000 := by
  rcases h01 with rfl | rfl
  · have h1 : a1 = -1 ∨ a1 = 0 ∨ a1 = 1 := by omega
    rcases h1 with rfl | rfl | rfl <;> (unfold mgfScaled; decide)
  · have h0 : a0 = -1 ∨ a0 = 0 ∨ a0 = 1 := by omega
    rcases h0 with rfl | rfl | rfl <;> (unfold mgfScaled; decide)

private theorem g_pair_right_le {a3 a4 : Int}
    (hb3 : -1 ≤ a3 ∧ a3 ≤ 1) (hb4 : -1 ≤ a4 ∧ a4 ≤ 1) (h34 : a3 = 0 ∨ a4 = 0) :
    4 * mgfScaled (1 + a3) + 1 * mgfScaled (2 + a4) ≤ 5651522000 := by
  rcases h34 with rfl | rfl
  · have h4 : a4 = -1 ∨ a4 = 0 ∨ a4 = 1 := by omega
    rcases h4 with rfl | rfl | rfl <;> (unfold mgfScaled; decide)
  · have h3 : a3 = -1 ∨ a3 = 0 ∨ a3 = 1 := by omega
    rcases h3 with rfl | rfl | rfl <;> (unfold mgfScaled; decide)

private theorem g_scaled_le_of_adj {a0 a1 a2 a3 a4 : Int}
    (hb0 : -1 ≤ a0 ∧ a0 ≤ 1) (hb1 : -1 ≤ a1 ∧ a1 ≤ 1) (hb2 : -1 ≤ a2 ∧ a2 ≤ 1)
    (hb3 : -1 ≤ a3 ∧ a3 ≤ 1) (hb4 : -1 ≤ a4 ∧ a4 ≤ 1)
    (h01 : a0 = 0 ∨ a1 = 0) (h12 : a1 = 0 ∨ a2 = 0)
    (h23 : a2 = 0 ∨ a3 = 0) (h34 : a3 = 0 ∨ a4 = 0) :
    1 * mgfScaled (-2 + a0) + 4 * mgfScaled (-1 + a1) + 6 * mgfScaled (0 + a2) +
      4 * mgfScaled (1 + a3) + 1 * mgfScaled (2 + a4) ≤ 17447044000 := by
  have ha2 : a2 = -1 ∨ a2 = 0 ∨ a2 = 1 := by omega
  rcases ha2 with rfl | rfl | rfl
  · have ha1 : a1 = 0 := by omega
    have ha3 : a3 = 0 := by omega
    subst ha1 ha3
    have hm0 := mgfScaled_le_max (t := -2 + a0) (by omega) (by omega)
    have hm4 := mgfScaled_le_max (t := 2 + a4) (by omega) (by omega)
    have hc1 : mgfScaled (-1 + 0) = 1049760000 := by unfold mgfScaled; decide
    have hc2 : mgfScaled (0 + -1) = 1049760000 := by unfold mgfScaled; decide
    have hc3 : mgfScaled (1 + 0) = 1049760000 := by unfold mgfScaled; decide
    omega
  · have hl := g_pair_left_le hb0 hb1 h01
    have hr := g_pair_right_le hb3 hb4 h34
    have hc2 : mgfScaled (0 + 0) = 1024000000 := by unfold mgfScaled; decide
    omega
  · have ha1 : a1 = 0 := by omega
    have ha3 : a3 = 0 := by omega
    subst ha1 ha3
    have hm0 := mgfScaled_le_max (t := -2 + a0) (by omega) (by omega)
    have hm4 := mgfScaled_le_max (t := 2 + a4) (by omega) (by omega)
    have hc1 : mgfScaled (-1 + 0) = 1049760000 := by unfold mgfScaled; decide
    have hc2 : mgfScaled (0 + 1) = 1049760000 := by unfold mgfScaled; decide
    have hc3 : mgfScaled (1 + 0) = 1049760000 := by unfold mgfScaled; decide
    omega

theorem termGAt_le_constG (w : ZMod mlkemQ) : termGAt w ≤ constG := by
  set x0 : ZMod mlkemQ := w + (-2 : Int)
  set x1 : ZMod mlkemQ := w + (-1 : Int)
  set x2 : ZMod mlkemQ := w + (0 : Int)
  set x3 : ZMod mlkemQ := w + (1 : Int)
  set x4 : ZMod mlkemQ := w + (2 : Int)
  have hx01 : x1 = x0 + 1 := by dsimp [x0, x1]; ring
  have hx12 : x2 = x1 + 1 := by dsimp [x1, x2]; ring
  have hx23 : x3 = x2 + 1 := by dsimp [x2, x3]; ring
  have hx34 : x4 = x3 + 1 := by dsimp [x3, x4]; ring
  set a0 : Int := compressErrZMod 11 x0
  set a1 : Int := compressErrZMod 11 x1
  set a2 : Int := compressErrZMod 11 x2
  set a3 : Int := compressErrZMod 11 x3
  set a4 : Int := compressErrZMod 11 x4
  have hb0 : -1 ≤ a0 ∧ a0 ≤ 1 := by dsimp [a0]; rw [compressErrZMod_11_eq]; exact err11Int_bounds _
  have hb1 : -1 ≤ a1 ∧ a1 ≤ 1 := by dsimp [a1]; rw [compressErrZMod_11_eq]; exact err11Int_bounds _
  have hb2 : -1 ≤ a2 ∧ a2 ≤ 1 := by dsimp [a2]; rw [compressErrZMod_11_eq]; exact err11Int_bounds _
  have hb3 : -1 ≤ a3 ∧ a3 ≤ 1 := by dsimp [a3]; rw [compressErrZMod_11_eq]; exact err11Int_bounds _
  have hb4 : -1 ≤ a4 ∧ a4 ≤ 1 := by dsimp [a4]; rw [compressErrZMod_11_eq]; exact err11Int_bounds _
  have hadj01 : a0 = 0 ∨ a1 = 0 := by dsimp [a0, a1]; rw [hx01]; exact compressErrZMod_11_adj x0
  have hadj12 : a1 = 0 ∨ a2 = 0 := by dsimp [a1, a2]; rw [hx12]; exact compressErrZMod_11_adj x1
  have hadj23 : a2 = 0 ∨ a3 = 0 := by dsimp [a2, a3]; rw [hx23]; exact compressErrZMod_11_adj x2
  have hadj34 : a3 = 0 ∨ a4 = 0 := by dsimp [a3, a4]; rw [hx34]; exact compressErrZMod_11_adj x3
  have hm0 := cbd2Mgf_eq_scaled (t := -2 + a0) (by omega) (by omega)
  have hm1 := cbd2Mgf_eq_scaled (t := -1 + a1) (by omega) (by omega)
  have hm2 := cbd2Mgf_eq_scaled (t := 0 + a2) (by omega) (by omega)
  have hm3 := cbd2Mgf_eq_scaled (t := 1 + a3) (by omega) (by omega)
  have hm4 := cbd2Mgf_eq_scaled (t := 2 + a4) (by omega) (by omega)
  have hsum_int := g_scaled_le_of_adj hb0 hb1 hb2 hb3 hb4 hadj01 hadj12 hadj23 hadj34
  have hsum_rat :
      (1 * mgfScaled (-2 + a0) + 4 * mgfScaled (-1 + a1) + 6 * mgfScaled (0 + a2) +
        4 * mgfScaled (1 + a3) + 1 * mgfScaled (2 + a4) : Rat) ≤ 17447044000 := by
    exact_mod_cast hsum_int
  simp only [termGAt, cbd2Support, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  change cbd2WeightQ (-2) * cbd2Mgf (-2 + a0) +
    (cbd2WeightQ (-1) * cbd2Mgf (-1 + a1) +
    (cbd2WeightQ 0 * cbd2Mgf (0 + a2) +
    (cbd2WeightQ 1 * cbd2Mgf (1 + a3) +
    (cbd2WeightQ 2 * cbd2Mgf (2 + a4) + 0)))) ≤ constG
  rw [hm0, hm1, hm2, hm3, hm4]
  have hw_m2 : cbd2WeightQ (-2) = 1 / 16 := by unfold cbd2WeightQ; norm_num
  have hw_m1 : cbd2WeightQ (-1) = 4 / 16 := by unfold cbd2WeightQ; norm_num
  have hw_0 : cbd2WeightQ 0 = 6 / 16 := by unfold cbd2WeightQ; norm_num
  have hw_p1 : cbd2WeightQ 1 = 4 / 16 := by unfold cbd2WeightQ; norm_num
  have hw_p2 : cbd2WeightQ 2 = 1 / 16 := by unfold cbd2WeightQ; norm_num
  rw [hw_m2, hw_m1, hw_0, hw_p1, hw_p2]
  unfold constG
  linarith

/-! ### Uniform Bound `termHAt v0 (±1) ≤ constH` -/

private def err5Int (u : Nat) : Int :=
  (((((u * 32 + 1664) / 3329) * 3329 + 16) / 32 : Nat) : Int) - (u : Int)

private theorem err5Int_bounds (u : Nat) :
    -52 ≤ err5Int u ∧ err5Int u ≤ 52 := by
  unfold err5Int
  set q0 : Nat := (u * 32 + 1664) / 3329
  set rem0 : Nat := (u * 32 + 1664) % 3329
  have hdiv0 : 3329 * q0 + rem0 = u * 32 + 1664 := Nat.div_add_mod _ 3329
  have hrem0 : rem0 < 3329 := Nat.mod_lt _ (by omega)
  clear_value q0 rem0
  set d0 : Nat := (q0 * 3329 + 16) / 32
  set rem1 : Nat := (q0 * 3329 + 16) % 32
  have hdiv1 : 32 * d0 + rem1 = q0 * 3329 + 16 := Nat.div_add_mod _ 32
  have hrem1 : rem1 < 32 := Nat.mod_lt _ (by omega)
  clear_value d0 rem1
  omega

private theorem compressErrZMod_5_eq (x : ZMod mlkemQ) :
    compressErrZMod 5 x = err5Int x.val := by
  have hu : x.val < 3329 := ZMod.val_lt x
  set q5 : Nat := (x.val * 32 + 1664) / 3329
  have hq_le : q5 ≤ 32 := by dsimp [q5]; omega
  have hdec_mod :
      (decompressCoeff 5 (compressCoeff 5 x.val) : ZMod mlkemQ) =
        (((q5 * 3329 + 16) / 32 : Nat) : ZMod mlkemQ) := by
    unfold decompressCoeff compressCoeff mlkemQ
    have h0 : (5 == 0) = false := rfl
    rw [h0]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mod_eq_of_lt hu,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, one_mul]
    have hp5 : (2 : Nat) ^ 5 = 32 := rfl
    have hp4 : (2 : Nat) ^ (5 - 1) = 16 := rfl
    rw [hp5, hp4]
    change (((q5 % 32 * 3329 + 16) / 32 : Nat) : ZMod 3329) = _
    by_cases hlt32 : q5 < 32
    · rw [Nat.mod_eq_of_lt hlt32]
    · have hq32 : q5 = 32 := by omega
      rw [hq32]
      have hlhs : (((32 % 32) * 3329 + 16) / 32 : Nat) = 0 := by decide
      have hrhs : ((32 * 3329 + 16) / 32 : Nat) = 3329 := by decide
      rw [hlhs, hrhs]
      decide
  unfold compressErrZMod
  rw [hdec_mod]
  have hb := err5Int_bounds x.val
  have hcast :
      ((((q5 * 3329 + 16) / 32 : Nat) : ZMod mlkemQ) - x) =
        (err5Int x.val : ZMod mlkemQ) := by
    unfold err5Int
    rw [show q5 = (x.val * 32 + 1664) / 3329 from rfl]
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hcast]
  exact centeredZMod_of_int_bounds (by omega) (by omega)

private theorem err5Int_step (u : Nat) :
    err5Int (u + 1) = err5Int u - 1 ∨ (err5Int u ≤ -51 ∧ 51 ≤ err5Int (u + 1)) := by
  unfold err5Int
  set q0 : Nat := (u * 32 + 1664) / 3329
  set rem : Nat := (u * 32 + 1664) % 3329
  have hdiv : 3329 * q0 + rem = u * 32 + 1664 := Nat.div_add_mod (u * 32 + 1664) 3329
  have hrem : rem < 3329 := Nat.mod_lt _ (by omega)
  clear_value q0 rem
  have hq1 : ((u + 1) * 32 + 1664) / 3329 = q0 + (rem + 32) / 3329 := by
    have heq : (u + 1) * 32 + 1664 = (rem + 32) + q0 * 3329 := by omega
    rw [heq, Nat.add_mul_div_right _ _ (by omega), Nat.add_comm]
  rw [hq1]
  by_cases hwrap : rem + 32 < 3329
  · left
    have hq1_0 : (rem + 32) / 3329 = 0 := Nat.div_eq_of_lt hwrap
    rw [hq1_0]
    simp only [Nat.add_zero]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  · right
    have hq1_1 : (rem + 32) / 3329 = 1 :=
      nat_div_eq (by omega) (by omega) (by omega)
    rw [hq1_1]
    set d0 : Nat := (q0 * 3329 + 16) / 32
    set r0 : Nat := (q0 * 3329 + 16) % 32
    have hd0 : 32 * d0 + r0 = q0 * 3329 + 16 := Nat.div_add_mod _ 32
    have hr0 : r0 < 32 := Nat.mod_lt _ (by omega)
    set d1 : Nat := ((q0 + 1) * 3329 + 16) / 32
    set r1 : Nat := ((q0 + 1) * 3329 + 16) % 32
    have hd1 : 32 * d1 + r1 = (q0 + 1) * 3329 + 16 := Nat.div_add_mod _ 32
    have hr1 : r1 < 32 := Nat.mod_lt _ (by omega)
    clear_value d0 r0 d1 r1
    omega

private theorem compressErrZMod_5_step (x : ZMod mlkemQ) :
    compressErrZMod 5 (x + 1) = compressErrZMod 5 x - 1 ∨
      (compressErrZMod 5 x ≤ -51 ∧ 51 ≤ compressErrZMod 5 (x + 1)) := by
  rw [compressErrZMod_5_eq x, compressErrZMod_5_eq (x + 1)]
  rcases val_add_one x with ⟨h3328, h0⟩ | ⟨_, hsucc⟩
  · left
    rw [h3328, h0]
    unfold err5Int
    omega
  · rw [hsucc]
    exact err5Int_step x.val

private theorem centered_decomp5_sub_eq (v0 : ZMod mlkemQ) {e : Int} (hlo : -2 ≤ e) (hhi : e ≤ 2) :
    centeredZMod ((decompressCoeff 5 (compressCoeff 5 (v0 + (e : ZMod mlkemQ)).val) : ZMod mlkemQ) - v0) =
      compressErrZMod 5 (v0 + (e : ZMod mlkemQ)) + e := by
  set x : ZMod mlkemQ := v0 + (e : ZMod mlkemQ)
  have hb : -52 ≤ compressErrZMod 5 x ∧ compressErrZMod 5 x ≤ 52 := by
    rw [compressErrZMod_5_eq]; exact err5Int_bounds _
  have hcast :
      ((decompressCoeff 5 (compressCoeff 5 x.val) : ZMod mlkemQ) - v0) =
        ((compressErrZMod 5 x + e : Int) : ZMod mlkemQ) := by
    push_cast
    unfold compressErrZMod
    rw [centeredZMod_cast_eq]
    dsimp [x]
    ring
  rw [hcast]
  exact centeredZMod_of_int_bounds (by omega) (by omega)

private theorem weighted_sum_le_constH {e0 e1 e2 e3 e4 : Int}
    (h : (e0 ≤ 50 ∧ e1 ≤ 50 ∧ e2 ≤ 50 ∧ e3 ≤ 50 ∧ e4 ≤ 50) ∨
         (e0 ≤ 0 ∧ e1 ≤ 51 ∧ e2 ≤ 51 ∧ e3 ≤ 51 ∧ e4 ≤ 51) ∨
         (e0 ≤ 0 ∧ e1 ≤ 0 ∧ e2 ≤ 52 ∧ e3 ≤ 52 ∧ e4 ≤ 52) ∨
         (e0 ≤ 0 ∧ e1 ≤ 0 ∧ e2 ≤ 0 ∧ e3 ≤ 53 ∧ e4 ≤ 53) ∨
         (e0 ≤ 0 ∧ e1 ≤ 0 ∧ e2 ≤ 0 ∧ e3 ≤ 0 ∧ e4 ≤ 54)) :
    (1 / 16 : Rat) * lamW2 ^ e0 +
    ((4 / 16 : Rat) * lamW2 ^ e1 +
    ((6 / 16 : Rat) * lamW2 ^ e2 +
    ((4 / 16 : Rat) * lamW2 ^ e3 +
    ((1 / 16 : Rat) * lamW2 ^ e4 + 0)))) ≤ constH := by
  have h1 : (1 : Rat) ≤ lamW2 := by unfold lamW2; norm_num
  rcases h with ⟨h0, h1', h2, h3, h4⟩ | ⟨h0, h1', h2, h3, h4⟩ |
    ⟨h0, h1', h2, h3, h4⟩ | ⟨h0, h1', h2, h3, h4⟩ | ⟨h0, h1', h2, h3, h4⟩
  · have p0 := zpow_le_zpow_right₀ h1 h0
    have p1 := zpow_le_zpow_right₀ h1 h1'
    have p2 := zpow_le_zpow_right₀ h1 h2
    have p3 := zpow_le_zpow_right₀ h1 h3
    have p4 := zpow_le_zpow_right₀ h1 h4
    have hsum :
        (1 / 16 : Rat) * lamW2 ^ e0 +
        ((4 / 16 : Rat) * lamW2 ^ e1 +
        ((6 / 16 : Rat) * lamW2 ^ e2 +
        ((4 / 16 : Rat) * lamW2 ^ e3 +
        ((1 / 16 : Rat) * lamW2 ^ e4 + 0)))) ≤ lamW2 ^ (50 : Int) := by linarith
    refine le_trans hsum ?_
    unfold lamW2 constH; norm_num
  · have p0 : lamW2 ^ e0 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h0
    have p1 := zpow_le_zpow_right₀ h1 h1'
    have p2 := zpow_le_zpow_right₀ h1 h2
    have p3 := zpow_le_zpow_right₀ h1 h3
    have p4 := zpow_le_zpow_right₀ h1 h4
    have hsum :
        (1 / 16 : Rat) * lamW2 ^ e0 +
        ((4 / 16 : Rat) * lamW2 ^ e1 +
        ((6 / 16 : Rat) * lamW2 ^ e2 +
        ((4 / 16 : Rat) * lamW2 ^ e3 +
        ((1 / 16 : Rat) * lamW2 ^ e4 + 0)))) ≤
          (1 / 16 : Rat) + (15 / 16 : Rat) * lamW2 ^ (51 : Int) := by linarith
    refine le_trans hsum ?_
    unfold lamW2 constH; norm_num
  · have p0 : lamW2 ^ e0 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h0
    have p1 : lamW2 ^ e1 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h1'
    have p2 := zpow_le_zpow_right₀ h1 h2
    have p3 := zpow_le_zpow_right₀ h1 h3
    have p4 := zpow_le_zpow_right₀ h1 h4
    have hsum :
        (1 / 16 : Rat) * lamW2 ^ e0 +
        ((4 / 16 : Rat) * lamW2 ^ e1 +
        ((6 / 16 : Rat) * lamW2 ^ e2 +
        ((4 / 16 : Rat) * lamW2 ^ e3 +
        ((1 / 16 : Rat) * lamW2 ^ e4 + 0)))) ≤
          (5 / 16 : Rat) + (11 / 16 : Rat) * lamW2 ^ (52 : Int) := by linarith
    refine le_trans hsum ?_
    unfold lamW2 constH; norm_num
  · have p0 : lamW2 ^ e0 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h0
    have p1 : lamW2 ^ e1 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h1'
    have p2 : lamW2 ^ e2 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h2
    have p3 := zpow_le_zpow_right₀ h1 h3
    have p4 := zpow_le_zpow_right₀ h1 h4
    have hsum :
        (1 / 16 : Rat) * lamW2 ^ e0 +
        ((4 / 16 : Rat) * lamW2 ^ e1 +
        ((6 / 16 : Rat) * lamW2 ^ e2 +
        ((4 / 16 : Rat) * lamW2 ^ e3 +
        ((1 / 16 : Rat) * lamW2 ^ e4 + 0)))) ≤
          (11 / 16 : Rat) + (5 / 16 : Rat) * lamW2 ^ (53 : Int) := by linarith
    refine le_trans hsum ?_
    unfold lamW2 constH; norm_num
  · have p0 : lamW2 ^ e0 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h0
    have p1 : lamW2 ^ e1 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h1'
    have p2 : lamW2 ^ e2 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h2
    have p3 : lamW2 ^ e3 ≤ 1 := by simpa using zpow_le_zpow_right₀ h1 h3
    have p4 := zpow_le_zpow_right₀ h1 h4
    have hsum :
        (1 / 16 : Rat) * lamW2 ^ e0 +
        ((4 / 16 : Rat) * lamW2 ^ e1 +
        ((6 / 16 : Rat) * lamW2 ^ e2 +
        ((4 / 16 : Rat) * lamW2 ^ e3 +
        ((1 / 16 : Rat) * lamW2 ^ e4 + 0)))) ≤
          (15 / 16 : Rat) + (1 / 16 : Rat) * lamW2 ^ (54 : Int) := by linarith
    refine le_trans hsum ?_
    unfold lamW2 constH; norm_num

private theorem step5_pos_cases {c0 c1 c2 c3 c4 : Int}
    (hb0 : -52 ≤ c0 ∧ c0 ≤ 52) (hb1 : -52 ≤ c1 ∧ c1 ≤ 52) (hb2 : -52 ≤ c2 ∧ c2 ≤ 52)
    (hb3 : -52 ≤ c3 ∧ c3 ≤ 52) (hb4 : -52 ≤ c4 ∧ c4 ≤ 52)
    (hs01 : c1 = c0 - 1 ∨ (c0 ≤ -51 ∧ 51 ≤ c1))
    (hs12 : c2 = c1 - 1 ∨ (c1 ≤ -51 ∧ 51 ≤ c2))
    (hs23 : c3 = c2 - 1 ∨ (c2 ≤ -51 ∧ 51 ≤ c3))
    (hs34 : c4 = c3 - 1 ∨ (c3 ≤ -51 ∧ 51 ≤ c4)) :
    (1 * (c0 + -2) ≤ 50 ∧ 1 * (c1 + -1) ≤ 50 ∧ 1 * (c2 + 0) ≤ 50 ∧ 1 * (c3 + 1) ≤ 50 ∧ 1 * (c4 + 2) ≤ 50) ∨
    (1 * (c0 + -2) ≤ 0 ∧ 1 * (c1 + -1) ≤ 51 ∧ 1 * (c2 + 0) ≤ 51 ∧ 1 * (c3 + 1) ≤ 51 ∧ 1 * (c4 + 2) ≤ 51) ∨
    (1 * (c0 + -2) ≤ 0 ∧ 1 * (c1 + -1) ≤ 0 ∧ 1 * (c2 + 0) ≤ 52 ∧ 1 * (c3 + 1) ≤ 52 ∧ 1 * (c4 + 2) ≤ 52) ∨
    (1 * (c0 + -2) ≤ 0 ∧ 1 * (c1 + -1) ≤ 0 ∧ 1 * (c2 + 0) ≤ 0 ∧ 1 * (c3 + 1) ≤ 53 ∧ 1 * (c4 + 2) ≤ 53) ∨
    (1 * (c0 + -2) ≤ 0 ∧ 1 * (c1 + -1) ≤ 0 ∧ 1 * (c2 + 0) ≤ 0 ∧ 1 * (c3 + 1) ≤ 0 ∧ 1 * (c4 + 2) ≤ 54) := by
  rcases hs01 with h01 | h01
  · rcases hs12 with h12 | h12
    · rcases hs23 with h23 | h23
      · rcases hs34 with h34 | h34
        · left; omega
        · right; right; right; right; omega
      · rcases hs34 with h34 | h34
        · right; right; right; left; omega
        · omega
    · rcases hs23 with h23 | h23
      · rcases hs34 with h34 | h34
        · right; right; left; omega
        · omega
      · omega
  · rcases hs12 with h12 | h12
    · rcases hs23 with h23 | h23
      · rcases hs34 with h34 | h34
        · right; left; omega
        · omega
      · omega
    · omega

private theorem step5_neg_cases {c0 c1 c2 c3 c4 : Int}
    (hb0 : -52 ≤ c0 ∧ c0 ≤ 52) (hb1 : -52 ≤ c1 ∧ c1 ≤ 52) (hb2 : -52 ≤ c2 ∧ c2 ≤ 52)
    (hb3 : -52 ≤ c3 ∧ c3 ≤ 52) (hb4 : -52 ≤ c4 ∧ c4 ≤ 52)
    (hs01 : c1 = c0 - 1 ∨ (c0 ≤ -51 ∧ 51 ≤ c1))
    (hs12 : c2 = c1 - 1 ∨ (c1 ≤ -51 ∧ 51 ≤ c2))
    (hs23 : c3 = c2 - 1 ∨ (c2 ≤ -51 ∧ 51 ≤ c3))
    (hs34 : c4 = c3 - 1 ∨ (c3 ≤ -51 ∧ 51 ≤ c4)) :
    ((-1) * (c4 + 2) ≤ 50 ∧ (-1) * (c3 + 1) ≤ 50 ∧ (-1) * (c2 + 0) ≤ 50 ∧ (-1) * (c1 + -1) ≤ 50 ∧ (-1) * (c0 + -2) ≤ 50) ∨
    ((-1) * (c4 + 2) ≤ 0 ∧ (-1) * (c3 + 1) ≤ 51 ∧ (-1) * (c2 + 0) ≤ 51 ∧ (-1) * (c1 + -1) ≤ 51 ∧ (-1) * (c0 + -2) ≤ 51) ∨
    ((-1) * (c4 + 2) ≤ 0 ∧ (-1) * (c3 + 1) ≤ 0 ∧ (-1) * (c2 + 0) ≤ 52 ∧ (-1) * (c1 + -1) ≤ 52 ∧ (-1) * (c0 + -2) ≤ 52) ∨
    ((-1) * (c4 + 2) ≤ 0 ∧ (-1) * (c3 + 1) ≤ 0 ∧ (-1) * (c2 + 0) ≤ 0 ∧ (-1) * (c1 + -1) ≤ 53 ∧ (-1) * (c0 + -2) ≤ 53) ∨
    ((-1) * (c4 + 2) ≤ 0 ∧ (-1) * (c3 + 1) ≤ 0 ∧ (-1) * (c2 + 0) ≤ 0 ∧ (-1) * (c1 + -1) ≤ 0 ∧ (-1) * (c0 + -2) ≤ 54) := by
  rcases hs01 with h01 | h01
  · rcases hs12 with h12 | h12
    · rcases hs23 with h23 | h23
      · rcases hs34 with h34 | h34
        · left; omega
        · right; left; omega
      · rcases hs34 with h34 | h34
        · right; right; left; omega
        · omega
    · rcases hs23 with h23 | h23
      · rcases hs34 with h34 | h34
        · right; right; right; left; omega
        · omega
      · omega
  · rcases hs12 with h12 | h12
    · rcases hs23 with h23 | h23
      · rcases hs34 with h34 | h34
        · right; right; right; right; omega
        · omega
      · omega
    · omega

theorem termHAt_le_constH (v0 : ZMod mlkemQ) :
    termHAt v0 1 ≤ constH ∧ termHAt v0 (-1) ≤ constH := by
  set x0 : ZMod mlkemQ := v0 + (-2 : Int)
  set x1 : ZMod mlkemQ := v0 + (-1 : Int)
  set x2 : ZMod mlkemQ := v0 + (0 : Int)
  set x3 : ZMod mlkemQ := v0 + (1 : Int)
  set x4 : ZMod mlkemQ := v0 + (2 : Int)
  have hx01 : x1 = x0 + 1 := by dsimp [x0, x1]; ring
  have hx12 : x2 = x1 + 1 := by dsimp [x1, x2]; ring
  have hx23 : x3 = x2 + 1 := by dsimp [x2, x3]; ring
  have hx34 : x4 = x3 + 1 := by dsimp [x3, x4]; ring
  set c0 : Int := compressErrZMod 5 x0
  set c1 : Int := compressErrZMod 5 x1
  set c2 : Int := compressErrZMod 5 x2
  set c3 : Int := compressErrZMod 5 x3
  set c4 : Int := compressErrZMod 5 x4
  have hb0 : -52 ≤ c0 ∧ c0 ≤ 52 := by dsimp [c0]; rw [compressErrZMod_5_eq]; exact err5Int_bounds _
  have hb1 : -52 ≤ c1 ∧ c1 ≤ 52 := by dsimp [c1]; rw [compressErrZMod_5_eq]; exact err5Int_bounds _
  have hb2 : -52 ≤ c2 ∧ c2 ≤ 52 := by dsimp [c2]; rw [compressErrZMod_5_eq]; exact err5Int_bounds _
  have hb3 : -52 ≤ c3 ∧ c3 ≤ 52 := by dsimp [c3]; rw [compressErrZMod_5_eq]; exact err5Int_bounds _
  have hb4 : -52 ≤ c4 ∧ c4 ≤ 52 := by dsimp [c4]; rw [compressErrZMod_5_eq]; exact err5Int_bounds _
  have hs01 : c1 = c0 - 1 ∨ (c0 ≤ -51 ∧ 51 ≤ c1) := by dsimp [c0, c1]; rw [hx01]; exact compressErrZMod_5_step x0
  have hs12 : c2 = c1 - 1 ∨ (c1 ≤ -51 ∧ 51 ≤ c2) := by dsimp [c1, c2]; rw [hx12]; exact compressErrZMod_5_step x1
  have hs23 : c3 = c2 - 1 ∨ (c2 ≤ -51 ∧ 51 ≤ c3) := by dsimp [c2, c3]; rw [hx23]; exact compressErrZMod_5_step x2
  have hs34 : c4 = c3 - 1 ∨ (c3 ≤ -51 ∧ 51 ≤ c4) := by dsimp [c3, c4]; rw [hx34]; exact compressErrZMod_5_step x3
  have hz0 := centered_decomp5_sub_eq v0 (e := -2) (by omega) (by omega)
  have hz1 := centered_decomp5_sub_eq v0 (e := -1) (by omega) (by omega)
  have hz2 := centered_decomp5_sub_eq v0 (e := 0) (by omega) (by omega)
  have hz3 := centered_decomp5_sub_eq v0 (e := 1) (by omega) (by omega)
  have hz4 := centered_decomp5_sub_eq v0 (e := 2) (by omega) (by omega)
  have hw_m2 : cbd2WeightQ (-2) = 1 / 16 := by unfold cbd2WeightQ; norm_num
  have hw_m1 : cbd2WeightQ (-1) = 4 / 16 := by unfold cbd2WeightQ; norm_num
  have hw_0 : cbd2WeightQ 0 = 6 / 16 := by unfold cbd2WeightQ; norm_num
  have hw_p1 : cbd2WeightQ 1 = 4 / 16 := by unfold cbd2WeightQ; norm_num
  have hw_p2 : cbd2WeightQ 2 = 1 / 16 := by unfold cbd2WeightQ; norm_num
  constructor
  · simp only [termHAt, cbd2Support, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    change cbd2WeightQ (-2) * lamW2 ^ (1 * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x0.val) : ZMod mlkemQ) - v0)) +
      (cbd2WeightQ (-1) * lamW2 ^ (1 * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x1.val) : ZMod mlkemQ) - v0)) +
      (cbd2WeightQ 0 * lamW2 ^ (1 * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x2.val) : ZMod mlkemQ) - v0)) +
      (cbd2WeightQ 1 * lamW2 ^ (1 * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x3.val) : ZMod mlkemQ) - v0)) +
      (cbd2WeightQ 2 * lamW2 ^ (1 * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x4.val) : ZMod mlkemQ) - v0)) + 0)))) ≤ constH
    rw [hz0, hz1, hz2, hz3, hz4, hw_m2, hw_m1, hw_0, hw_p1, hw_p2]
    exact weighted_sum_le_constH (step5_pos_cases hb0 hb1 hb2 hb3 hb4 hs01 hs12 hs23 hs34)
  · simp only [termHAt, cbd2Support, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    change cbd2WeightQ (-2) * lamW2 ^ ((-1) * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x0.val) : ZMod mlkemQ) - v0)) +
      (cbd2WeightQ (-1) * lamW2 ^ ((-1) * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x1.val) : ZMod mlkemQ) - v0)) +
      (cbd2WeightQ 0 * lamW2 ^ ((-1) * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x2.val) : ZMod mlkemQ) - v0)) +
      (cbd2WeightQ 1 * lamW2 ^ ((-1) * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x3.val) : ZMod mlkemQ) - v0)) +
      (cbd2WeightQ 2 * lamW2 ^ ((-1) * centeredZMod ((decompressCoeff 5 (compressCoeff 5 x4.val) : ZMod mlkemQ) - v0)) + 0)))) ≤ constH
    rw [hz0, hz1, hz2, hz3, hz4, hw_m2, hw_m1, hw_0, hw_p1, hw_p2]
    have hsym :
        (1 / 16 : Rat) * lamW2 ^ ((-1) * (c0 + -2)) +
        ((4 / 16 : Rat) * lamW2 ^ ((-1) * (c1 + -1)) +
        ((6 / 16 : Rat) * lamW2 ^ ((-1) * (c2 + 0)) +
        ((4 / 16 : Rat) * lamW2 ^ ((-1) * (c3 + 1)) +
        ((1 / 16 : Rat) * lamW2 ^ ((-1) * (c4 + 2)) + 0)))) =
        (1 / 16 : Rat) * lamW2 ^ ((-1) * (c4 + 2)) +
        ((4 / 16 : Rat) * lamW2 ^ ((-1) * (c3 + 1)) +
        ((6 / 16 : Rat) * lamW2 ^ ((-1) * (c2 + 0)) +
        ((4 / 16 : Rat) * lamW2 ^ ((-1) * (c1 + -1)) +
        ((1 / 16 : Rat) * lamW2 ^ ((-1) * (c0 + -2)) + 0)))) := by ring
    rw [hsym]
    exact weighted_sum_le_constH (step5_neg_cases hb0 hb1 hb2 hb3 hb4 hs01 hs12 hs23 hs34)

/-! ### Dyadic Squaring Chain for `w2_certificate_lt_two_pow_neg_112` -/

private theorem sq_dyadic_le {x : Rat} {m m' e e' : Nat} (s : Nat)
    (hx0 : 0 ≤ x) (hx : x ≤ (m : Rat) / (2 : Rat) ^ e)
    (he : e' + s = 2 * e) (hm : m * m ≤ m' * 2 ^ s) :
    x ^ 2 ≤ (m' : Rat) / (2 : Rat) ^ e' := by
  have hsq : x ^ 2 ≤ ((m : Rat) / (2 : Rat) ^ e) ^ 2 :=
    pow_le_pow_left₀ hx0 hx 2
  refine le_trans hsq ?_
  have hm_rat : (m : Rat) ^ 2 ≤ (m' : Rat) * (2 : Rat) ^ s := by
    have hnat : ((m * m : Nat) : Rat) ≤ ((m' * 2 ^ s : Nat) : Rat) := by exact_mod_cast hm
    simpa [sq] using hnat
  have h2s_ne : (2 : Rat) ^ s ≠ 0 := by positivity
  rw [div_pow, ← pow_mul, mul_comm e 2, ← he, pow_add]
  calc (m : Rat) ^ 2 / ((2 : Rat) ^ e' * (2 : Rat) ^ s)
      ≤ ((m' : Rat) * (2 : Rat) ^ s) / ((2 : Rat) ^ e' * (2 : Rat) ^ s) :=
        div_le_div_of_nonneg_right hm_rat (by positivity)
    _ = (m' : Rat) / (2 : Rat) ^ e' :=
        mul_div_mul_right (m' : Rat) ((2 : Rat) ^ e') h2s_ne

private theorem pow_double_dyadic_le {x : Rat} {k m m' e e' : Nat} (s : Nat)
    (hx0 : 0 ≤ x) (hx : x ^ k ≤ (m : Rat) / (2 : Rat) ^ e)
    (he : e' + s = 2 * e) (hm : m * m ≤ m' * 2 ^ s) :
    x ^ (2 * k) ≤ (m' : Rat) / (2 : Rat) ^ e' := by
  have hk0 : 0 ≤ x ^ k := pow_nonneg hx0 k
  have h2 := sq_dyadic_le s hk0 hx he hm
  simpa [pow_mul'] using h2

theorem w2_certificate_lt_two_pow_neg_112 :
    512 * lamW2 ^ (-832 : Int) * constA ^ 1024 * constG ^ 1024 * constH < 1 / (2 : Rat) ^ 112 := by
  have hag0 : 0 ≤ constA * constG := by unfold constA constG; norm_num
  have hag1 : (constA * constG) ^ 1 ≤ (2345258007 : Rat) / (2 : Rat) ^ 31 := by
    unfold constA constG; norm_num
  have hag2 := pow_double_dyadic_le (m' := 2561246567) (e' := 31) 31 hag0 hag1 (by norm_num) (by norm_num)
  have hag4 := pow_double_dyadic_le (m' := 3054730584) (e' := 31) 31 hag0 hag2 (by norm_num) (by norm_num)
  have hag8 := pow_double_dyadic_le (m' := 2172630965) (e' := 30) 32 hag0 hag4 (by norm_num) (by norm_num)
  have hag16 := pow_double_dyadic_le (m' := 2198072761) (e' := 29) 31 hag0 hag8 (by norm_num) (by norm_num)
  set X : Rat := (constA * constG) ^ (2 * (2 * (2 * (2 * 1)))) * (4 / 5 : Rat) ^ 13
  have hX0 : 0 ≤ X := mul_nonneg (pow_nonneg hag0 _) (by norm_num)
  have hX1 : X ^ 1 ≤ (3866890496 : Rat) / (2 : Rat) ^ 34 := by
    rw [pow_one]
    have hmul : X ≤ ((2198072761 : Rat) / (2 : Rat) ^ 29) * (4 / 5 : Rat) ^ 13 :=
      mul_le_mul_of_nonneg_right hag16 (by norm_num)
    refine le_trans hmul ?_
    norm_num
  have hX2 := pow_double_dyadic_le (m' := 3481479853) (e' := 36) 32 hX0 hX1 (by norm_num) (by norm_num)
  have hX4 := pow_double_dyadic_le (m' := 2822070841) (e' := 40) 32 hX0 hX2 (by norm_num) (by norm_num)
  have hX8 := pow_double_dyadic_le (m' := 3708565530) (e' := 49) 31 hX0 hX4 (by norm_num) (by norm_num)
  have hX16 := pow_double_dyadic_le (m' := 3202226547) (e' := 66) 32 hX0 hX8 (by norm_num) (by norm_num)
  have hX32 := pow_double_dyadic_le (m' := 2387504759) (e' := 100) 32 hX0 hX16 (by norm_num) (by norm_num)
  have hX64 := pow_double_dyadic_le (m' := 2654352680) (e' := 169) 31 hX0 hX32 (by norm_num) (by norm_num)
  have hlam_inv : lamW2⁻¹ = 4 / 5 := by unfold lamW2; norm_num
  have hlam : lamW2 ^ (-832 : Int) = (4 / 5 : Rat) ^ 832 := by
    have hneg : (-832 : Int) = -(832 : Nat) := by decide
    rw [hneg, zpow_neg, zpow_natCast, ← inv_pow, hlam_inv]
  have h64 : 2 * (2 * (2 * (2 * (2 * (2 * 1))))) = 64 := rfl
  rw [h64] at hX64
  have hX64_eq : X ^ 64 = lamW2 ^ (-832 : Int) * constA ^ 1024 * constG ^ 1024 := by
    rw [hlam]
    dsimp [X]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_pow]
    rw [show 16 * 64 = 1024 by decide, show 13 * 64 = 832 by decide]
    rw [mul_comm _ ((4 / 5 : Rat) ^ 832), ← mul_assoc]
  have hprod :
      512 * lamW2 ^ (-832 : Int) * constA ^ 1024 * constG ^ 1024 * constH =
        512 * (lamW2 ^ (-832 : Int) * constA ^ 1024 * constG ^ 1024) * constH := by
    simp only [mul_assoc]
  rw [hprod, ← hX64_eq]
  have hH : constH = 82108 := rfl
  rw [hH]
  have hstep : 512 * X ^ 64 * 82108 ≤ 512 * ((2654352680 : Rat) / (2 : Rat) ^ 169) * 82108 := by
    linarith
  refine lt_of_le_of_lt hstep ?_
  norm_num

end Computational.Proofs.Kyber1024Delta.RationalCertificate

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Shared Definitions for Kyber-1024 `δ_kem` Correctness Proofs (`Kyber1024Delta.Common`)

Shared ring, polynomial, centered-representative, compression-error, and `CBD_2` definitions
for the Kyber-1024 `δ_kem ≤ ε + 2^-112` proof modules.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.Kyber1024Delta.Common

open CryptoGames.MLKEM (
  Poly
  compressCoeff
  decompressCoeff
  mlkemQ
)

/-- Prime modulus `3329` is positive (`NeZero 3329` instance for `ZMod 3329`). -/
instance instNeZeroMlkemQ : NeZero mlkemQ := ⟨by decide⟩

/-- Polynomial ring carrier `Fin 256 → ZMod 3329` corresponding to `ℤ_3329[X]/(X^256 + 1)`. -/
abbrev ZPoly := Fin 256 → ZMod mlkemQ

/-- Interpret a specification `Poly` (`Array Nat`) as a `ZPoly` via `.getD i.val 0`. -/
@[expose] def toZPoly (p : Poly) : ZPoly :=
  fun i => ((p.getD i.val 0 : Nat) : ZMod mlkemQ)

/-- Canonical `Poly` (`Array Nat` of size 256 with entries in `[0, 3328]`) from a `ZPoly`. -/
@[expose] def ofZPoly (f : ZPoly) : Poly :=
  Array.ofFn (n := 256) fun i => (f i).val

/-- A specification `Poly` is canonical when it has size 256 and every entry is `< 3329`. -/
@[expose] def IsCanonicalPoly (p : Poly) : Prop :=
  p.size = 256 ∧ ∀ i : Nat, i < 256 → p.getD i 0 < mlkemQ

/-- Explicit negacyclic convolution in `ℤ_3329[X]/(X^256 + 1)`:
`(negacyclicMul a b) j = ∑_{i ≤ j} a_i b_{j - i} - ∑_{i > j} a_i b_{256 + j - i}`. -/
@[expose] def negacyclicMul (a b : ZPoly) : ZPoly :=
  fun j =>
    ∑ i : Fin 256,
      if h : i.val ≤ j.val then
        a i * b ⟨j.val - i.val, by omega⟩
      else
        -(a i * b ⟨256 + j.val - i.val, by omega⟩)

/-- Explicit negacyclic convolution over integer polynomials `Fin 256 → Int` (before mod-`3329`
reduction, avoiding intermediate wraparound in the Chernoff noise sum). -/
@[expose] def negacyclicMulInt (a b : Fin 256 → Int) : Fin 256 → Int :=
  fun j =>
    ∑ i : Fin 256,
      if h : i.val ≤ j.val then
        a i * b ⟨j.val - i.val, by omega⟩
      else
        -(a i * b ⟨256 + j.val - i.val, by omega⟩)

/-- Centered representative in `[-1664, 1664]` of `x : ZMod 3329`. -/
@[expose] def centeredZMod (x : ZMod mlkemQ) : Int :=
  let u : Nat := x.val
  if u ≤ 1664 then (u : Int) else (u : Int) - 3329

/-- Centered roundtrip compression error `centeredZMod (decompressCoeff d (compressCoeff d x.val) - x)`. -/
@[expose] def compressErrZMod (d : Nat) (x : ZMod mlkemQ) : Int :=
  centeredZMod ((decompressCoeff d (compressCoeff d x.val) : ZMod mlkemQ) - x)

/-- Exact `CBD_2` probability weight in `ℚ` on `k ∈ ℤ`: `C(4, k + 2) / 16` for `k ∈ [-2, 2]`, `0` otherwise. -/
@[expose] def cbd2WeightQ (k : Int) : Rat :=
  if k == -2 then 1 / 16
  else if k == -1 then 4 / 16
  else if k == 0 then 6 / 16
  else if k == 1 then 4 / 16
  else if k == 2 then 1 / 16
  else 0

/-- Support list `[-2, -1, 0, 1, 2]` of `CBD_2`. -/
@[expose] def cbd2Support : List Int := [-2, -1, 0, 1, 2]

theorem getD_ofFn_nat {α : Type} {n : Nat} (g : Fin n → α) (i : Nat) (d : α) (hi : i < n) :
    (Array.ofFn g).getD i d = g ⟨i, hi⟩ := by
  simp [Array.getD, hi]

theorem toZPoly_ofZPoly (f : ZPoly) : toZPoly (ofZPoly f) = f := by
  funext i
  simp [toZPoly, ofZPoly, getD_ofFn_nat _ _ _ i.isLt]

theorem ofZPoly_isCanonical (f : ZPoly) : IsCanonicalPoly (ofZPoly f) := by
  refine ⟨by simp [ofZPoly], fun i hi => ?_⟩
  rw [ofZPoly, getD_ofFn_nat _ _ _ hi]
  exact ZMod.val_lt (f ⟨i, hi⟩)

theorem ofZPoly_toZPoly {p : Poly} (hp : IsCanonicalPoly p) : ofZPoly (toZPoly p) = p := by
  rcases hp with ⟨hsz, hlt⟩
  apply Array.ext
  · simp [ofZPoly, hsz]
  · intro i hi1 hi2
    have hi : i < 256 := by simpa [hsz] using hi2
    have hp_getD : p.getD i 0 = p[i] := by simp [Array.getD, hi2]
    have hlt_i : p[i] < mlkemQ := hp_getD ▸ hlt i hi
    simp [ofZPoly, toZPoly, hi2, Nat.mod_eq_of_lt hlt_i]

theorem centeredZMod_bounds (x : ZMod mlkemQ) :
    -1664 ≤ centeredZMod x ∧ centeredZMod x ≤ 1664 := by
  unfold centeredZMod
  have hlt : x.val < 3329 := ZMod.val_lt x
  dsimp only
  split_ifs <;> omega

theorem centeredZMod_cast_eq (x : ZMod mlkemQ) :
    ((centeredZMod x : Int) : ZMod mlkemQ) = x := by
  unfold centeredZMod
  dsimp only
  split_ifs
  · simp
  · push_cast
    have hq : (3329 : ZMod mlkemQ) = 0 := by decide
    simp [hq]

theorem centeredZMod_of_int_bounds {z : Int} (hlo : -1664 ≤ z) (hhi : z ≤ 1664) :
    centeredZMod (z : ZMod mlkemQ) = z := by
  unfold centeredZMod
  by_cases hz : 0 ≤ z
  · lift z to Nat using hz
    have hlt : z < mlkemQ := by dsimp [mlkemQ]; omega
    have hval : ((z : Nat) : ZMod mlkemQ).val = z := ZMod.val_cast_of_lt hlt
    have hcast : ((z : Int) : ZMod mlkemQ) = ((z : Nat) : ZMod mlkemQ) := by norm_cast
    rw [hcast, hval]
    dsimp only
    split_ifs <;> omega
  · have hpos : 0 ≤ z + 3329 := by omega
    let u : Nat := (z + 3329).toNat
    have hu_lt : u < mlkemQ := by dsimp [u, mlkemQ]; omega
    have hcast : ((z : Int) : ZMod mlkemQ) = ((u : Nat) : ZMod mlkemQ) := by
      have hz_eq : z = (u : Int) - 3329 := by dsimp [u]; omega
      rw [hz_eq]
      push_cast
      have hq : (3329 : ZMod mlkemQ) = 0 := by decide
      simp [hq]
    rw [hcast, ZMod.val_cast_of_lt hu_lt]
    dsimp only
    split_ifs <;> (dsimp [u] at *; omega)

theorem centeredZMod_neg (x : ZMod mlkemQ) :
    centeredZMod (-x) = -centeredZMod x := by
  have hb := centeredZMod_bounds x
  have hcast : ((-centeredZMod x : Int) : ZMod mlkemQ) = -x := by
    push_cast
    rw [centeredZMod_cast_eq]
  rw [← hcast]
  exact centeredZMod_of_int_bounds (by omega) (by omega)

theorem negacyclicMulInt_cast (a b : Fin 256 → Int) (j : Fin 256) :
    ((negacyclicMulInt a b j : Int) : ZMod mlkemQ) =
      negacyclicMul (fun i => (a i : ZMod mlkemQ)) (fun i => (b i : ZMod mlkemQ)) j := by
  unfold negacyclicMulInt negacyclicMul
  change (Int.castRingHom (ZMod mlkemQ)) _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Computational.Proofs.Kyber1024Delta.Common

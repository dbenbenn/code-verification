/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Kyber1024Delta.Common -- proof-setup: allow-public-import
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# ML-KEM / Kyber NTT Ring Homomorphism & Inversion (`Kyber1024Delta.NttAlgebra`)

Canonicality invariants, `ZPoly` (`Fin 256 → ZMod 3329`) ring operations, 7-stage butterfly
inversion (`polyInvNtt ∘ polyNtt = id`, `polyNtt ∘ polyInvNtt = id`), CRT degree-2 evaluation
over `ℤ_3329[X]/(X^2 - γ_p)`, and negacyclic convolution (`polyInvNtt (polyNttMul (polyNtt a) (polyNtt b)) = negacyclicMul a b`).
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.Kyber1024Delta.NttAlgebra

open CryptoGames.MLKEM (
  Poly
  bitRev7
  fipsZetas
  invNttStage
  mlkemQ
  nttStage
  polyAdd
  polyInvNtt
  polyNtt
  polyNttMul
  polySub
  vecDotNtt
  zeroPoly
)
open Computational.Proofs.Kyber1024Delta.Common (
  IsCanonicalPoly
  ZPoly
  getD_ofFn_nat
  negacyclicMul
  toZPoly
)

/-! ## 0. Polymorphic 256-Lane Butterfly Indexing & Modular Cast Helpers -/

private theorem size_set! {α : Type} (arr : Array α) (i : Nat) (v : α) :
    (arr.set! i v).size = arr.size := by
  simp [Array.set!]

private theorem getD_set! {α : Type} (arr : Array α) (k : Nat) (v : α) (idx : Nat) (d : α) :
    (arr.set! k v).getD idx d = if idx = k ∧ k < arr.size then v else arr.getD idx d := by
  by_cases hk : k < arr.size
  · by_cases hidx : idx = k
    · subst hidx; simp [Array.set!, Array.setIfInBounds, Array.getD, hk]
    · by_cases hi : idx < arr.size
      · simp [Array.set!, Array.setIfInBounds, Array.getD, hk, hi, hidx, Ne.symm hidx]
      · simp [Array.set!, Array.setIfInBounds, hk, hi, hidx]
  · simp [Array.set!, Array.setIfInBounds, hk]

private theorem foldl_range_stepK {α : Type} (n : Nat) (body : Array α → Nat → Nat → Array α)
    (stepK kAt : Nat → Nat) (kInit : Nat)
    (hk0 : kAt 0 = kInit) (hks : ∀ b, stepK (kAt b) = kAt (b + 1))
    (arr : Array α) :
    (List.range n).foldl (fun (cur, k) blk => (body cur k blk, stepK k)) (arr, kInit) =
      ((List.range n).foldl (fun cur blk => body cur (kAt blk) blk) arr, kAt n) := by
  induction n with
  | zero => simp [hk0]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih]
    simp [hks]

private def butterflyStage {α : Type} (len : Nat) (pairFn : Nat → α → α → α × α)
    (d : α) (arr : Array α) : Array α :=
  let nBlocks := 256 / (2 * len)
  (List.range nBlocks).foldl
    (fun cur blk =>
      let start := blk * 2 * len
      (List.range len).foldl
        (fun a off =>
          let j := start + off
          (a.set! j (pairFn blk (a.getD j d) (a.getD (j + len) d)).1).set!
            (j + len) (pairFn blk (a.getD j d) (a.getD (j + len) d)).2)
        cur)
    arr

private theorem inner_butterfly_spec {α : Type} (start len m : Nat)
    (pair : α → α → α × α) (d : α) (cur : Array α)
    (hsize : cur.size = 256) (hlen : 0 < len) (hm : m ≤ len) (hbnd : start + 2 * len ≤ 256) :
    let res := (List.range m).foldl
      (fun a off =>
        let j := start + off
        (a.set! j (pair (a.getD j d) (a.getD (j + len) d)).1).set!
          (j + len) (pair (a.getD j d) (a.getD (j + len) d)).2) cur
    res.size = 256 ∧
    ∀ idx < 256,
      res.getD idx d =
        if start ≤ idx ∧ idx < start + m then
          (pair (cur.getD idx d) (cur.getD (idx + len) d)).1
        else if start + len ≤ idx ∧ idx < start + len + m then
          (pair (cur.getD (idx - len) d) (cur.getD idx d)).2
        else
          cur.getD idx d := by
  induction m with
  | zero =>
    refine ⟨hsize, fun idx _ => ?_⟩
    have h1 : ¬ (start ≤ idx ∧ idx < start + 0) := by omega
    have h2 : ¬ (start + len ≤ idx ∧ idx < start + len + 0) := by omega
    simp only [List.range_zero, List.foldl_nil, h1, h2, ↓reduceIte]
  | succ m ih =>
    obtain ⟨hsz_m, hget_m⟩ := ih (by omega)
    dsimp only
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set prev := (List.range m).foldl
      (fun a off =>
        let j := start + off
        (a.set! j (pair (a.getD j d) (a.getD (j + len) d)).1).set!
          (j + len) (pair (a.getD j d) (a.getD (j + len) d)).2) cur
    have hj_lt : start + m < 256 := by omega
    have hjl_lt : start + m + len < 256 := by omega
    have hprev_j : prev.getD (start + m) d = cur.getD (start + m) d := by
      rw [hget_m (start + m) hj_lt]
      have c1 : ¬ (start ≤ start + m ∧ start + m < start + m) := by omega
      have c2 : ¬ (start + len ≤ start + m ∧ start + m < start + len + m) := by omega
      simp only [c1, c2, ↓reduceIte]
    have hprev_jl : prev.getD (start + m + len) d = cur.getD (start + m + len) d := by
      rw [hget_m (start + m + len) hjl_lt]
      have c1 : ¬ (start ≤ start + m + len ∧ start + m + len < start + m) := by omega
      have c2 : ¬ (start + len ≤ start + m + len ∧ start + m + len < start + len + m) := by omega
      simp only [c1, c2, ↓reduceIte]
    refine ⟨by rw [size_set!, size_set!, hsz_m], fun idx hidx => ?_⟩
    rw [getD_set!, getD_set!, size_set!, hsz_m, hprev_j, hprev_jl]
    by_cases heq2 : idx = start + m + len
    · subst heq2
      have hne1 : ¬ (start ≤ start + m + len ∧ start + m + len < start + (m + 1)) := by omega
      have hok2 : start + len ≤ start + m + len ∧ start + m + len < start + len + (m + 1) := by omega
      have hsub : start + m + len - len = start + m := by omega
      simp only [true_and, hjl_lt, hne1, hok2, ↓reduceIte, hsub]
    · simp only [heq2, false_and, ↓reduceIte]
      by_cases heq1 : idx = start + m
      · subst heq1
        have hok1 : start ≤ start + m ∧ start + m < start + (m + 1) := by omega
        simp only [true_and, hj_lt, hok1, ↓reduceIte]
      · simp only [heq1, false_and, ↓reduceIte, hget_m idx hidx]
        have he1 : (start ≤ idx ∧ idx < start + (m + 1)) ↔ (start ≤ idx ∧ idx < start + m) := by omega
        have he2 : (start + len ≤ idx ∧ idx < start + len + (m + 1)) ↔
            (start + len ≤ idx ∧ idx < start + len + m) := by omega
        simp only [he1, he2]

private theorem outer_butterfly_spec {α : Type} (len nBlocks b : Nat)
    (pairFn : Nat → α → α → α × α) (d : α) (arr : Array α)
    (hsize : arr.size = 256) (hlen : 0 < len) (hblocks : 2 * len * nBlocks = 256) (hb : b ≤ nBlocks) :
    let res := (List.range b).foldl
      (fun cur blk =>
        let start := blk * 2 * len
        (List.range len).foldl
          (fun a off =>
            let j := start + off
            (a.set! j (pairFn blk (a.getD j d) (a.getD (j + len) d)).1).set!
              (j + len) (pairFn blk (a.getD j d) (a.getD (j + len) d)).2)
          cur) arr
    res.size = 256 ∧
    ∀ idx < 256,
      res.getD idx d =
        if idx < b * (2 * len) then
          let blk := idx / (2 * len)
          if idx % (2 * len) < len then
            (pairFn blk (arr.getD idx d) (arr.getD (idx + len) d)).1
          else
            (pairFn blk (arr.getD (idx - len) d) (arr.getD idx d)).2
        else
          arr.getD idx d := by
  induction b with
  | zero =>
    refine ⟨hsize, fun idx _ => ?_⟩
    simp
  | succ b ih =>
    obtain ⟨hsz_b, hget_b⟩ := ih (by omega)
    dsimp only
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set prev := (List.range b).foldl
      (fun cur blk =>
        let start := blk * 2 * len
        (List.range len).foldl
          (fun a off =>
            let j := start + off
            (a.set! j (pairFn blk (a.getD j d) (a.getD (j + len) d)).1).set!
              (j + len) (pairFn blk (a.getD j d) (a.getD (j + len) d)).2)
          cur) arr
    have hmul_b : b * 2 * len = b * (2 * len) := Nat.mul_assoc b 2 len
    have hb_succ : (b + 1) * (2 * len) = b * (2 * len) + 2 * len := Nat.succ_mul b (2 * len)
    have hb_le : (b + 1) * (2 * len) ≤ 256 := by
      calc (b + 1) * (2 * len)
          ≤ nBlocks * (2 * len) := Nat.mul_le_mul_right (2 * len) hb
        _ = 256 := by rw [Nat.mul_comm]; exact hblocks
    have hbnd : b * 2 * len + 2 * len ≤ 256 := by omega
    obtain ⟨hsz_in, hget_in⟩ :=
      inner_butterfly_spec (b * 2 * len) len len (pairFn b) d prev hsz_b hlen (Nat.le_refl _) hbnd
    refine ⟨hsz_in, fun idx hidx => ?_⟩
    rw [hget_in idx hidx]
    by_cases hlo : idx < b * (2 * len)
    · have c1 : ¬ (b * 2 * len ≤ idx ∧ idx < b * 2 * len + len) := by omega
      have c2 : ¬ (b * 2 * len + len ≤ idx ∧ idx < b * 2 * len + len + len) := by omega
      have hlo' : idx < (b + 1) * (2 * len) := by omega
      simp only [c1, c2, hlo, hlo', ↓reduceIte, hget_b idx hidx]
    · by_cases hhi : idx < (b + 1) * (2 * len)
      · have hblk : idx / (2 * len) = b := Nat.div_eq_of_lt_le (by omega) hhi
        have hrem_eq : idx % (2 * len) = idx - b * (2 * len) := by
          have hd := Nat.div_add_mod idx (2 * len)
          rw [hblk, Nat.mul_comm (2 * len) b] at hd
          omega
        by_cases hhalf : idx < b * 2 * len + len
        · have c1 : b * 2 * len ≤ idx ∧ idx < b * 2 * len + len := by omega
          have hmod : idx % (2 * len) < len := by omega
          have hp1 : prev.getD idx d = arr.getD idx d := by
            rw [hget_b idx hidx]; simp only [hlo, ↓reduceIte]
          have hp2 : prev.getD (idx + len) d = arr.getD (idx + len) d := by
            have hnl : ¬ (idx + len < b * (2 * len)) := by omega
            rw [hget_b (idx + len) (by omega)]; simp only [hnl, ↓reduceIte]
          simp only [c1, hhi, hblk, hmod, and_self, ↓reduceIte, hp1, hp2]
        · have c1 : ¬ (b * 2 * len ≤ idx ∧ idx < b * 2 * len + len) := by omega
          have c2 : b * 2 * len + len ≤ idx ∧ idx < b * 2 * len + len + len := by omega
          have hmod : ¬ (idx % (2 * len) < len) := by omega
          have hp1 : prev.getD (idx - len) d = arr.getD (idx - len) d := by
            have hnl : ¬ (idx - len < b * (2 * len)) := by omega
            rw [hget_b (idx - len) (by omega)]; simp only [hnl, ↓reduceIte]
          have hp2 : prev.getD idx d = arr.getD idx d := by
            rw [hget_b idx hidx]; simp only [hlo, ↓reduceIte]
          simp only [c1, c2, hhi, hblk, hmod, and_self, ↓reduceIte, hp1, hp2]
      · have c1 : ¬ (b * 2 * len ≤ idx ∧ idx < b * 2 * len + len) := by omega
        have c2 : ¬ (b * 2 * len + len ≤ idx ∧ idx < b * 2 * len + len + len) := by omega
        simp only [c1, c2, hhi, hlo, ↓reduceIte, hget_b idx hidx]

private theorem butterflyStage_size {α : Type} {len : Nat} (pairFn : Nat → α → α → α × α)
    (d : α) {arr : Array α}
    (hsize : arr.size = 256) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) :
    (butterflyStage len pairFn d arr).size = 256 := by
  have hblocks : 2 * len * (256 / (2 * len)) = 256 := Nat.mul_div_cancel' hdiv
  exact (outer_butterfly_spec len (256 / (2 * len)) (256 / (2 * len))
    pairFn d arr hsize hlen hblocks (Nat.le_refl _)).1

private theorem butterflyStage_getD {α : Type} {len : Nat} (pairFn : Nat → α → α → α × α)
    (d : α) {arr : Array α} {idx : Nat}
    (hsize : arr.size = 256) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) (hidx : idx < 256) :
    (butterflyStage len pairFn d arr).getD idx d =
      let blk := idx / (2 * len)
      if idx % (2 * len) < len then
        (pairFn blk (arr.getD idx d) (arr.getD (idx + len) d)).1
      else
        (pairFn blk (arr.getD (idx - len) d) (arr.getD idx d)).2 := by
  have hblocks : 2 * len * (256 / (2 * len)) = 256 := Nat.mul_div_cancel' hdiv
  have h := (outer_butterfly_spec len (256 / (2 * len)) (256 / (2 * len))
    pairFn d arr hsize hlen hblocks (Nat.le_refl _)).2 idx hidx
  have hlt : idx < (256 / (2 * len)) * (2 * len) := by rw [Nat.mul_comm, hblocks]; exact hidx
  unfold butterflyStage
  dsimp only at h ⊢
  rw [h]
  simp only [hlt, ↓reduceIte]

private theorem nttStage_eq_butterfly (len kInit : Nat) (f : Poly) :
    nttStage len kInit f =
      (butterflyStage len
        (fun blk fj fjl =>
          let t := (fipsZetas.getD (kInit + blk) 0 * fjl) % mlkemQ
          ((fj + t) % mlkemQ, (fj + mlkemQ - t) % mlkemQ))
        0 f,
       kInit + 256 / (2 * len)) := by
  unfold nttStage butterflyStage
  exact foldl_range_stepK (256 / (2 * len))
    (fun cur k blk =>
      let start := blk * 2 * len
      (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let fj := arr.getD j 0
          let fjl := arr.getD (j + len) 0
          let t := (fipsZetas.getD k 0 * fjl) % mlkemQ
          (arr.set! j ((fj + t) % mlkemQ)).set! (j + len) ((fj + mlkemQ - t) % mlkemQ))
        cur)
    (· + 1) (kInit + ·) kInit (Nat.add_zero kInit) (fun b => (Nat.add_assoc kInit b 1).symm) f

private theorem invNttStage_eq_butterfly (len kInit : Nat) (f : Poly) :
    invNttStage len kInit f =
      (butterflyStage len
        (fun blk t fjl =>
          let zeta := fipsZetas.getD (kInit - blk) 0
          ((t + fjl) % mlkemQ, (zeta * (fjl + mlkemQ - t)) % mlkemQ))
        0 f,
       kInit - 256 / (2 * len)) := by
  unfold invNttStage butterflyStage
  exact foldl_range_stepK (256 / (2 * len))
    (fun cur k blk =>
      let start := blk * 2 * len
      (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let t := arr.getD j 0
          let fjl := arr.getD (j + len) 0
          (arr.set! j ((t + fjl) % mlkemQ)).set!
            (j + len) ((fipsZetas.getD k 0 * (fjl + mlkemQ - t)) % mlkemQ))
        cur)
    (· - 1) (kInit - ·) kInit (Nat.sub_zero kInit) (fun b => Nat.sub_sub kInit b 1) f

private theorem natCast_mod_q (n : Nat) :
    ((n % mlkemQ : Nat) : ZMod mlkemQ) = (n : ZMod mlkemQ) := by
  have hdiv : mlkemQ * (n / mlkemQ) + n % mlkemQ = n := Nat.div_add_mod n mlkemQ
  have hq : (3329 : ZMod mlkemQ) = 0 := by decide
  calc ((n % mlkemQ : Nat) : ZMod mlkemQ)
      = ((mlkemQ * (n / mlkemQ) + n % mlkemQ : Nat) : ZMod mlkemQ) := by
          push_cast
          simp [hq]
    _ = (n : ZMod mlkemQ) := by rw [hdiv]

private theorem natCast_sub_q {x y : Nat} (hy : y ≤ mlkemQ) :
    (((x + mlkemQ - y) % mlkemQ : Nat) : ZMod mlkemQ) =
      (x : ZMod mlkemQ) - (y : ZMod mlkemQ) := by
  rw [natCast_mod_q]
  have h1 : x + mlkemQ - y + y = x + mlkemQ := by omega
  have h2 : ((x + mlkemQ - y + y : Nat) : ZMod mlkemQ) = ((x + mlkemQ : Nat) : ZMod mlkemQ) :=
    congrArg Nat.cast h1
  have hq : (3329 : ZMod mlkemQ) = 0 := by decide
  push_cast at h2
  rw [hq, add_zero] at h2
  exact eq_sub_of_add_eq h2

/-! ## 1. Canonicality (`size = 256` and `< 3329`) -/

theorem zeroPoly_isCanonical : IsCanonicalPoly zeroPoly := by
  refine ⟨by simp [zeroPoly], fun i hi => ?_⟩
  simp [zeroPoly, Array.getD, hi, mlkemQ]

theorem polyAdd_isCanonical (a b : Poly) : IsCanonicalPoly (polyAdd a b) := by
  refine ⟨by simp [polyAdd], fun i hi => ?_⟩
  rw [polyAdd, getD_ofFn_nat _ _ _ hi]
  exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem polySub_isCanonical (a b : Poly) : IsCanonicalPoly (polySub a b) := by
  refine ⟨by simp [polySub], fun i hi => ?_⟩
  rw [polySub, getD_ofFn_nat _ _ _ hi]
  exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

private theorem nttStage_isCanonical {len kInit : Nat} {f : Poly}
    (hf : f.size = 256) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) :
    IsCanonicalPoly (nttStage len kInit f).1 := by
  rw [nttStage_eq_butterfly]
  dsimp only
  refine ⟨butterflyStage_size _ 0 hf hlen hdiv, fun idx hidx => ?_⟩
  rw [butterflyStage_getD _ 0 hf hlen hdiv hidx]
  dsimp only
  split_ifs <;> exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem polyNtt_isCanonical {f : Poly} (hf : f.size = 256) : IsCanonicalPoly (polyNtt f) := by
  unfold polyNtt
  have h1 := (nttStage_isCanonical (len := 128) (kInit := 1) hf (by decide) (by decide)).1
  rcases hf1 : nttStage 128 1 f with ⟨f1, k1⟩; rw [hf1] at h1; dsimp only at h1 ⊢
  have h2 := (nttStage_isCanonical (len := 64) (kInit := k1) h1 (by decide) (by decide)).1
  rcases hf2 : nttStage 64 k1 f1 with ⟨f2, k2⟩; rw [hf2] at h2; dsimp only at h2 ⊢
  have h3 := (nttStage_isCanonical (len := 32) (kInit := k2) h2 (by decide) (by decide)).1
  rcases hf3 : nttStage 32 k2 f2 with ⟨f3, k3⟩; rw [hf3] at h3; dsimp only at h3 ⊢
  have h4 := (nttStage_isCanonical (len := 16) (kInit := k3) h3 (by decide) (by decide)).1
  rcases hf4 : nttStage 16 k3 f3 with ⟨f4, k4⟩; rw [hf4] at h4; dsimp only at h4 ⊢
  have h5 := (nttStage_isCanonical (len := 8) (kInit := k4) h4 (by decide) (by decide)).1
  rcases hf5 : nttStage 8 k4 f4 with ⟨f5, k5⟩; rw [hf5] at h5; dsimp only at h5 ⊢
  have h6 := (nttStage_isCanonical (len := 4) (kInit := k5) h5 (by decide) (by decide)).1
  rcases hf6 : nttStage 4 k5 f5 with ⟨f6, k6⟩; rw [hf6] at h6; dsimp only at h6 ⊢
  have h7 := nttStage_isCanonical (len := 2) (kInit := k6) h6 (by decide) (by decide)
  rcases hf7 : nttStage 2 k6 f6 with ⟨f7, k7⟩; rw [hf7] at h7; exact h7

private theorem invNttStage_size {len kInit : Nat} {f : Poly}
    (hf : f.size = 256) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) :
    (invNttStage len kInit f).1.size = 256 := by
  rw [invNttStage_eq_butterfly]
  dsimp only
  exact butterflyStage_size _ 0 hf hlen hdiv

private theorem invNttStage_isCanonical {len kInit : Nat} {f : Poly}
    (hf : IsCanonicalPoly f) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) :
    IsCanonicalPoly (invNttStage len kInit f).1 := by
  rw [invNttStage_eq_butterfly]
  dsimp only
  refine ⟨butterflyStage_size _ 0 hf.1 hlen hdiv, fun idx hidx => ?_⟩
  rw [butterflyStage_getD _ 0 hf.1 hlen hdiv hidx]
  dsimp only
  split_ifs <;> exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem polyInvNtt_isCanonical {f : Poly} (hf : f.size = 256) : IsCanonicalPoly (polyInvNtt f) := by
  unfold polyInvNtt
  have s1 := invNttStage_size (len := 2) (kInit := 127) hf (by decide) (by decide)
  rcases e1 : invNttStage 2 127 f with ⟨f1, k1⟩; rw [e1] at s1; dsimp only at s1 ⊢
  have s2 := invNttStage_size (len := 4) (kInit := k1) s1 (by decide) (by decide)
  rcases e2 : invNttStage 4 k1 f1 with ⟨f2, k2⟩; rw [e2] at s2; dsimp only at s2 ⊢
  have s3 := invNttStage_size (len := 8) (kInit := k2) s2 (by decide) (by decide)
  rcases e3 : invNttStage 8 k2 f2 with ⟨f3, k3⟩; rw [e3] at s3; dsimp only at s3 ⊢
  have s4 := invNttStage_size (len := 16) (kInit := k3) s3 (by decide) (by decide)
  rcases e4 : invNttStage 16 k3 f3 with ⟨f4, k4⟩; rw [e4] at s4; dsimp only at s4 ⊢
  have s5 := invNttStage_size (len := 32) (kInit := k4) s4 (by decide) (by decide)
  rcases e5 : invNttStage 32 k4 f4 with ⟨f5, k5⟩; rw [e5] at s5; dsimp only at s5 ⊢
  have s6 := invNttStage_size (len := 64) (kInit := k5) s5 (by decide) (by decide)
  rcases e6 : invNttStage 64 k5 f5 with ⟨f6, k6⟩; rw [e6] at s6; dsimp only at s6 ⊢
  have s7 := invNttStage_size (len := 128) (kInit := k6) s6 (by decide) (by decide)
  rcases e7 : invNttStage 128 k6 f6 with ⟨f7, k7⟩; rw [e7] at s7; dsimp only at s7 ⊢
  refine ⟨by simp [s7], fun i hi => ?_⟩
  have hget : (f7.map fun c => (c * 3303) % mlkemQ).getD i 0 = (f7.getD i 0 * 3303) % mlkemQ := by
    simp [Array.getD, s7, hi]
  rw [hget]
  exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem polyNttMul_isCanonical (a b : Poly) : IsCanonicalPoly (polyNttMul a b) := by
  refine ⟨by simp [polyNttMul], fun i hi => ?_⟩
  rw [polyNttMul, getD_ofFn_nat _ _ _ hi]
  dsimp only
  split_ifs <;> exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem vecDotNtt_isCanonical (k : Nat) (a b : Array Poly) : IsCanonicalPoly (vecDotNtt k a b) := by
  unfold vecDotNtt
  induction k with
  | zero => exact zeroPoly_isCanonical
  | succ m _ =>
    rw [List.range_succ, List.foldl_append]
    simpa only [List.foldl_cons, List.foldl_nil] using polyAdd_isCanonical _ _

/-! ## 2. Ring Operations in `ZPoly := Fin 256 → ZMod 3329` -/

theorem toZPoly_zeroPoly : toZPoly zeroPoly = 0 := by
  funext i
  simp [toZPoly, zeroPoly, Array.getD, i.isLt]

theorem toZPoly_polyAdd (a b : Poly) : toZPoly (polyAdd a b) = toZPoly a + toZPoly b := by
  funext i
  simp only [toZPoly, polyAdd, getD_ofFn_nat _ _ _ i.isLt, Pi.add_apply, natCast_mod_q]
  push_cast
  rfl

theorem toZPoly_polySub (a b : Poly) : toZPoly (polySub a b) = toZPoly a - toZPoly b := by
  funext i
  have hle : b.getD i.val 0 % mlkemQ ≤ mlkemQ :=
    Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < mlkemQ))
  simp only [toZPoly, polySub, getD_ofFn_nat _ _ _ i.isLt, Pi.sub_apply,
    natCast_sub_q hle, natCast_mod_q]

theorem negacyclicMul_comm (a b : ZPoly) : negacyclicMul a b = negacyclicMul b a := by
  funext j
  unfold negacyclicMul
  let swapIdx : Fin 256 → Fin 256 := fun i =>
    if h : i.val ≤ j.val then ⟨j.val - i.val, by omega⟩ else ⟨256 + j.val - i.val, by omega⟩
  have hswap_invol : ∀ i : Fin 256, swapIdx (swapIdx i) = i := by
    intro i
    ext
    dsimp only [swapIdx]
    by_cases hij : i.val ≤ j.val
    · have h2 : j.val - i.val ≤ j.val := by omega
      simp only [hij, h2, ↓reduceDIte]
      omega
    · have h2 : ¬ (256 + j.val - i.val ≤ j.val) := by omega
      simp only [hij, h2, ↓reduceDIte]
      omega
  refine Finset.sum_bij' (fun i _ => swapIdx i) (fun i _ => swapIdx i)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
    (fun i _ => hswap_invol i) (fun i _ => hswap_invol i) ?_
  intro i _
  dsimp only [swapIdx]
  by_cases hij : i.val ≤ j.val
  · have h2 : j.val - i.val ≤ j.val := by omega
    have hi_eq : (⟨j.val - (j.val - i.val), by omega⟩ : Fin 256) = i := by ext; dsimp; omega
    simp only [hij, h2, ↓reduceDIte, hi_eq, mul_comm]
  · have h2 : ¬ (256 + j.val - i.val ≤ j.val) := by omega
    have hi_eq : (⟨256 + j.val - (256 + j.val - i.val), by omega⟩ : Fin 256) = i := by
      ext; dsimp; omega
    simp only [hij, h2, ↓reduceDIte, hi_eq, mul_comm]

theorem negacyclicMul_add_left (a b c : ZPoly) :
    negacyclicMul (a + b) c = negacyclicMul a c + negacyclicMul b c := by
  funext j
  simp only [negacyclicMul, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

theorem negacyclicMul_add_right (a b c : ZPoly) :
    negacyclicMul a (b + c) = negacyclicMul a b + negacyclicMul a c := by
  funext j
  simp only [negacyclicMul, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-! ## 3. Pure `ZPoly` Butterfly Stages, Inversion, and CRT Evaluation -/

private def zNttStage (len kInit : Nat) (f : ZPoly) : ZPoly :=
  fun idx =>
    let blk := idx.val / (2 * len)
    let z : ZMod mlkemQ := (fipsZetas.getD (kInit + blk) 0 : ZMod mlkemQ)
    if idx.val % (2 * len) < len then
      f idx + z * f ⟨(idx.val + len) % 256, Nat.mod_lt _ (by decide)⟩
    else
      f ⟨(idx.val - len) % 256, Nat.mod_lt _ (by decide)⟩ - z * f idx

private def zInvNttStage (len kInit : Nat) (f : ZPoly) : ZPoly :=
  fun idx =>
    let blk := idx.val / (2 * len)
    let z : ZMod mlkemQ := (fipsZetas.getD (kInit - blk) 0 : ZMod mlkemQ)
    if idx.val % (2 * len) < len then
      f idx + f ⟨(idx.val + len) % 256, Nat.mod_lt _ (by decide)⟩
    else
      z * (f idx - f ⟨(idx.val - len) % 256, Nat.mod_lt _ (by decide)⟩)

private theorem butterfly_add_lt {len idx : Nat}
    (hdiv : 2 * len ∣ 256) (hidx : idx < 256) (hrem : idx % (2 * len) < len) :
    idx + len < 256 := by
  rcases hdiv with ⟨q, hq⟩
  have hdiv_lt : idx / (2 * len) < q := by
    rw [hq] at hidx
    exact Nat.div_lt_of_lt_mul hidx
  have hd := Nat.div_add_mod idx (2 * len)
  have hle : (idx / (2 * len) + 1) * (2 * len) ≤ 256 := by
    rw [hq, Nat.mul_comm (2 * len) q]
    exact Nat.mul_le_mul_right (2 * len) hdiv_lt
  have hle' : (2 * len) * (idx / (2 * len)) + 2 * len ≤ 256 := by
    calc (2 * len) * (idx / (2 * len)) + 2 * len
        = (idx / (2 * len) + 1) * (2 * len) := by ring
      _ ≤ 256 := hle
  omega

private theorem toZPoly_nttStage {len kInit : Nat} {f : Poly}
    (hf : f.size = 256) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) :
    toZPoly (nttStage len kInit f).1 = zNttStage len kInit (toZPoly f) ∧
    (nttStage len kInit f).2 = kInit + 256 / (2 * len) := by
  rw [nttStage_eq_butterfly]
  refine ⟨?_, rfl⟩
  funext idx
  simp only [toZPoly, zNttStage, butterflyStage_getD _ 0 hf hlen hdiv idx.isLt]
  by_cases hlo : idx.val % (2 * len) < len
  · have hadd : idx.val + len < 256 := butterfly_add_lt hdiv idx.isLt hlo
    have hmod : (idx.val + len) % 256 = idx.val + len := Nat.mod_eq_of_lt hadd
    simp only [hlo, ↓reduceIte, natCast_mod_q, hmod]
    push_cast
    simp only [natCast_mod_q]
    push_cast
    rfl
  · have hmod : (idx.val - len) % 256 = idx.val - len := Nat.mod_eq_of_lt (by omega)
    have ht_le : (fipsZetas.getD (kInit + idx.val / (2 * len)) 0 * f.getD idx.val 0) % mlkemQ ≤ mlkemQ :=
      Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < mlkemQ))
    simp only [hlo, ↓reduceIte, natCast_sub_q ht_le, natCast_mod_q, hmod]
    push_cast
    rfl

private theorem toZPoly_invNttStage {len kInit : Nat} {f : Poly}
    (hf : IsCanonicalPoly f) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) :
    toZPoly (invNttStage len kInit f).1 = zInvNttStage len kInit (toZPoly f) ∧
    (invNttStage len kInit f).2 = kInit - 256 / (2 * len) := by
  rw [invNttStage_eq_butterfly]
  refine ⟨?_, rfl⟩
  funext idx
  simp only [toZPoly, zInvNttStage, butterflyStage_getD _ 0 hf.1 hlen hdiv idx.isLt]
  by_cases hlo : idx.val % (2 * len) < len
  · have hadd : idx.val + len < 256 := butterfly_add_lt hdiv idx.isLt hlo
    have hmod : (idx.val + len) % 256 = idx.val + len := Nat.mod_eq_of_lt hadd
    simp only [hlo, ↓reduceIte, natCast_mod_q, hmod]
    push_cast
    rfl
  · have hsub_lt : idx.val - len < 256 := by omega
    have hmod : (idx.val - len) % 256 = idx.val - len := Nat.mod_eq_of_lt hsub_lt
    have ht_le : f.getD (idx.val - len) 0 ≤ mlkemQ := Nat.le_of_lt (hf.2 _ hsub_lt)
    simp only [hlo, ↓reduceIte, natCast_mod_q, hmod]
    push_cast
    have hsub_cast :
        ((f.getD idx.val 0 + mlkemQ - f.getD (idx.val - len) 0 : Nat) : ZMod mlkemQ) =
          (f.getD idx.val 0 : ZMod mlkemQ) - (f.getD (idx.val - len) 0 : ZMod mlkemQ) := by
      rw [← natCast_mod_q, natCast_sub_q ht_le]
    rw [hsub_cast]

private def zNttPrefix : Nat → ZPoly → ZPoly
  | 0, f => f
  | s + 1, f => zNttStage (128 / 2 ^ s) (2 ^ s) (zNttPrefix s f)

private def zInvNttSuffix : Nat → ZPoly → ZPoly
  | 0, f => f
  | s + 1, f => zInvNttSuffix s (zInvNttStage (128 / 2 ^ s) (2 * 2 ^ s - 1) f)

private def zPolyNtt (f : ZPoly) : ZPoly := zNttPrefix 7 f

private def zPolyInvNtt (f : ZPoly) : ZPoly :=
  fun i => (3303 : ZMod mlkemQ) * zInvNttSuffix 7 f i

private theorem toZPoly_polyNtt_eq {f : Poly} (hf : f.size = 256) :
    toZPoly (polyNtt f) = zPolyNtt (toZPoly f) := by
  unfold polyNtt zPolyNtt
  have c1 := (nttStage_isCanonical (len := 128) (kInit := 1) hf (by decide) (by decide)).1
  rcases toZPoly_nttStage (len := 128) (kInit := 1) hf (by decide) (by decide) with ⟨z1, hk1⟩
  rcases e1 : nttStage 128 1 f with ⟨f1, k1⟩; rw [e1] at c1 z1 hk1; dsimp only at c1 z1 hk1 ⊢
  subst hk1
  have c2 := (nttStage_isCanonical (len := 64) (kInit := 2) c1 (by decide) (by decide)).1
  rcases toZPoly_nttStage (len := 64) (kInit := 2) c1 (by decide) (by decide) with ⟨z2, hk2⟩
  rcases e2 : nttStage 64 2 f1 with ⟨f2, k2⟩; rw [e2] at c2 z2 hk2; dsimp only at c2 z2 hk2 ⊢
  subst hk2
  have c3 := (nttStage_isCanonical (len := 32) (kInit := 4) c2 (by decide) (by decide)).1
  rcases toZPoly_nttStage (len := 32) (kInit := 4) c2 (by decide) (by decide) with ⟨z3, hk3⟩
  rcases e3 : nttStage 32 4 f2 with ⟨f3, k3⟩; rw [e3] at c3 z3 hk3; dsimp only at c3 z3 hk3 ⊢
  subst hk3
  have c4 := (nttStage_isCanonical (len := 16) (kInit := 8) c3 (by decide) (by decide)).1
  rcases toZPoly_nttStage (len := 16) (kInit := 8) c3 (by decide) (by decide) with ⟨z4, hk4⟩
  rcases e4 : nttStage 16 8 f3 with ⟨f4, k4⟩; rw [e4] at c4 z4 hk4; dsimp only at c4 z4 hk4 ⊢
  subst hk4
  have c5 := (nttStage_isCanonical (len := 8) (kInit := 16) c4 (by decide) (by decide)).1
  rcases toZPoly_nttStage (len := 8) (kInit := 16) c4 (by decide) (by decide) with ⟨z5, hk5⟩
  rcases e5 : nttStage 8 16 f4 with ⟨f5, k5⟩; rw [e5] at c5 z5 hk5; dsimp only at c5 z5 hk5 ⊢
  subst hk5
  have c6 := (nttStage_isCanonical (len := 4) (kInit := 32) c5 (by decide) (by decide)).1
  rcases toZPoly_nttStage (len := 4) (kInit := 32) c5 (by decide) (by decide) with ⟨z6, hk6⟩
  rcases e6 : nttStage 4 32 f5 with ⟨f6, k6⟩; rw [e6] at c6 z6 hk6; dsimp only at c6 z6 hk6 ⊢
  subst hk6
  rcases toZPoly_nttStage (len := 2) (kInit := 64) c6 (by decide) (by decide) with ⟨z7, _⟩
  rcases e7 : nttStage 2 64 f6 with ⟨f7, k7⟩; rw [e7] at z7; dsimp only at z7 ⊢
  rw [z7, z6, z5, z4, z3, z2, z1]
  rfl

private theorem toZPoly_polyInvNtt_eq {f : Poly} (hf : IsCanonicalPoly f) :
    toZPoly (polyInvNtt f) = zPolyInvNtt (toZPoly f) := by
  unfold polyInvNtt zPolyInvNtt
  have c1 := invNttStage_isCanonical (len := 2) (kInit := 127) hf (by decide) (by decide)
  rcases toZPoly_invNttStage (len := 2) (kInit := 127) hf (by decide) (by decide) with ⟨z1, hk1⟩
  rcases e1 : invNttStage 2 127 f with ⟨f1, k1⟩; rw [e1] at c1 z1 hk1; dsimp only at c1 z1 hk1 ⊢
  subst hk1
  have c2 := invNttStage_isCanonical (len := 4) (kInit := 63) c1 (by decide) (by decide)
  rcases toZPoly_invNttStage (len := 4) (kInit := 63) c1 (by decide) (by decide) with ⟨z2, hk2⟩
  rcases e2 : invNttStage 4 63 f1 with ⟨f2, k2⟩; rw [e2] at c2 z2 hk2; dsimp only at c2 z2 hk2 ⊢
  subst hk2
  have c3 := invNttStage_isCanonical (len := 8) (kInit := 31) c2 (by decide) (by decide)
  rcases toZPoly_invNttStage (len := 8) (kInit := 31) c2 (by decide) (by decide) with ⟨z3, hk3⟩
  rcases e3 : invNttStage 8 31 f2 with ⟨f3, k3⟩; rw [e3] at c3 z3 hk3; dsimp only at c3 z3 hk3 ⊢
  subst hk3
  have c4 := invNttStage_isCanonical (len := 16) (kInit := 15) c3 (by decide) (by decide)
  rcases toZPoly_invNttStage (len := 16) (kInit := 15) c3 (by decide) (by decide) with ⟨z4, hk4⟩
  rcases e4 : invNttStage 16 15 f3 with ⟨f4, k4⟩; rw [e4] at c4 z4 hk4; dsimp only at c4 z4 hk4 ⊢
  subst hk4
  have c5 := invNttStage_isCanonical (len := 32) (kInit := 7) c4 (by decide) (by decide)
  rcases toZPoly_invNttStage (len := 32) (kInit := 7) c4 (by decide) (by decide) with ⟨z5, hk5⟩
  rcases e5 : invNttStage 32 7 f4 with ⟨f5, k5⟩; rw [e5] at c5 z5 hk5; dsimp only at c5 z5 hk5 ⊢
  subst hk5
  have c6 := invNttStage_isCanonical (len := 64) (kInit := 3) c5 (by decide) (by decide)
  rcases toZPoly_invNttStage (len := 64) (kInit := 3) c5 (by decide) (by decide) with ⟨z6, hk6⟩
  rcases e6 : invNttStage 64 3 f5 with ⟨f6, k6⟩; rw [e6] at c6 z6 hk6; dsimp only at c6 z6 hk6 ⊢
  subst hk6
  have c7 := invNttStage_isCanonical (len := 128) (kInit := 1) c6 (by decide) (by decide)
  rcases toZPoly_invNttStage (len := 128) (kInit := 1) c6 (by decide) (by decide) with ⟨z7, _⟩
  rcases e7 : invNttStage 128 1 f6 with ⟨f7, k7⟩; rw [e7] at c7 z7; dsimp only at c7 z7 ⊢
  funext i
  have hget : (f7.map fun c => (c * 3303) % mlkemQ).getD i.val 0 = (f7.getD i.val 0 * 3303) % mlkemQ := by
    simp [Array.getD, c7.1, i.isLt]
  have hf7_eq : ((f7.getD i.val 0 : Nat) : ZMod mlkemQ) = zInvNttSuffix 7 (toZPoly f) i := by
    change toZPoly f7 i = zInvNttSuffix 7 (toZPoly f) i
    rw [z7, z6, z5, z4, z3, z2, z1]
    rfl
  simp only [toZPoly, hget, natCast_mod_q]
  push_cast
  rw [hf7_eq, mul_comm]

/-! ### Stage Linearity & Exact 7-Stage Butterfly Inversion -/

private theorem zNttStage_add (len kInit : Nat) (f g : ZPoly) :
    zNttStage len kInit (f + g) = zNttStage len kInit f + zNttStage len kInit g := by
  funext idx
  simp only [zNttStage, Pi.add_apply]
  split_ifs <;> ring

private theorem zNttStage_smul (len kInit : Nat) (c : ZMod mlkemQ) (f : ZPoly) :
    zNttStage len kInit (c • f) = c • zNttStage len kInit f := by
  funext idx
  simp only [zNttStage, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

private theorem zInvNttStage_add (len kInit : Nat) (f g : ZPoly) :
    zInvNttStage len kInit (f + g) = zInvNttStage len kInit f + zInvNttStage len kInit g := by
  funext idx
  simp only [zInvNttStage, Pi.add_apply]
  split_ifs <;> ring

private theorem zInvNttStage_smul (len kInit : Nat) (c : ZMod mlkemQ) (f : ZPoly) :
    zInvNttStage len kInit (c • f) = c • zInvNttStage len kInit f := by
  funext idx
  simp only [zInvNttStage, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

private theorem zNttPrefix_add (n : Nat) (f g : ZPoly) :
    zNttPrefix n (f + g) = zNttPrefix n f + zNttPrefix n g := by
  induction n with
  | zero => rfl
  | succ s ih => simp only [zNttPrefix, ih, zNttStage_add]

private theorem zNttPrefix_smul (n : Nat) (c : ZMod mlkemQ) (f : ZPoly) :
    zNttPrefix n (c • f) = c • zNttPrefix n f := by
  induction n with
  | zero => rfl
  | succ s ih => simp only [zNttPrefix, ih, zNttStage_smul]

private theorem zInvNttSuffix_add (n : Nat) (f g : ZPoly) :
    zInvNttSuffix n (f + g) = zInvNttSuffix n f + zInvNttSuffix n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ s ih => simp only [zInvNttSuffix, zInvNttStage_add, ih]

private theorem zInvNttSuffix_smul (n : Nat) (c : ZMod mlkemQ) (f : ZPoly) :
    zInvNttSuffix n (c • f) = c • zInvNttSuffix n f := by
  induction n generalizing f with
  | zero => rfl
  | succ s ih => simp only [zInvNttSuffix, zInvNttStage_smul, ih]

private def zetaNat (k : Nat) : Nat := (17 ^ bitRev7 k) % 3329

private theorem fipsZetas_getD_eq_zetaNat {k : Nat} (hk : k < 128) :
    fipsZetas.getD k 0 = zetaNat k := by
  rw [fipsZetas, getD_ofFn_nat _ _ _ hk]
  rfl

-- Seal the 128-entry `fipsZetas` table so `simp` / `isDefEq` never unroll `fipsZetas`
-- during symbolic `ZPoly` algebra.
attribute [local irreducible] fipsZetas

private theorem add_congr_eq {α : Type} [Add α] {a₁ a₂ b₁ b₂ : α}
    (ha : a₁ = a₂) (hb : b₁ = b₂) : a₁ + b₁ = a₂ + b₂ := by
  rw [ha, hb]

private theorem zetaNat_inv_pair :
    ∀ s : Fin 7, ∀ blk : Fin 64, blk.val < 2 ^ s.val →
      (zetaNat (2 ^ s.val + blk.val) * zetaNat (2 * 2 ^ s.val - 1 - blk.val)) % 3329 = 3328 := by
  decide

private theorem fipsZetas_inv_pair {s blk : Nat} (hs : s < 7) (hblk : blk < 2 ^ s) :
    (fipsZetas.getD (2 ^ s + blk) 0 : ZMod mlkemQ) *
      (fipsZetas.getD (2 * 2 ^ s - 1 - blk) 0 : ZMod mlkemQ) = -1 := by
  have hs64 : 2 ^ s ≤ 64 := by
    have : ∀ x : Fin 7, 2 ^ x.val ≤ 64 := by decide
    exact this ⟨s, hs⟩
  have hk1 : 2 ^ s + blk < 128 := by omega
  have hk2 : 2 * 2 ^ s - 1 - blk < 128 := by omega
  rw [fipsZetas_getD_eq_zetaNat hk1, fipsZetas_getD_eq_zetaNat hk2]
  have hnat := zetaNat_inv_pair ⟨s, hs⟩ ⟨blk, by omega⟩ hblk
  have hcast :
      (((zetaNat (2 ^ s + blk) * zetaNat (2 * 2 ^ s - 1 - blk)) % mlkemQ : Nat) : ZMod mlkemQ) =
        ((3328 : Nat) : ZMod mlkemQ) :=
    congrArg Nat.cast hnat
  rw [natCast_mod_q] at hcast
  push_cast at hcast
  have h3328 : ((3328 : Nat) : ZMod mlkemQ) = -1 := by decide
  exact hcast.trans h3328

private theorem stage_arith_props (s : Fin 7) :
    let len := 128 / 2 ^ s.val
    0 < len ∧ 2 * len = 256 / 2 ^ s.val ∧ len = 256 / 2 ^ (s.val + 1) ∧
    (2 * len) * 2 ^ s.val = 256 ∧ len * 2 ^ (s.val + 1) = 256 := by
  revert s
  decide

private theorem butterfly_pair_lo {len idx : Nat} (hlen : 0 < len) (hlo : idx % (2 * len) < len) :
    (idx + len) / (2 * len) = idx / (2 * len) ∧
    ¬ ((idx + len) % (2 * len) < len) ∧
    idx / len = 2 * (idx / (2 * len)) ∧
    idx % len = idx % (2 * len) ∧
    (idx + len) % (2 * len) = idx % len + len := by
  set q := idx / (2 * len)
  set r := idx % (2 * len)
  have hd : 2 * len * q + r = idx := Nat.div_add_mod idx (2 * len)
  have hidx_len : idx = r + len * (2 * q) := by
    calc idx = 2 * len * q + r := hd.symm
      _ = r + len * (2 * q) := by ring
  have hadd_2len : idx + len = (r + len) + (2 * len) * q := by
    calc idx + len = (2 * len * q + r) + len := by rw [hd]
      _ = (r + len) + (2 * len) * q := by ring
  have hr_div_len : r / len = 0 := Nat.div_eq_of_lt hlo
  have hr_mod_len : r % len = r := Nat.mod_eq_of_lt hlo
  have hrl_lt : r + len < 2 * len := by omega
  have hrl_div : (r + len) / (2 * len) = 0 := Nat.div_eq_of_lt hrl_lt
  have hrl_mod : (r + len) % (2 * len) = r + len := Nat.mod_eq_of_lt hrl_lt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hadd_2len, Nat.add_mul_div_left _ _ (by omega : 0 < 2 * len), hrl_div, Nat.zero_add]
  · rw [hadd_2len, Nat.add_mul_mod_self_left, hrl_mod]; omega
  · rw [hidx_len, Nat.add_mul_div_left _ _ hlen, hr_div_len, Nat.zero_add]
  · rw [hidx_len, Nat.add_mul_mod_self_left, hr_mod_len]
  · rw [hadd_2len, Nat.add_mul_mod_self_left, hrl_mod, hidx_len, Nat.add_mul_mod_self_left, hr_mod_len]

private theorem butterfly_pair_hi {len idx : Nat} (hlen : 0 < len) (hhi : ¬ (idx % (2 * len) < len)) :
    len ≤ idx ∧
    (idx - len) / (2 * len) = idx / (2 * len) ∧
    (idx - len) % (2 * len) < len ∧
    idx / len = 2 * (idx / (2 * len)) + 1 ∧
    (idx - len) % (2 * len) = idx % len ∧
    idx % (2 * len) = idx % len + len := by
  set q := idx / (2 * len)
  set r := idx % (2 * len)
  have hr_lt : r < 2 * len := Nat.mod_lt idx (by omega)
  have hd : 2 * len * q + r = idx := Nat.div_add_mod idx (2 * len)
  have hlen_le_idx : len ≤ idx := by omega
  set r' := r - len
  have hr'_lt : r' < len := by omega
  have hr_eq : r = r' + len := by omega
  have hidx_len : idx = r' + len * (2 * q + 1) := by
    calc idx = 2 * len * q + (r' + len) := by rw [← hr_eq, hd]
      _ = r' + len * (2 * q + 1) := by ring
  have hsub_2len : idx - len = r' + (2 * len) * q := by omega
  have hr'_div_len : r' / len = 0 := Nat.div_eq_of_lt hr'_lt
  have hr'_mod_len : r' % len = r' := Nat.mod_eq_of_lt hr'_lt
  have hr'_div_2len : r' / (2 * len) = 0 := Nat.div_eq_of_lt (by omega)
  have hr'_mod_2len : r' % (2 * len) = r' := Nat.mod_eq_of_lt (by omega)
  refine ⟨hlen_le_idx, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsub_2len, Nat.add_mul_div_left _ _ (by omega : 0 < 2 * len), hr'_div_2len, Nat.zero_add]
  · rw [hsub_2len, Nat.add_mul_mod_self_left, hr'_mod_2len]; exact hr'_lt
  · rw [hidx_len, Nat.add_mul_div_left _ _ hlen, hr'_div_len, Nat.zero_add]
  · rw [hsub_2len, Nat.add_mul_mod_self_left, hr'_mod_2len, hidx_len, Nat.add_mul_mod_self_left, hr'_mod_len]
  · rw [hidx_len, Nat.add_mul_mod_self_left, hr'_mod_len]; exact hr_eq

private theorem zInvNttStage_zNttStage {s : Nat} (hs : s < 7) (f : ZPoly) :
    zInvNttStage (128 / 2 ^ s) (2 * 2 ^ s - 1) (zNttStage (128 / 2 ^ s) (2 ^ s) f) =
      (2 : ZMod mlkemQ) • f := by
  obtain ⟨hlen, _, _, hmul, _⟩ := stage_arith_props ⟨s, hs⟩
  set len := 128 / 2 ^ s
  have hdiv : 2 * len ∣ 256 := ⟨2 ^ s, hmul.symm⟩
  funext idx
  have hblk_lt : idx.val / (2 * len) < 2 ^ s := by
    have hidx : idx.val < (2 * len) * 2 ^ s := by rw [hmul]; exact idx.isLt
    exact Nat.div_lt_of_lt_mul hidx
  have hzeta := fipsZetas_inv_pair hs hblk_lt
  change zInvNttStage len (2 * 2 ^ s - 1) (zNttStage len (2 ^ s) f) idx = 2 * f idx
  by_cases hlo : idx.val % (2 * len) < len
  · obtain ⟨hdiv_hi, hrem_hi, _, _, _⟩ := butterfly_pair_lo hlen hlo
    have hadd_lt : idx.val + len < 256 := butterfly_add_lt hdiv idx.isLt hlo
    have hmod_hi : (idx.val + len) % 256 = idx.val + len := Nat.mod_eq_of_lt hadd_lt
    let idxHi : Fin 256 := ⟨idx.val + len, hadd_lt⟩
    have hfin_hi : (⟨(idx.val + len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idxHi := by
      ext; exact hmod_hi
    have hsub_back :
        (⟨(idxHi.val - len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idx := by
      ext; dsimp [idxHi]; rw [Nat.add_sub_cancel, Nat.mod_eq_of_lt idx.isLt]
    simp only [zInvNttStage, hlo, ↓reduceIte, hfin_hi]
    have hd_hi : idxHi.val / (2 * len) = idx.val / (2 * len) := hdiv_hi
    have hr_hi : ¬ (idxHi.val % (2 * len) < len) := hrem_hi
    simp only [zNttStage, hlo, hr_hi, hd_hi, ↓reduceIte, hfin_hi, hsub_back]
    ring
  · obtain ⟨hlen_le, hdiv_lo, hrem_lo, _, _, _⟩ := butterfly_pair_hi hlen hlo
    have hsub_lt : idx.val - len < 256 := by omega
    have hmod_lo : (idx.val - len) % 256 = idx.val - len := Nat.mod_eq_of_lt hsub_lt
    let idxLo : Fin 256 := ⟨idx.val - len, hsub_lt⟩
    have hfin_lo : (⟨(idx.val - len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idxLo := by
      ext; exact hmod_lo
    have hadd_back :
        (⟨(idxLo.val + len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idx := by
      ext; dsimp [idxLo]; rw [Nat.sub_add_cancel hlen_le, Nat.mod_eq_of_lt idx.isLt]
    simp only [zInvNttStage, hlo, ↓reduceIte, hfin_lo]
    have hd_lo : idxLo.val / (2 * len) = idx.val / (2 * len) := hdiv_lo
    have hr_lo : idxLo.val % (2 * len) < len := hrem_lo
    simp only [zNttStage, hlo, hr_lo, hd_lo, ↓reduceIte, hfin_lo, hadd_back]
    set z1 : ZMod mlkemQ := (fipsZetas.getD (2 ^ s + idx.val / (2 * len)) 0 : ZMod mlkemQ)
    set z2 : ZMod mlkemQ := (fipsZetas.getD (2 * 2 ^ s - 1 - idx.val / (2 * len)) 0 : ZMod mlkemQ)
    calc z2 * (f idxLo - z1 * f idx - (f idxLo + z1 * f idx))
        = -2 * (z1 * z2) * f idx := by ring
      _ = -2 * (-1) * f idx := by rw [hzeta]
      _ = 2 * f idx := by ring

private theorem zNttStage_zInvNttStage {s : Nat} (hs : s < 7) (f : ZPoly) :
    zNttStage (128 / 2 ^ s) (2 ^ s) (zInvNttStage (128 / 2 ^ s) (2 * 2 ^ s - 1) f) =
      (2 : ZMod mlkemQ) • f := by
  obtain ⟨hlen, _, _, hmul, _⟩ := stage_arith_props ⟨s, hs⟩
  set len := 128 / 2 ^ s
  have hdiv : 2 * len ∣ 256 := ⟨2 ^ s, hmul.symm⟩
  funext idx
  have hblk_lt : idx.val / (2 * len) < 2 ^ s := by
    have hidx : idx.val < (2 * len) * 2 ^ s := by rw [hmul]; exact idx.isLt
    exact Nat.div_lt_of_lt_mul hidx
  have hzeta := fipsZetas_inv_pair hs hblk_lt
  change zNttStage len (2 ^ s) (zInvNttStage len (2 * 2 ^ s - 1) f) idx = 2 * f idx
  by_cases hlo : idx.val % (2 * len) < len
  · obtain ⟨hdiv_hi, hrem_hi, _, _, _⟩ := butterfly_pair_lo hlen hlo
    have hadd_lt : idx.val + len < 256 := butterfly_add_lt hdiv idx.isLt hlo
    have hmod_hi : (idx.val + len) % 256 = idx.val + len := Nat.mod_eq_of_lt hadd_lt
    let idxHi : Fin 256 := ⟨idx.val + len, hadd_lt⟩
    have hfin_hi : (⟨(idx.val + len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idxHi := by
      ext; exact hmod_hi
    have hsub_back :
        (⟨(idxHi.val - len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idx := by
      ext; dsimp [idxHi]; rw [Nat.add_sub_cancel, Nat.mod_eq_of_lt idx.isLt]
    simp only [zNttStage, hlo, ↓reduceIte, hfin_hi]
    have hd_hi : idxHi.val / (2 * len) = idx.val / (2 * len) := hdiv_hi
    have hr_hi : ¬ (idxHi.val % (2 * len) < len) := hrem_hi
    simp only [zInvNttStage, hlo, hr_hi, hd_hi, ↓reduceIte, hfin_hi, hsub_back]
    set z1 : ZMod mlkemQ := (fipsZetas.getD (2 ^ s + idx.val / (2 * len)) 0 : ZMod mlkemQ)
    set z2 : ZMod mlkemQ := (fipsZetas.getD (2 * 2 ^ s - 1 - idx.val / (2 * len)) 0 : ZMod mlkemQ)
    calc f idx + f idxHi + z1 * (z2 * (f idxHi - f idx))
        = f idx + f idxHi + (z1 * z2) * (f idxHi - f idx) := by ring
      _ = f idx + f idxHi + (-1) * (f idxHi - f idx) := by rw [hzeta]
      _ = 2 * f idx := by ring
  · obtain ⟨hlen_le, hdiv_lo, hrem_lo, _, _, _⟩ := butterfly_pair_hi hlen hlo
    have hsub_lt : idx.val - len < 256 := by omega
    have hmod_lo : (idx.val - len) % 256 = idx.val - len := Nat.mod_eq_of_lt hsub_lt
    let idxLo : Fin 256 := ⟨idx.val - len, hsub_lt⟩
    have hfin_lo : (⟨(idx.val - len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idxLo := by
      ext; exact hmod_lo
    have hadd_back :
        (⟨(idxLo.val + len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idx := by
      ext; dsimp [idxLo]; rw [Nat.sub_add_cancel hlen_le, Nat.mod_eq_of_lt idx.isLt]
    simp only [zNttStage, hlo, ↓reduceIte, hfin_lo]
    have hr_lo : idxLo.val % (2 * len) < len := hrem_lo
    simp only [zInvNttStage, hlo, hr_lo, ↓reduceIte, hfin_lo, hadd_back]
    set z1 : ZMod mlkemQ := (fipsZetas.getD (2 ^ s + idx.val / (2 * len)) 0 : ZMod mlkemQ)
    set z2 : ZMod mlkemQ := (fipsZetas.getD (2 * 2 ^ s - 1 - idx.val / (2 * len)) 0 : ZMod mlkemQ)
    calc f idxLo + f idx - z1 * (z2 * (f idx - f idxLo))
        = f idxLo + f idx - (z1 * z2) * (f idx - f idxLo) := by ring
      _ = f idxLo + f idx - (-1) * (f idx - f idxLo) := by rw [hzeta]
      _ = 2 * f idx := by ring

private theorem zInvNttSuffix_zNttPrefix {n : Nat} (hn : n ≤ 7) (f : ZPoly) :
    zInvNttSuffix n (zNttPrefix n f) = ((2 : ZMod mlkemQ) ^ n) • f := by
  induction n with
  | zero => funext idx; simp [zInvNttSuffix, zNttPrefix]
  | succ s ih =>
    simp only [zInvNttSuffix, zNttPrefix, zInvNttStage_zNttStage (by omega : s < 7),
      zInvNttSuffix_smul, ih (by omega)]
    funext idx
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

private theorem zNttPrefix_zInvNttSuffix {n : Nat} (hn : n ≤ 7) (f : ZPoly) :
    zNttPrefix n (zInvNttSuffix n f) = ((2 : ZMod mlkemQ) ^ n) • f := by
  induction n generalizing f with
  | zero => funext idx; simp [zInvNttSuffix, zNttPrefix]
  | succ s ih =>
    simp only [zInvNttSuffix, zNttPrefix, ih (by omega), zNttStage_smul,
      zNttStage_zInvNttStage (by omega : s < 7)]
    funext idx
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

private theorem zPolyInvNtt_zPolyNtt (f : ZPoly) : zPolyInvNtt (zPolyNtt f) = f := by
  unfold zPolyInvNtt zPolyNtt
  rw [zInvNttSuffix_zNttPrefix (Nat.le_refl 7)]
  funext idx
  simp only [Pi.smul_apply, smul_eq_mul]
  have hinv : (3303 : ZMod mlkemQ) * (2 : ZMod mlkemQ) ^ 7 = 1 := by decide
  calc (3303 : ZMod mlkemQ) * ((2 : ZMod mlkemQ) ^ 7 * f idx)
      = ((3303 : ZMod mlkemQ) * (2 : ZMod mlkemQ) ^ 7) * f idx := by ring
    _ = 1 * f idx := by rw [hinv]
    _ = f idx := one_mul _

private theorem zPolyNtt_zPolyInvNtt (f : ZPoly) : zPolyNtt (zPolyInvNtt f) = f := by
  have hsmul : zPolyInvNtt f = (3303 : ZMod mlkemQ) • zInvNttSuffix 7 f := rfl
  rw [hsmul, zPolyNtt, zNttPrefix_smul, zNttPrefix_zInvNttSuffix (Nat.le_refl 7)]
  funext idx
  simp only [Pi.smul_apply, smul_eq_mul]
  have hinv : (3303 : ZMod mlkemQ) * (2 : ZMod mlkemQ) ^ 7 = 1 := by decide
  calc (3303 : ZMod mlkemQ) * ((2 : ZMod mlkemQ) ^ 7 * f idx)
      = ((3303 : ZMod mlkemQ) * (2 : ZMod mlkemQ) ^ 7) * f idx := by ring
    _ = 1 * f idx := by rw [hinv]
    _ = f idx := one_mul _

/-! ### 7-Stage CRT Degree-2 Evaluation & Quadratic Extension `Quad γ` -/

private def stageRootNat (s blk : Nat) : Nat :=
  if s == 0 then 3328
  else
    let bz := zetaNat (2 ^ (s - 1) + blk / 2)
    if blk % 2 == 0 then bz else (3329 - bz) % 3329

private def stageRoot (s blk : Nat) : ZMod mlkemQ :=
  if s = 0 then -1
  else
    let bz : ZMod mlkemQ := (fipsZetas.getD (2 ^ (s - 1) + blk / 2) 0 : ZMod mlkemQ)
    if blk % 2 = 0 then bz else -bz

private theorem stageRoot_eq_nat {s blk : Nat} (hs : s ≤ 7) (hblk : blk < 2 ^ s) :
    stageRoot s blk = (stageRootNat s blk : ZMod mlkemQ) := by
  rcases s with _ | s'
  · dsimp [stageRoot, stageRootNat]
    decide
  · have hk_lt : 2 ^ s' + blk / 2 < 128 := by
      have hpow : 2 ^ (s' + 1) ≤ 128 := by
        have : ∀ x : Fin 7, 2 ^ (x.val + 1) ≤ 128 := by decide
        exact this ⟨s', by omega⟩
      omega
    have hbz_le : zetaNat (2 ^ s' + blk / 2) ≤ mlkemQ :=
      Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 3329))
    by_cases hpar : blk % 2 = 0
    · simp only [stageRoot, stageRootNat, Nat.succ_ne_zero, ↓reduceIte,
        show (s' + 1 == 0) = false from rfl, Bool.false_eq_true, Nat.add_sub_cancel,
        hpar, beq_self_eq_true, fipsZetas_getD_eq_zetaNat hk_lt]
    · have hbeq : (blk % 2 == 0) = false := Bool.eq_false_iff.mpr (by simpa using hpar)
      have hsub :
          (((3329 - zetaNat (2 ^ s' + blk / 2)) % 3329 : Nat) : ZMod mlkemQ) =
            -(zetaNat (2 ^ s' + blk / 2) : ZMod mlkemQ) := by
        simpa using natCast_sub_q (x := 0) hbz_le
      simp only [stageRoot, stageRootNat, Nat.succ_ne_zero, ↓reduceIte,
        show (s' + 1 == 0) = false from rfl, Bool.false_eq_true, Nat.add_sub_cancel,
        hpar, hbeq, fipsZetas_getD_eq_zetaNat hk_lt, hsub]

private theorem stageRootNat_sq :
    ∀ s : Fin 7, ∀ blk : Fin 128, blk.val < 2 ^ (s.val + 1) →
      (stageRootNat (s.val + 1) blk.val ^ 2) % 3329 = stageRootNat s.val (blk.val / 2) % 3329 := by
  decide

private theorem stageRoot_sq {s blk : Nat} (hs : s < 7) (hblk : blk < 2 ^ (s + 1)) :
    stageRoot (s + 1) blk ^ 2 = stageRoot s (blk / 2) := by
  have h128 : 2 ^ (s + 1) ≤ 128 := by
    have : ∀ x : Fin 7, 2 ^ (x.val + 1) ≤ 128 := by decide
    exact this ⟨s, hs⟩
  rw [stageRoot_eq_nat (by omega) hblk, stageRoot_eq_nat (by omega) (by omega)]
  have hnat := stageRootNat_sq ⟨s, hs⟩ ⟨blk, by omega⟩ hblk
  have hcast :
      (((stageRootNat (s + 1) blk ^ 2) % mlkemQ : Nat) : ZMod mlkemQ) =
        ((stageRootNat s (blk / 2) % mlkemQ : Nat) : ZMod mlkemQ) :=
    congrArg Nat.cast hnat
  rw [natCast_mod_q, natCast_mod_q] at hcast
  push_cast at hcast
  exact hcast

private theorem stageRoot7_pow_128_nat :
    ∀ p : Fin 128, (stageRootNat 7 p.val ^ 128) % 3329 = 3328 := by
  decide

private theorem stageRoot7_pow_128 (p : Fin 128) :
    stageRoot 7 p.val ^ 128 = -1 := by
  rw [stageRoot_eq_nat (Nat.le_refl 7) p.isLt]
  have hnat := stageRoot7_pow_128_nat p
  have hcast : (((stageRootNat 7 p.val ^ 128) % mlkemQ : Nat) : ZMod mlkemQ) =
      ((3328 : Nat) : ZMod mlkemQ) :=
    congrArg Nat.cast hnat
  rw [natCast_mod_q] at hcast
  push_cast at hcast
  have h3328 : ((3328 : Nat) : ZMod mlkemQ) = -1 := by decide
  exact hcast.trans h3328

private theorem sum_range_even_odd {M : Type} [AddCommMonoid M] (n : Nat) (g : Nat → M) :
    ∑ k ∈ Finset.range (2 * n), g k =
      (∑ m ∈ Finset.range n, g (2 * m)) + (∑ m ∈ Finset.range n, g (2 * m + 1)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ac_rfl

private theorem zNttPrefix_crt {s : Nat} (hs : s ≤ 7) (f : ZPoly) (idx : Fin 256) :
    let w := 256 / 2 ^ s
    zNttPrefix s f idx =
      ∑ m ∈ Finset.range (2 ^ s),
        f ⟨(m * w + idx.val % w) % 256, Nat.mod_lt _ (by decide)⟩ *
          stageRoot s (idx.val / w) ^ m := by
  induction s generalizing idx with
  | zero =>
    dsimp only [zNttPrefix]
    have hmod : idx.val % 256 = idx.val := Nat.mod_eq_of_lt idx.isLt
    simp [hmod]
  | succ s ih =>
    have hs7 : s < 7 := by omega
    obtain ⟨hlen, hw_old, hw_new, hmul_old, hmul_new⟩ := stage_arith_props ⟨s, hs7⟩
    set len := 128 / 2 ^ s
    have hdiv : 2 * len ∣ 256 := ⟨2 ^ s, hmul_old.symm⟩
    have hblk_new_lt : idx.val / len < 2 ^ (s + 1) := by
      have hidx : idx.val < len * 2 ^ (s + 1) := by rw [hmul_new]; exact idx.isLt
      exact Nat.div_lt_of_lt_mul hidx
    have hpow2 : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    dsimp only [zNttPrefix]
    rw [← hw_new]
    change zNttStage len (2 ^ s) (zNttPrefix s f) idx =
      ∑ m ∈ Finset.range (2 ^ (s + 1)),
        f ⟨(m * len + idx.val % len) % 256, Nat.mod_lt _ (by decide)⟩ *
          stageRoot (s + 1) (idx.val / len) ^ m
    have hrhs_split :
        (∑ m ∈ Finset.range (2 ^ (s + 1)),
          f ⟨(m * len + idx.val % len) % 256, Nat.mod_lt _ (by decide)⟩ *
            stageRoot (s + 1) (idx.val / len) ^ m) =
        (∑ m ∈ Finset.range (2 ^ s),
          f ⟨(2 * m * len + idx.val % len) % 256, Nat.mod_lt _ (by decide)⟩ *
            stageRoot (s + 1) (idx.val / len) ^ (2 * m)) +
        (∑ m ∈ Finset.range (2 ^ s),
          f ⟨((2 * m + 1) * len + idx.val % len) % 256, Nat.mod_lt _ (by decide)⟩ *
            stageRoot (s + 1) (idx.val / len) ^ (2 * m + 1)) := by
      have hrange : Finset.range (2 ^ (s + 1)) = Finset.range (2 * 2 ^ s) := congrArg Finset.range hpow2
      rw [hrange, sum_range_even_odd]
    rw [hrhs_split]
    by_cases hlo : idx.val % (2 * len) < len
    · obtain ⟨hdiv_hi, _, hblk_new, hrem_lo, hrem_hi⟩ := butterfly_pair_lo hlen hlo
      have hadd_lt : idx.val + len < 256 := butterfly_add_lt hdiv idx.isLt hlo
      have hmod_hi : (idx.val + len) % 256 = idx.val + len := Nat.mod_eq_of_lt hadd_lt
      let idxHi : Fin 256 := ⟨idx.val + len, hadd_lt⟩
      have hfin_hi : (⟨(idx.val + len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idxHi := by
        ext; exact hmod_hi
      have hpar : (idx.val / len) % 2 = 0 := by rw [hblk_new]; omega
      have hhalf : (idx.val / len) / 2 = idx.val / (2 * len) := by rw [hblk_new]; omega
      have hroot_pos : stageRoot (s + 1) (idx.val / len) =
          (fipsZetas.getD (2 ^ s + idx.val / (2 * len)) 0 : ZMod mlkemQ) := by
        unfold stageRoot
        rw [ite_eq_right (Nat.succ_ne_zero s)]
        dsimp only
        rw [ite_eq_left hpar, Nat.add_sub_cancel, hhalf]
      have hsq : stageRoot s (idx.val / (2 * len)) = stageRoot (s + 1) (idx.val / len) ^ 2 := by
        rw [← hhalf, stageRoot_sq hs7 hblk_new_lt]
      have hd_hi : idxHi.val / (2 * len) = idx.val / (2 * len) := hdiv_hi
      have hr_hi : idxHi.val % (2 * len) = idx.val % len + len := hrem_hi
      simp only [zNttStage, hlo, ↓reduceIte, hfin_hi, ih (by omega) idx, ih (by omega) idxHi]
      simp only [← hw_old, hd_hi, ← hrem_lo, hr_hi, ← hroot_pos, hsq, Finset.mul_sum]
      refine add_congr_eq ?_ ?_
      · refine Finset.sum_congr rfl fun m _ => ?_
        have hidx_eq : 2 * m * len + idx.val % len = m * (2 * len) + idx.val % len := by ring
        rw [hidx_eq, pow_mul]
      · refine Finset.sum_congr rfl fun m _ => ?_
        have hidx_eq : (2 * m + 1) * len + idx.val % len = m * (2 * len) + (idx.val % len + len) := by ring
        rw [hidx_eq]
        set ρ := stageRoot (s + 1) (idx.val / len)
        have hpow_odd : ρ * (ρ ^ 2) ^ m = ρ ^ (2 * m + 1) := by ring
        calc ρ * (f ⟨(m * (2 * len) + (idx.val % len + len)) % 256, _⟩ * (ρ ^ 2) ^ m)
            = f ⟨(m * (2 * len) + (idx.val % len + len)) % 256, _⟩ * (ρ * (ρ ^ 2) ^ m) := by ring
          _ = f ⟨(m * (2 * len) + (idx.val % len + len)) % 256, _⟩ * ρ ^ (2 * m + 1) := by rw [hpow_odd]
    · obtain ⟨_, hdiv_lo, _, hblk_new, hrem_lo, hrem_hi⟩ := butterfly_pair_hi hlen hlo
      have hsub_lt : idx.val - len < 256 := by omega
      have hmod_lo : (idx.val - len) % 256 = idx.val - len := Nat.mod_eq_of_lt hsub_lt
      let idxLo : Fin 256 := ⟨idx.val - len, hsub_lt⟩
      have hfin_lo : (⟨(idx.val - len) % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = idxLo := by
        ext; exact hmod_lo
      have hpar : (idx.val / len) % 2 ≠ 0 := by rw [hblk_new]; omega
      have hhalf : (idx.val / len) / 2 = idx.val / (2 * len) := by rw [hblk_new]; omega
      have hroot_neg : stageRoot (s + 1) (idx.val / len) =
          -(fipsZetas.getD (2 ^ s + idx.val / (2 * len)) 0 : ZMod mlkemQ) := by
        unfold stageRoot
        rw [ite_eq_right (Nat.succ_ne_zero s)]
        dsimp only
        rw [ite_eq_right hpar, Nat.add_sub_cancel, hhalf]
      have hzeta_eq : (fipsZetas.getD (2 ^ s + idx.val / (2 * len)) 0 : ZMod mlkemQ) =
          -stageRoot (s + 1) (idx.val / len) := by
        rw [hroot_neg, neg_neg]
      have hsq : stageRoot s (idx.val / (2 * len)) = stageRoot (s + 1) (idx.val / len) ^ 2 := by
        rw [← hhalf, stageRoot_sq hs7 hblk_new_lt]
      have hd_lo : idxLo.val / (2 * len) = idx.val / (2 * len) := hdiv_lo
      have hr_lo : idxLo.val % (2 * len) = idx.val % len := hrem_lo
      simp only [zNttStage, hlo, ↓reduceIte, hfin_lo, ih (by omega) idxLo, ih (by omega) idx]
      simp only [← hw_old, hd_lo, hr_lo, hrem_hi, hzeta_eq, hsq]
      have hsub_neg : ∀ x y : ZMod mlkemQ, x - (-stageRoot (s + 1) (idx.val / len)) * y =
          x + stageRoot (s + 1) (idx.val / len) * y := fun x y => by ring
      rw [hsub_neg, Finset.mul_sum]
      refine add_congr_eq ?_ ?_
      · refine Finset.sum_congr rfl fun m _ => ?_
        have hidx_eq : 2 * m * len + idx.val % len = m * (2 * len) + idx.val % len := by ring
        rw [hidx_eq, pow_mul]
      · refine Finset.sum_congr rfl fun m _ => ?_
        have hidx_eq : (2 * m + 1) * len + idx.val % len = m * (2 * len) + (idx.val % len + len) := by ring
        rw [hidx_eq]
        set ρ := stageRoot (s + 1) (idx.val / len)
        have hpow_odd : ρ * (ρ ^ 2) ^ m = ρ ^ (2 * m + 1) := by ring
        calc ρ * (f ⟨(m * (2 * len) + (idx.val % len + len)) % 256, _⟩ * (ρ ^ 2) ^ m)
            = f ⟨(m * (2 * len) + (idx.val % len + len)) % 256, _⟩ * (ρ * (ρ ^ 2) ^ m) := by ring
          _ = f ⟨(m * (2 * len) + (idx.val % len + len)) % 256, _⟩ * ρ ^ (2 * m + 1) := by rw [hpow_odd]

private theorem zPolyNtt_even (f : ZPoly) (p : Fin 128) :
    zPolyNtt f ⟨2 * p.val, by omega⟩ =
      ∑ m ∈ Finset.range 128,
        f ⟨(2 * m) % 256, Nat.mod_lt _ (by decide)⟩ * stageRoot 7 p.val ^ m := by
  have h := zNttPrefix_crt (Nat.le_refl 7) f ⟨2 * p.val, by omega⟩
  have hw : 256 / 2 ^ 7 = 2 := by decide
  have hp2 : 2 ^ 7 = 128 := by decide
  have hdiv : (2 * p.val) / 2 = p.val := by omega
  have hrem : (2 * p.val) % 2 = 0 := by omega
  dsimp only at h
  rw [zPolyNtt, h, hw, hp2, hdiv, hrem]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : m * 2 + 0 = 2 * m := by omega
  rw [hm]

private theorem zPolyNtt_odd (f : ZPoly) (p : Fin 128) :
    zPolyNtt f ⟨2 * p.val + 1, by omega⟩ =
      ∑ m ∈ Finset.range 128,
        f ⟨(2 * m + 1) % 256, Nat.mod_lt _ (by decide)⟩ * stageRoot 7 p.val ^ m := by
  have h := zNttPrefix_crt (Nat.le_refl 7) f ⟨2 * p.val + 1, by omega⟩
  have hw : 256 / 2 ^ 7 = 2 := by decide
  have hp2 : 2 ^ 7 = 128 := by decide
  have hdiv : (2 * p.val + 1) / 2 = p.val := by omega
  have hrem : (2 * p.val + 1) % 2 = 1 := by omega
  dsimp only at h
  rw [zPolyNtt, h, hw, hp2, hdiv, hrem]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : m * 2 + 1 = 2 * m + 1 := by omega
  rw [hm]

/-! ### Quadratic Ring `Quad γ ≅ ℤ_3329[X]/(X^2 - γ)` for Base-Case Convolution -/

@[ext]
private structure Quad (γ : ZMod mlkemQ) where
  re : ZMod mlkemQ
  im : ZMod mlkemQ

private instance instZeroQuad (γ : ZMod mlkemQ) : Zero (Quad γ) := ⟨⟨0, 0⟩⟩
private instance instOneQuad (γ : ZMod mlkemQ) : One (Quad γ) := ⟨⟨1, 0⟩⟩
private instance instAddQuad (γ : ZMod mlkemQ) : Add (Quad γ) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
private instance instNegQuad (γ : ZMod mlkemQ) : Neg (Quad γ) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
private instance instSubQuad (γ : ZMod mlkemQ) : Sub (Quad γ) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
private instance instMulQuad (γ : ZMod mlkemQ) : Mul (Quad γ) :=
  ⟨fun x y => ⟨x.re * y.re + γ * (x.im * y.im), x.re * y.im + x.im * y.re⟩⟩
private instance instNatCastQuad (γ : ZMod mlkemQ) : NatCast (Quad γ) := ⟨fun n => ⟨n, 0⟩⟩
private instance instIntCastQuad (γ : ZMod mlkemQ) : IntCast (Quad γ) := ⟨fun z => ⟨z, 0⟩⟩

private theorem quad_zero_re (γ : ZMod mlkemQ) : (0 : Quad γ).re = 0 := rfl
private theorem quad_zero_im (γ : ZMod mlkemQ) : (0 : Quad γ).im = 0 := rfl
private theorem quad_one_re (γ : ZMod mlkemQ) : (1 : Quad γ).re = 1 := rfl
private theorem quad_one_im (γ : ZMod mlkemQ) : (1 : Quad γ).im = 0 := rfl
private theorem quad_add_re {γ : ZMod mlkemQ} (x y : Quad γ) : (x + y).re = x.re + y.re := rfl
private theorem quad_add_im {γ : ZMod mlkemQ} (x y : Quad γ) : (x + y).im = x.im + y.im := rfl
private theorem quad_neg_re {γ : ZMod mlkemQ} (x : Quad γ) : (-x).re = -x.re := rfl
private theorem quad_neg_im {γ : ZMod mlkemQ} (x : Quad γ) : (-x).im = -x.im := rfl
private theorem quad_sub_re {γ : ZMod mlkemQ} (x y : Quad γ) : (x - y).re = x.re - y.re := rfl
private theorem quad_sub_im {γ : ZMod mlkemQ} (x y : Quad γ) : (x - y).im = x.im - y.im := rfl
private theorem quad_mul_re {γ : ZMod mlkemQ} (x y : Quad γ) :
    (x * y).re = x.re * y.re + γ * (x.im * y.im) := rfl
private theorem quad_mul_im {γ : ZMod mlkemQ} (x y : Quad γ) :
    (x * y).im = x.re * y.im + x.im * y.re := rfl
private theorem quad_natCast_re (γ : ZMod mlkemQ) (n : Nat) : (n : Quad γ).re = n := rfl
private theorem quad_natCast_im (γ : ZMod mlkemQ) (n : Nat) : (n : Quad γ).im = 0 := rfl
private theorem quad_intCast_re (γ : ZMod mlkemQ) (z : Int) : (z : Quad γ).re = z := rfl
private theorem quad_intCast_im (γ : ZMod mlkemQ) (z : Int) : (z : Quad γ).im = 0 := rfl

private instance instCommRingQuad (γ : ZMod mlkemQ) : CommRing (Quad γ) where
  nsmul n x := ⟨n • x.re, n • x.im⟩
  zsmul z x := ⟨z • x.re, z • x.im⟩
  add_assoc a b c := by ext <;> exact add_assoc _ _ _
  zero_add a := by ext <;> exact zero_add _
  add_zero a := by ext <;> exact add_zero _
  add_comm a b := by ext <;> exact add_comm _ _
  nsmul_zero a := by ext <;> exact zero_smul _ _
  nsmul_succ n a := by ext <;> exact succ_nsmul _ _
  zsmul_zero' a := by ext <;> exact zero_smul _ _
  zsmul_succ' n a := by ext <;> exact SubNegMonoid.zsmul_succ' n _
  zsmul_neg' n a := by ext <;> exact SubNegMonoid.zsmul_neg' n _
  sub_eq_add_neg a b := by ext <;> exact sub_eq_add_neg _ _
  neg_add_cancel a := by ext <;> exact neg_add_cancel _
  mul_assoc a b c := by ext <;> simp only [quad_mul_re, quad_mul_im] <;> ring
  one_mul a := by ext <;> simp only [quad_mul_re, quad_mul_im, quad_one_re, quad_one_im] <;> ring
  mul_one a := by ext <;> simp only [quad_mul_re, quad_mul_im, quad_one_re, quad_one_im] <;> ring
  left_distrib a b c := by ext <;> simp only [quad_mul_re, quad_mul_im, quad_add_re, quad_add_im] <;> ring
  right_distrib a b c := by ext <;> simp only [quad_mul_re, quad_mul_im, quad_add_re, quad_add_im] <;> ring
  zero_mul a := by ext <;> simp only [quad_mul_re, quad_mul_im, quad_zero_re, quad_zero_im] <;> ring
  mul_zero a := by ext <;> simp only [quad_mul_re, quad_mul_im, quad_zero_re, quad_zero_im] <;> ring
  mul_comm a b := by ext <;> simp only [quad_mul_re, quad_mul_im] <;> ring
  natCast_zero := by ext <;> simp [quad_natCast_re, quad_natCast_im, quad_zero_re, quad_zero_im]
  natCast_succ n := by
    ext <;> simp [quad_natCast_re, quad_natCast_im, quad_add_re, quad_add_im, quad_one_re, quad_one_im]
  intCast_ofNat n := by ext <;> simp [quad_intCast_re, quad_intCast_im, quad_natCast_re, quad_natCast_im]
  intCast_negSucc n := by
    ext <;> simp [quad_intCast_re, quad_intCast_im, quad_neg_re, quad_neg_im,
      quad_natCast_re, quad_natCast_im, Int.cast_negSucc]

private def quadConst (γ : ZMod mlkemQ) : ZMod mlkemQ →+* Quad γ where
  toFun c := ⟨c, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp only [quad_mul_re, quad_mul_im] <;> ring
  map_zero' := rfl
  map_add' a b := by ext <;> simp [quad_add_re, quad_add_im]

private theorem quadConst_apply (γ c : ZMod mlkemQ) : quadConst γ c = ⟨c, 0⟩ := rfl

private def quadX (γ : ZMod mlkemQ) : Quad γ := ⟨0, 1⟩

private theorem quadX_sq (γ : ZMod mlkemQ) : quadX γ ^ 2 = ⟨γ, 0⟩ := by
  rw [sq]
  ext <;> simp only [quad_mul_re, quad_mul_im, quadX] <;> ring

private theorem quadX_pow_even (γ : ZMod mlkemQ) (m : Nat) :
    quadX γ ^ (2 * m) = ⟨γ ^ m, 0⟩ := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have h : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h, pow_add, ih, quadX_sq]
    ext <;> simp only [quad_mul_re, quad_mul_im, pow_succ] <;> ring

private theorem quadX_pow_odd (γ : ZMod mlkemQ) (m : Nat) :
    quadX γ ^ (2 * m + 1) = ⟨0, γ ^ m⟩ := by
  rw [pow_add, pow_one, quadX_pow_even, quadX]
  ext <;> simp only [quad_mul_re, quad_mul_im] <;> ring

private def evalQuad (γ : ZMod mlkemQ) (f : ZPoly) : Quad γ :=
  ∑ i : Fin 256, quadConst γ (f i) * quadX γ ^ i.val

private theorem evalQuad_eq_zPolyNttPair (f : ZPoly) (p : Fin 128) :
    evalQuad (stageRoot 7 p.val) f =
      ⟨zPolyNtt f ⟨2 * p.val, by omega⟩, zPolyNtt f ⟨2 * p.val + 1, by omega⟩⟩ := by
  set γ := stageRoot 7 p.val
  have huniv :
      evalQuad γ f =
        ∑ k ∈ Finset.range (2 * 128),
          quadConst γ (f ⟨k % 256, Nat.mod_lt _ (by decide)⟩) * quadX γ ^ k := by
    unfold evalQuad
    refine Finset.sum_bij' (fun (i : Fin 256) _ => i.val)
      (fun k hk => ⟨k, Finset.mem_range.mp hk⟩)
      (fun i _ => Finset.mem_range.mpr i.isLt)
      (fun _ _ => Finset.mem_univ _)
      (fun i _ => by ext; rfl)
      (fun _ _ => rfl) ?_
    intro i _
    have hmod : (⟨i.val % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = i := by
      ext; exact Nat.mod_eq_of_lt i.isLt
    rw [hmod]
  rw [huniv, sum_range_even_odd, zPolyNtt_even, zPolyNtt_odd]
  have heven :
      (∑ m ∈ Finset.range 128,
        quadConst γ (f ⟨(2 * m) % 256, Nat.mod_lt _ (by decide)⟩) * quadX γ ^ (2 * m)) =
      ⟨∑ m ∈ Finset.range 128, f ⟨(2 * m) % 256, Nat.mod_lt _ (by decide)⟩ * γ ^ m, 0⟩ := by
    rw [show (⟨∑ m ∈ Finset.range 128, f ⟨(2 * m) % 256, Nat.mod_lt _ (by decide)⟩ * γ ^ m, 0⟩ : Quad γ) =
        quadConst γ (∑ m ∈ Finset.range 128, f ⟨(2 * m) % 256, Nat.mod_lt _ (by decide)⟩ * γ ^ m) from rfl,
      map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [quadX_pow_even]
    ext <;> simp [quadConst_apply, quad_mul_re, quad_mul_im]
  have hodd :
      (∑ m ∈ Finset.range 128,
        quadConst γ (f ⟨(2 * m + 1) % 256, Nat.mod_lt _ (by decide)⟩) * quadX γ ^ (2 * m + 1)) =
      ⟨0, ∑ m ∈ Finset.range 128, f ⟨(2 * m + 1) % 256, Nat.mod_lt _ (by decide)⟩ * γ ^ m⟩ := by
    have hmulX :
        (⟨0, ∑ m ∈ Finset.range 128, f ⟨(2 * m + 1) % 256, Nat.mod_lt _ (by decide)⟩ * γ ^ m⟩ : Quad γ) =
          quadConst γ (∑ m ∈ Finset.range 128, f ⟨(2 * m + 1) % 256, Nat.mod_lt _ (by decide)⟩ * γ ^ m) * quadX γ := by
      rw [quadConst_apply, quadX]
      ext <;> simp [quad_mul_re, quad_mul_im]
    rw [hmulX, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [quadX_pow_odd]
    ext <;> simp [quadConst_apply, quadX, quad_mul_re, quad_mul_im]
  rw [heven, hodd]
  ext <;> simp [quad_add_re, quad_add_im, γ]

private theorem evalQuad_negacyclicMul (p : Fin 128) (a b : ZPoly) :
    evalQuad (stageRoot 7 p.val) (negacyclicMul a b) =
      evalQuad (stageRoot 7 p.val) a * evalQuad (stageRoot 7 p.val) b := by
  set γ := stageRoot 7 p.val
  have hX256 : quadX γ ^ 256 = -1 := by
    have h256 : (256 : Nat) = 2 * 128 := rfl
    rw [h256, quadX_pow_even, stageRoot7_pow_128 p]
    ext <;> simp [quad_neg_re, quad_neg_im, quad_one_re, quad_one_im]
  unfold evalQuad
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have hinner : ∀ i : Fin 256,
      (∑ v : Fin 256, (quadConst γ (a i) * quadX γ ^ i.val) * (quadConst γ (b v) * quadX γ ^ v.val)) =
      ∑ j : Fin 256,
        quadConst γ (if h : i.val ≤ j.val then a i * b ⟨j.val - i.val, by omega⟩
                     else -(a i * b ⟨256 + j.val - i.val, by omega⟩)) * quadX γ ^ j.val := by
    intro i
    refine Finset.sum_bij'
      (fun (v : Fin 256) _ => ⟨(i.val + v.val) % 256, Nat.mod_lt _ (by decide)⟩)
      (fun (j : Fin 256) _ => ⟨(256 + j.val - i.val) % 256, Nat.mod_lt _ (by decide)⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ => Finset.mem_univ _)
      (fun v _ => by ext; dsimp; omega)
      (fun j _ => by ext; dsimp; omega) ?_
    intro v _
    dsimp only
    by_cases hsum : i.val + v.val < 256
    · have hmod : (i.val + v.val) % 256 = i.val + v.val := Nat.mod_eq_of_lt hsum
      have hij : i.val ≤ (i.val + v.val) % 256 := by omega
      have hv_eq : (⟨(i.val + v.val) % 256 - i.val, by omega⟩ : Fin 256) = v := by ext; dsimp; omega
      simp only [hij, ↓reduceDIte, hv_eq]
      rw [hmod, map_mul, pow_add]
      ring
    · have hij : ¬ (i.val ≤ (i.val + v.val) % 256) := by omega
      have hv_eq : (⟨256 + (i.val + v.val) % 256 - i.val, by omega⟩ : Fin 256) = v := by
        ext; dsimp; omega
      have hpow : quadX γ ^ i.val * quadX γ ^ v.val = -(quadX γ ^ ((i.val + v.val) % 256)) := by
        have hsplit : i.val + v.val = 256 + (i.val + v.val) % 256 := by omega
        calc quadX γ ^ i.val * quadX γ ^ v.val
            = quadX γ ^ (i.val + v.val) := (pow_add _ _ _).symm
          _ = quadX γ ^ 256 * quadX γ ^ ((i.val + v.val) % 256) := by rw [← pow_add, ← hsplit]
          _ = (-1) * quadX γ ^ ((i.val + v.val) % 256) := by rw [hX256]
          _ = -(quadX γ ^ ((i.val + v.val) % 256)) := by ring
      simp only [hij, ↓reduceDIte, hv_eq]
      rw [map_neg, map_mul]
      calc quadConst γ (a i) * quadX γ ^ i.val * (quadConst γ (b v) * quadX γ ^ v.val)
          = quadConst γ (a i) * quadConst γ (b v) * (quadX γ ^ i.val * quadX γ ^ v.val) := by ring
        _ = quadConst γ (a i) * quadConst γ (b v) * -(quadX γ ^ ((i.val + v.val) % 256)) := by rw [hpow]
        _ = -(quadConst γ (a i) * quadConst γ (b v)) * quadX γ ^ ((i.val + v.val) % 256) := by ring
  simp_rw [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold negacyclicMul
  rw [map_sum, Finset.sum_mul]

private def zPolyNttMul (f g : ZPoly) : ZPoly :=
  fun idx =>
    let p : Fin 128 := ⟨idx.val / 2, by omega⟩
    let prod := (⟨f ⟨2 * p.val, by omega⟩, f ⟨2 * p.val + 1, by omega⟩⟩ : Quad (stageRoot 7 p.val)) *
                ⟨g ⟨2 * p.val, by omega⟩, g ⟨2 * p.val + 1, by omega⟩⟩
    if idx.val % 2 = 0 then prod.re else prod.im

private theorem toZPoly_polyNttMul_eq (f g : Poly) :
    toZPoly (polyNttMul f g) = zPolyNttMul (toZPoly f) (toZPoly g) := by
  funext idx
  simp only [toZPoly, polyNttMul, getD_ofFn_nat _ _ _ idx.isLt, zPolyNttMul]
  set p := idx.val / 2
  have hk_lt : 64 + p / 2 < 128 := by omega
  have hbz_le : fipsZetas.getD (64 + p / 2) 0 ≤ mlkemQ := by
    rw [fipsZetas_getD_eq_zetaNat hk_lt]
    exact Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 3329))
  have hgamma_cast :
      (if (p % 2 == 0) = true then (fipsZetas.getD (64 + p / 2) 0 : ZMod mlkemQ)
        else (((mlkemQ - fipsZetas.getD (64 + p / 2) 0) % mlkemQ : Nat) : ZMod mlkemQ)) =
        stageRoot 7 p := by
    by_cases hpar : p % 2 = 0
    · simp only [stageRoot, show (7 : Nat) ≠ 0 by decide, ↓reduceIte,
        show 7 - 1 = 6 from rfl, show 2 ^ 6 = 64 by decide, hpar, beq_self_eq_true]
    · have hbeq : (p % 2 == 0) = false := Bool.eq_false_iff.mpr (by simpa using hpar)
      have hsub :
          (((mlkemQ - fipsZetas.getD (64 + p / 2) 0) % mlkemQ : Nat) : ZMod mlkemQ) =
            -(fipsZetas.getD (64 + p / 2) 0 : ZMod mlkemQ) := by
        have h0 := natCast_sub_q (x := 0) hbz_le
        rw [Nat.zero_add, Nat.cast_zero, zero_sub] at h0
        exact h0
      simp only [stageRoot, show (7 : Nat) ≠ 0 by decide, ↓reduceIte,
        show 7 - 1 = 6 from rfl, show 2 ^ 6 = 64 by decide, hpar, hbeq, Bool.false_eq_true, hsub]
  by_cases hidx_even : idx.val % 2 = 0
  · simp only [hidx_even, beq_self_eq_true, ↓reduceIte, natCast_mod_q, quad_mul_re]
    push_cast
    rw [natCast_mod_q]
    push_cast
    rw [hgamma_cast]
    ring
  · have hbeq : (idx.val % 2 == 0) = false := Bool.eq_false_iff.mpr (by simpa using hidx_even)
    simp only [hidx_even, hbeq, Bool.false_eq_true, ↓reduceIte, natCast_mod_q, quad_mul_im]
    push_cast
    rfl

private theorem zPolyNtt_negacyclicMul (a b : ZPoly) :
    zPolyNtt (negacyclicMul a b) = zPolyNttMul (zPolyNtt a) (zPolyNtt b) := by
  funext idx
  let p : Fin 128 := ⟨idx.val / 2, by omega⟩
  have heval := evalQuad_negacyclicMul p a b
  rw [evalQuad_eq_zPolyNttPair, evalQuad_eq_zPolyNttPair, evalQuad_eq_zPolyNttPair] at heval
  dsimp only [zPolyNttMul]
  by_cases hpar : idx.val % 2 = 0
  · have hidx_eq : idx = ⟨2 * p.val, by omega⟩ := by ext; dsimp [p]; omega
    simp only [hpar, ↓reduceIte]
    exact (congrArg (zPolyNtt (negacyclicMul a b)) hidx_eq).trans (congrArg Quad.re heval)
  · have hidx_eq : idx = ⟨2 * p.val + 1, by omega⟩ := by ext; dsimp [p]; omega
    simp only [hpar, ↓reduceIte]
    exact (congrArg (zPolyNtt (negacyclicMul a b)) hidx_eq).trans (congrArg Quad.im heval)

/-! ## 4. Public NTT Linearity, Inversion, and Negacyclic Convolution Theorems -/

theorem toZPoly_polyNtt_congr {a b : Poly} (ha : a.size = 256) (hb : b.size = 256)
    (h : toZPoly a = toZPoly b) : toZPoly (polyNtt a) = toZPoly (polyNtt b) := by
  rw [toZPoly_polyNtt_eq ha, toZPoly_polyNtt_eq hb, h]

theorem toZPoly_polyInvNtt_congr {a b : Poly} (ha : IsCanonicalPoly a) (hb : IsCanonicalPoly b)
    (h : toZPoly a = toZPoly b) : toZPoly (polyInvNtt a) = toZPoly (polyInvNtt b) := by
  rw [toZPoly_polyInvNtt_eq ha, toZPoly_polyInvNtt_eq hb, h]

theorem toZPoly_polyNttMul_congr {a1 a2 b1 b2 : Poly}
    (ha : toZPoly a1 = toZPoly a2) (hb : toZPoly b1 = toZPoly b2) :
    toZPoly (polyNttMul a1 b1) = toZPoly (polyNttMul a2 b2) := by
  rw [toZPoly_polyNttMul_eq, toZPoly_polyNttMul_eq, ha, hb]

theorem toZPoly_polyNtt_polyAdd {a b : Poly} (ha : a.size = 256) (hb : b.size = 256) :
    toZPoly (polyNtt (polyAdd a b)) = toZPoly (polyNtt a) + toZPoly (polyNtt b) := by
  rw [toZPoly_polyNtt_eq (polyAdd_isCanonical a b).1, toZPoly_polyNtt_eq ha,
    toZPoly_polyNtt_eq hb, toZPoly_polyAdd, zPolyNtt, zNttPrefix_add]
  rfl

theorem toZPoly_polyInvNtt_polyAdd {a b : Poly} (ha : IsCanonicalPoly a) (hb : IsCanonicalPoly b) :
    toZPoly (polyInvNtt (polyAdd a b)) = toZPoly (polyInvNtt a) + toZPoly (polyInvNtt b) := by
  rw [toZPoly_polyInvNtt_eq (polyAdd_isCanonical a b), toZPoly_polyInvNtt_eq ha,
    toZPoly_polyInvNtt_eq hb, toZPoly_polyAdd]
  funext i
  simp only [zPolyInvNtt, zInvNttSuffix_add, Pi.add_apply]
  ring

theorem toZPoly_polyNtt_zeroPoly : toZPoly (polyNtt zeroPoly) = 0 := by
  rw [toZPoly_polyNtt_eq zeroPoly_isCanonical.1, toZPoly_zeroPoly]
  have h0 : (0 : ZPoly) = (0 : ZMod mlkemQ) • (0 : ZPoly) := by funext i; simp
  rw [h0, zPolyNtt, zNttPrefix_smul]
  funext i
  simp

theorem toZPoly_polyInvNtt_zeroPoly : toZPoly (polyInvNtt zeroPoly) = 0 := by
  rw [toZPoly_polyInvNtt_eq zeroPoly_isCanonical, toZPoly_zeroPoly]
  have h0 : (0 : ZPoly) = (0 : ZMod mlkemQ) • (0 : ZPoly) := by funext i; simp
  funext i
  rw [zPolyInvNtt, h0, zInvNttSuffix_smul]
  simp

theorem toZPoly_polyNtt_polySub {a b : Poly} (ha : a.size = 256) (hb : b.size = 256) :
    toZPoly (polyNtt (polySub a b)) = toZPoly (polyNtt a) - toZPoly (polyNtt b) := by
  rw [toZPoly_polyNtt_eq (polySub_isCanonical a b).1, toZPoly_polyNtt_eq ha,
    toZPoly_polyNtt_eq hb, toZPoly_polySub, sub_eq_add_neg]
  have hneg : -toZPoly b = (-1 : ZMod mlkemQ) • toZPoly b := by
    funext i; simp
  rw [hneg, zPolyNtt, zNttPrefix_add, zNttPrefix_smul]
  funext i
  simp [zPolyNtt, sub_eq_add_neg]

theorem toZPoly_polyInvNtt_polySub {a b : Poly} (ha : IsCanonicalPoly a) (hb : IsCanonicalPoly b) :
    toZPoly (polyInvNtt (polySub a b)) = toZPoly (polyInvNtt a) - toZPoly (polyInvNtt b) := by
  rw [toZPoly_polyInvNtt_eq (polySub_isCanonical a b), toZPoly_polyInvNtt_eq ha,
    toZPoly_polyInvNtt_eq hb, toZPoly_polySub, sub_eq_add_neg]
  have hneg : -toZPoly b = (-1 : ZMod mlkemQ) • toZPoly b := by
    funext i; simp
  funext i
  rw [zPolyInvNtt, hneg, zInvNttSuffix_add, zInvNttSuffix_smul]
  simp only [zPolyInvNtt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

theorem toZPoly_polyInvNtt_polyNtt {a : Poly} (ha : a.size = 256) :
    toZPoly (polyInvNtt (polyNtt a)) = toZPoly a := by
  rw [toZPoly_polyInvNtt_eq (polyNtt_isCanonical ha), toZPoly_polyNtt_eq ha, zPolyInvNtt_zPolyNtt]

theorem toZPoly_polyNtt_polyInvNtt {a : Poly} (ha : IsCanonicalPoly a) :
    toZPoly (polyNtt (polyInvNtt a)) = toZPoly a := by
  rw [toZPoly_polyNtt_eq (polyInvNtt_isCanonical ha.1).1, toZPoly_polyInvNtt_eq ha,
    zPolyNtt_zPolyInvNtt]

theorem toZPoly_polyInvNtt_polyNttMul {a b : Poly} (ha : a.size = 256) (hb : b.size = 256) :
    toZPoly (polyInvNtt (polyNttMul (polyNtt a) (polyNtt b))) =
      negacyclicMul (toZPoly a) (toZPoly b) := by
  rw [toZPoly_polyInvNtt_eq (polyNttMul_isCanonical _ _), toZPoly_polyNttMul_eq,
    toZPoly_polyNtt_eq ha, toZPoly_polyNtt_eq hb, ← zPolyNtt_negacyclicMul, zPolyInvNtt_zPolyNtt]

theorem toZPoly_polyInvNtt_vecDotNtt (k : Nat) (a b : Array Poly) :
    toZPoly (polyInvNtt (vecDotNtt k a b)) =
      ∑ j ∈ Finset.range k,
        toZPoly (polyInvNtt (polyNttMul (a.getD j zeroPoly) (b.getD j zeroPoly))) := by
  induction k with
  | zero =>
    simp only [vecDotNtt, List.range_zero, List.foldl_nil, toZPoly_polyInvNtt_zeroPoly,
      Finset.range_zero, Finset.sum_empty]
  | succ m ih =>
    have hstep : vecDotNtt (m + 1) a b =
        polyAdd (vecDotNtt m a b) (polyNttMul (a.getD m zeroPoly) (b.getD m zeroPoly)) := by
      unfold vecDotNtt
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep,
      toZPoly_polyInvNtt_polyAdd (vecDotNtt_isCanonical m a b) (polyNttMul_isCanonical _ _),
      ih, Finset.sum_range_succ]

end Computational.Proofs.Kyber1024Delta.NttAlgebra

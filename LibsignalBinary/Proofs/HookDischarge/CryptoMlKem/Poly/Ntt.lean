/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import

/-!
# Forward NEON `NTT` soundness and butterfly stage helper

1. Polymorphic 256-lane `butterflyStage` closed-form indexing (`butterflyStage_getD`,
   `foldl_range_stepK`), shared by forward `NTT` (`Poly.Ntt`) and inverse `NTT⁻¹` (`Poly.InvNtt`).
2. NEON 128-bit vector butterfly steps matching compiled `MlKemPlacedObj` (`B03`, `B04`, `B06`):
   - Binomial layer 7 (`mul v.8h, 0xf9c0#16`, `-1600 ≡ 1729 (mod 3329)`),
   - Whole-vector layers (`len ∈ {128, 64, 32, 16, 8}`) with `dup8x16 (zetaTableAt k)`,
   - Layer `len = 4` (`pack2x64` / `zip1.2d` + `zip2.2d`),
   - Layer `len = 2` (`simdTrn1_4s` / `simdTrn2_4s` with `[k, k+2, k+1, k+3]` zeta ordering).
3. Full polynomial soundness and `[-1664, 1664]` output bounds for both general Montgomery
   `neonPolyNtt16` (`PolyBounded16 3328` input) and binomial `neonPolyNttBinomial16`
   (`PolyBounded16 3` input, covering `cbd2` and `cbd3`) against `Spec.polyNtt`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 mlkemQ fipsZetas zetasTimesMontgomeryR
  neonBarrettReduce16 neonMontgomeryMul16 nttStage polyNtt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane16 lane32 lane64 pack8x16 pack2x64 dup8x16
  lane16_pack8x16 lane16_dup8x16 lane16_append64_lo lane16_append64_hi
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdSub8h simdMul8h simdTrn1_4s simdTrn2_4s
  lane16_simdAdd8h lane16_simdSub8h lane16_simdMul8h
  lane32_simdTrn1_4s lane32_simdTrn2_4s
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  fipsZetaAt fipsZetas_getD
  zetaTableAt_eq_zetasTimesMontgomeryR zetasTimesMontgomeryR_bounds
  zetasTimesMontgomeryR_ne_0x8000 zetasTimesMontgomeryR_mod_3329
  toInt_eq_of_emod_65536 toInt_mul_emod_65536 toInt_add_of_bounds toInt_sub_of_bounds
  neonBarrettReduce16_spec neonMontgomeryMul16_spec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents
)

/-! ## 1. Polymorphic 256-Lane Butterfly Stage & Sub-Lane Extraction Helpers -/

theorem size_set! {α : Type} (arr : Array α) (i : Nat) (v : α) :
    (arr.set! i v).size = arr.size := by
  simp [Array.set!]

theorem getD_set! {α : Type} (arr : Array α) (k : Nat) (v : α) (idx : Nat) (d : α) :
    (arr.set! k v).getD idx d = if idx = k ∧ k < arr.size then v else arr.getD idx d := by
  by_cases hk : k < arr.size
  · by_cases hidx : idx = k
    · subst hidx; simp [Array.set!, Array.setIfInBounds, Array.getD, hk]
    · by_cases hi : idx < arr.size
      · simp [Array.set!, Array.setIfInBounds, Array.getD, hk, hi, hidx, Ne.symm hidx]
      · simp [Array.set!, Array.setIfInBounds, hk, hi, hidx]
  · simp [Array.set!, Array.setIfInBounds, hk]

theorem foldl_range_stepK {α : Type} (n : Nat) (body : Array α → Nat → Nat → Array α)
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

/-- Polymorphic 256-lane butterfly stage (`nBlocks = 256 / (2 * len)` blocks of width `2 * len`). -/
@[expose] def butterflyStage {α : Type} (len : Nat) (pairFn : Nat → α → α → α × α)
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

theorem butterflyStage_size {α : Type} {len : Nat} (pairFn : Nat → α → α → α × α)
    (d : α) {arr : Array α}
    (hsize : arr.size = 256) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) :
    (butterflyStage len pairFn d arr).size = 256 := by
  have hblocks : 2 * len * (256 / (2 * len)) = 256 := Nat.mul_div_cancel' hdiv
  exact (outer_butterfly_spec len (256 / (2 * len)) (256 / (2 * len))
    pairFn d arr hsize hlen hblocks (Nat.le_refl _)).1

theorem butterflyStage_getD {α : Type} {len : Nat} (pairFn : Nat → α → α → α × α)
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

theorem extract16_lane64 (v : BitVec 128) (c : Fin 2) (j : Nat) (hj : j < 4) :
    (lane64 v c).extractLsb' (16 * j) 16 = lane16 v ⟨4 * c.val + j, by omega⟩ := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [lane64, lane16, BitVec.getLsbD_extractLsb', hb,
    show 16 * j + b < 64 by omega, decide_true, Bool.true_and]
  congr 1; omega

@[simp] theorem lane16_pack2x64_sel (x y : BitVec 128) (cx cy : Fin 2) (i : Fin 8) :
    lane16 (pack2x64 fun c => if c.val = 0 then lane64 x cx else lane64 y cy) i =
      if h : i.val < 4 then lane16 x ⟨4 * cx.val + i.val, by omega⟩
      else lane16 y ⟨4 * cy.val + (i.val - 4), by omega⟩ := by
  dsimp only [pack2x64]
  by_cases h : i.val < 4
  · simp only [h, ↓reduceDIte, lane16_append64_lo _ _ i h]
    exact extract16_lane64 x cx i.val h
  · simp only [h, ↓reduceDIte, lane16_append64_hi _ _ i (by omega)]
    exact extract16_lane64 y cy (i.val - 4) (by omega)

@[simp] theorem extract16_lane32_lo (v : BitVec 128) (k : Fin 4) :
    (lane32 v k).extractLsb' 0 16 = lane16 v ⟨2 * k.val, by omega⟩ := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [lane32, lane16, BitVec.getLsbD_extractLsb', Nat.zero_add, hb,
    show b < 32 by omega, decide_true, Bool.true_and]
  congr 1; omega

@[simp] theorem extract16_lane32_hi (v : BitVec 128) (k : Fin 4) :
    (lane32 v k).extractLsb' 16 16 = lane16 v ⟨2 * k.val + 1, by omega⟩ := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [lane32, lane16, BitVec.getLsbD_extractLsb', hb,
    show 16 + b < 32 by omega, decide_true, Bool.true_and]
  congr 1; omega

theorem lane16_of_lane32 (v : BitVec 128) (i : Fin 8) :
    lane16 v i =
      if i.val % 2 = 0 then
        (lane32 v ⟨i.val / 2, by omega⟩).extractLsb' 0 16
      else
        (lane32 v ⟨i.val / 2, by omega⟩).extractLsb' 16 16 := by
  by_cases he : i.val % 2 = 0
  · simp only [he, ↓reduceIte, extract16_lane32_lo]; congr 1; ext; dsimp only; omega
  · simp only [he, ↓reduceIte, extract16_lane32_hi]; congr 1; ext; dsimp only; omega

@[simp] theorem lane16_simdTrn1_4s (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdTrn1_4s vn vm) i =
      if h : (i.val / 2) % 2 = 0 then lane16 vn ⟨4 * (i.val / 4) + i.val % 2, by omega⟩
      else lane16 vm ⟨4 * (i.val / 4) + i.val % 2, by omega⟩ := by
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals
    rw [lane16_of_lane32]
    dsimp only
    simp only [lane32_simdTrn1_4s, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte,
      extract16_lane32_lo, extract16_lane32_hi]

@[simp] theorem lane16_simdTrn2_4s (vn vm : BitVec 128) (i : Fin 8) :
    lane16 (simdTrn2_4s vn vm) i =
      if h : (i.val / 2) % 2 = 0 then lane16 vn ⟨4 * (i.val / 4) + 2 + i.val % 2, by omega⟩
      else lane16 vm ⟨4 * (i.val / 4) + 2 + i.val % 2, by omega⟩ := by
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals
    rw [lane16_of_lane32]
    dsimp only
    simp only [lane32_simdTrn2_4s, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte,
      extract16_lane32_lo, extract16_lane32_hi]

/-! ## 2. Forward NEON `NTT` Definitions & Vector Butterfly Equivalences -/

/-- Forward NEON `NTT` stage at stride `len` using Montgomery multiplication with `zetasTimesMontgomeryR`. -/
@[expose] def neonNttStage16 (len kInit : Nat) (f : Poly16) : Poly16 × Nat :=
  let nBlocks := 256 / (2 * len)
  (List.range nBlocks).foldl
    (fun (cur, k) blk =>
      let start := blk * 2 * len
      let zeta := zetasTimesMontgomeryR.getD k 0#16
      let next := (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let a := arr.getD j 0#16
          let b := arr.getD (j + len) 0#16
          let t := neonMontgomeryMul16 b zeta
          (arr.set! j (a + t)).set! (j + len) (a - t))
        cur
      (next, k + 1))
    (f, kInit)

/-- Binomial layer 7 (`len = 128`, `k = 1`, `B03 +0x3754`): direct `mul · 0xf9c0#16` (`-1600 ≡ 1729 (mod 3329)`). -/
@[expose] def neonNttBinomialLayer7_16 (f : Poly16) : Poly16 :=
  (List.range 128).foldl
    (fun arr j =>
      let a := arr.getD j 0#16
      let b := arr.getD (j + 128) 0#16
      let t := b * 0xf9c0#16
      (arr.set! j (a + t)).set! (j + 128) (a - t))
    f

/-- General 7-stage NEON Montgomery forward `NTT` + `neonBarrettReduce16` (`B04` / `B06`). -/
@[expose] def neonPolyNtt16 (f : Poly16) : Poly16 :=
  let (f, k) := neonNttStage16 128 1 f
  let (f, k) := neonNttStage16 64 k f
  let (f, k) := neonNttStage16 32 k f
  let (f, k) := neonNttStage16 16 k f
  let (f, k) := neonNttStage16 8 k f
  let (f, k) := neonNttStage16 4 k f
  let (f, _) := neonNttStage16 2 k f
  f.map neonBarrettReduce16

/-- Binomial 7-stage NEON forward `NTT` (`neonNttBinomialLayer7_16` + 6 Montgomery stages + Barrett, `B03`). -/
@[expose] def neonPolyNttBinomial16 (f : Poly16) : Poly16 :=
  let f := neonNttBinomialLayer7_16 f
  let (f, k) := neonNttStage16 64 2 f
  let (f, k) := neonNttStage16 32 k f
  let (f, k) := neonNttStage16 16 k f
  let (f, k) := neonNttStage16 8 k f
  let (f, k) := neonNttStage16 4 k f
  let (f, _) := neonNttStage16 2 k f
  f.map neonBarrettReduce16

/-- 8-lane NEON Montgomery multiply (`pack8x16` of `neonMontgomeryMul16`). -/
@[expose] def simdMontMul8h (v zVec : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => neonMontgomeryMul16 (lane16 v i) (lane16 zVec i)

@[simp] theorem lane16_simdMontMul8h (v zVec : BitVec 128) (i : Fin 8) :
    lane16 (simdMontMul8h v zVec) i = neonMontgomeryMul16 (lane16 v i) (lane16 zVec i) :=
  lane16_pack8x16 _ i

/-- Binomial layer-7 NEON vector butterfly (`B03 +0x3754`: `mul v.8h, v.8h, 0xf9c0#16`). -/
@[expose] def nttBinomialLayer7VecPair (va vb : BitVec 128) : BitVec 128 × BitVec 128 :=
  let t := simdMul8h vb (dup8x16 0xf9c0#16)
  (simdAdd8h va t, simdSub8h va t)

@[simp] theorem lane16_nttBinomialLayer7VecPair (va vb : BitVec 128) (i : Fin 8) :
    lane16 (nttBinomialLayer7VecPair va vb).1 i = lane16 va i + lane16 vb i * 0xf9c0#16 ∧
    lane16 (nttBinomialLayer7VecPair va vb).2 i = lane16 va i - lane16 vb i * 0xf9c0#16 := by
  simp [nttBinomialLayer7VecPair]

/-- Whole-vector NEON butterfly (`len ∈ {128, 64, 32, 16, 8}`) with `dup8x16 (zetaTableAt k)`. -/
@[expose] def nttLayer8hVecPair (va vb : BitVec 128) (k : Nat) : BitVec 128 × BitVec 128 :=
  let t := simdMontMul8h vb (dup8x16 (zetaTableAt k))
  (simdAdd8h va t, simdSub8h va t)

theorem lane16_nttLayer8hVecPair {k : Nat} (hk : k < 128) (va vb : BitVec 128) (i : Fin 8) :
    let z := zetasTimesMontgomeryR.getD k 0#16
    lane16 (nttLayer8hVecPair va vb k).1 i = lane16 va i + neonMontgomeryMul16 (lane16 vb i) z ∧
    lane16 (nttLayer8hVecPair va vb k).2 i = lane16 va i - neonMontgomeryMul16 (lane16 vb i) z := by
  dsimp [nttLayer8hVecPair]
  simp [zetaTableAt_eq_zetasTimesMontgomeryR hk]

/-- Layer `len = 4` NEON 2-vector butterfly (`zip1.2d`/`zip2.2d` via `pack2x64`, `B03 +0x4398..+0x43f8`). -/
@[expose] def nttLayer4VecPair (vLo vHi : BitVec 128) (k : Nat) : BitVec 128 × BitVec 128 :=
  let a := pack2x64 fun c => if c.val = 0 then lane64 vLo 0 else lane64 vHi 0
  let b := pack2x64 fun c => if c.val = 0 then lane64 vLo 1 else lane64 vHi 1
  let zVec := pack8x16 fun i => if i.val < 4 then zetaTableAt k else zetaTableAt (k + 1)
  let t := simdMontMul8h b zVec
  let a' := simdAdd8h a t
  let b' := simdSub8h a t
  (pack2x64 (fun c => if c.val = 0 then lane64 a' 0 else lane64 b' 0),
   pack2x64 (fun c => if c.val = 0 then lane64 a' 1 else lane64 b' 1))

@[local simp] private theorem lane16_pack2x64_sel_zero (x y : BitVec 128) (cx cy : Fin 2) (i : Fin 8) :
    lane16 (pack2x64 fun c => if c = 0 then lane64 x cx else lane64 y cy) i =
      if h : i.val < 4 then lane16 x ⟨4 * cx.val + i.val, by omega⟩
      else lane16 y ⟨4 * cy.val + (i.val - 4), by omega⟩ := by
  dsimp only [pack2x64]
  by_cases h : i.val < 4
  · simp only [h, ↓reduceDIte, lane16_append64_lo _ _ i h]
    exact extract16_lane64 x cx i.val h
  · simp only [h, ↓reduceDIte, lane16_append64_hi _ _ i (by omega)]
    exact extract16_lane64 y cy (i.val - 4) (by omega)

theorem lane16_nttLayer4VecPair {k : Nat} (hk : k + 1 < 128) (vLo vHi : BitVec 128) (i : Fin 8) :
    let z0 := zetasTimesMontgomeryR.getD k 0#16
    let z1 := zetasTimesMontgomeryR.getD (k + 1) 0#16
    lane16 (nttLayer4VecPair vLo vHi k).1 i =
      (if h : i.val < 4 then
        lane16 vLo i + neonMontgomeryMul16 (lane16 vLo ⟨i.val + 4, by omega⟩) z0
       else
        lane16 vLo ⟨i.val - 4, by omega⟩ - neonMontgomeryMul16 (lane16 vLo i) z0) ∧
    lane16 (nttLayer4VecPair vLo vHi k).2 i =
      (if h : i.val < 4 then
        lane16 vHi i + neonMontgomeryMul16 (lane16 vHi ⟨i.val + 4, by omega⟩) z1
       else
        lane16 vHi ⟨i.val - 4, by omega⟩ - neonMontgomeryMul16 (lane16 vHi i) z1) := by
  have hz0 := zetaTableAt_eq_zetasTimesMontgomeryR (by omega : k < 128)
  have hz1 := zetaTableAt_eq_zetasTimesMontgomeryR hk
  unfold nttLayer4VecPair
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals
    dsimp only
    simp [lane16_simdAdd8h, lane16_simdSub8h,
      lane16_simdMontMul8h, lane16_pack8x16, hz0, hz1]

/-- Layer `len = 2` NEON 2-vector butterfly (`simdTrn1_4s`/`simdTrn2_4s` with `[k, k+2, k+1, k+3]`
    zeta ordering matching `B03 +0x4408..+0x4480`). -/
@[expose] def nttLayer2VecPair (vLo vHi : BitVec 128) (k : Nat) : BitVec 128 × BitVec 128 :=
  let a := simdTrn1_4s vLo vHi
  let b := simdTrn2_4s vLo vHi
  let zVec := pack8x16 fun i =>
    if i.val / 2 = 0 then zetaTableAt k
    else if i.val / 2 = 1 then zetaTableAt (k + 2)
    else if i.val / 2 = 2 then zetaTableAt (k + 1)
    else zetaTableAt (k + 3)
  let t := simdMontMul8h b zVec
  let a' := simdAdd8h a t
  let b' := simdSub8h a t
  (simdTrn1_4s a' b', simdTrn2_4s a' b')

theorem lane16_nttLayer2VecPair {k : Nat} (hk : k + 3 < 128) (vLo vHi : BitVec 128) (i : Fin 8) :
    let zk (m : Nat) := zetasTimesMontgomeryR.getD (k + m) 0#16
    lane16 (nttLayer2VecPair vLo vHi k).1 i =
      (let z := zk (i.val / 4)
       if h : i.val % 4 < 2 then
         lane16 vLo i + neonMontgomeryMul16 (lane16 vLo ⟨i.val + 2, by have := i.isLt; omega⟩) z
       else
         lane16 vLo ⟨i.val - 2, by have := i.isLt; omega⟩ - neonMontgomeryMul16 (lane16 vLo i) z) ∧
    lane16 (nttLayer2VecPair vLo vHi k).2 i =
      (let z := zk (2 + i.val / 4)
       if h : i.val % 4 < 2 then
         lane16 vHi i + neonMontgomeryMul16 (lane16 vHi ⟨i.val + 2, by have := i.isLt; omega⟩) z
       else
         lane16 vHi ⟨i.val - 2, by have := i.isLt; omega⟩ - neonMontgomeryMul16 (lane16 vHi i) z) := by
  have hz0 := zetaTableAt_eq_zetasTimesMontgomeryR (by omega : k < 128)
  have hz1 := zetaTableAt_eq_zetasTimesMontgomeryR (by omega : k + 1 < 128)
  have hz2 := zetaTableAt_eq_zetasTimesMontgomeryR (by omega : k + 2 < 128)
  have hz3 := zetaTableAt_eq_zetasTimesMontgomeryR hk
  unfold nttLayer2VecPair
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals
    dsimp only
    simp only [lane16_simdTrn1_4s, lane16_simdTrn2_4s, lane16_simdAdd8h, lane16_simdSub8h,
      lane16_simdMontMul8h, lane16_pack8x16, Nat.reduceAdd, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      ↓reduceDIte, ↓reduceIte, Nat.add_zero, hz0, hz1, hz2, hz3]
    exact ⟨trivial, trivial⟩

/-! ## 3. Stage & Full Polynomial Soundness (`neonPolyNtt16` & `neonPolyNttBinomial16`) -/

/-- `neonMontgomeryMul16` by `zetasTimesMontgomeryR[k]` cancels `2^16` modulo `3329`. -/
theorem neonMontgomeryMul16_zeta_spec {k : Nat} (hk : k < 128) (v : BitVec 16) :
    let z := zetasTimesMontgomeryR.getD k 0#16
    (neonMontgomeryMul16 v z).toInt % 3329 =
      (v.toInt * (fipsZetas.getD k 0 : Int)) % 3329 ∧
    -2496 ≤ (neonMontgomeryMul16 v z).toInt ∧
    (neonMontgomeryMul16 v z).toInt ≤ 2496 := by
  dsimp only
  set z := zetasTimesMontgomeryR.getD k 0#16
  have hne := zetasTimesMontgomeryR_ne_0x8000 hk
  have hzb := zetasTimesMontgomeryR_bounds hk
  have hzm := zetasTimesMontgomeryR_mod_3329 hk
  obtain ⟨hm, hb⟩ := neonMontgomeryMul16_spec v z hne
  obtain ⟨hlo, hhi⟩ := hb hzb
  refine ⟨?_, hlo, hhi⟩
  let fz : Int := fipsZetas.getD k 0
  have hrhs : (v.toInt * z.toInt) % 3329 = ((v.toInt * fz) * 65536) % 3329 := by
    rw [Int.mul_emod v.toInt z.toInt, hzm, ← Int.mul_emod]
    exact congrArg (· % 3329) (Int.mul_assoc v.toInt fz 65536).symm
  let d := (neonMontgomeryMul16 v z).toInt - v.toInt * fz
  have hd64 : (d * 65536) % 3329 = 0 := by
    dsimp [d]
    rw [Int.sub_mul, Int.sub_emod, hm, hrhs, Int.sub_self, Int.zero_emod]
  have hd1 : d % 3329 = 0 := by
    have : ((d * 65536) * 169) % 3329 = 0 := by rw [Int.mul_emod, hd64]; simp
    have h169 : (d * 65536) * 169 = d + d * 3327 * 3329 := by omega
    rw [h169] at this; omega
  dsimp [d, fz] at hd1; omega

/-- Pointwise `neonBarrettReduce16` bounds a polynomial to `[-1664, 1664]` while preserving `PolyRepresents`. -/
theorem neonBarrettReducePoly16_spec {p : Poly16} {f : Poly} (hrep : PolyRepresents p f) :
    PolyBounded16 1664 (p.map neonBarrettReduce16) ∧
    PolyRepresents (p.map neonBarrettReduce16) f := by
  have hsize : (p.map neonBarrettReduce16).size = 256 := by simp [hrep.1]
  refine ⟨⟨hsize, fun i hi => ?_⟩, ⟨hsize, fun i hi => ?_⟩⟩
  · have hmap : (p.map neonBarrettReduce16).getD i 0#16 = neonBarrettReduce16 (p.getD i 0#16) := by
      simp [Array.getD, hrep.1, hi]
    rw [hmap]
    have hb := neonBarrettReduce16_spec (p.getD i 0#16)
    exact ⟨hb.1, hb.2.1⟩
  · have hmap : (p.map neonBarrettReduce16).getD i 0#16 = neonBarrettReduce16 (p.getD i 0#16) := by
      simp [Array.getD, hrep.1, hi]
    rw [hmap, (neonBarrettReduce16_spec (p.getD i 0#16)).2.2]
    exact hrep.2 i hi

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

private theorem neonNttStage16_eq_butterfly (len kInit : Nat) (p : Poly16) :
    neonNttStage16 len kInit p =
      (butterflyStage len
        (fun blk a b =>
          let t := neonMontgomeryMul16 b (zetasTimesMontgomeryR.getD (kInit + blk) 0#16)
          (a + t, a - t))
        0#16 p,
       kInit + 256 / (2 * len)) := by
  unfold neonNttStage16 butterflyStage
  exact foldl_range_stepK (256 / (2 * len))
    (fun cur k blk =>
      let start := blk * 2 * len
      (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let a := arr.getD j 0#16
          let b := arr.getD (j + len) 0#16
          let t := neonMontgomeryMul16 b (zetasTimesMontgomeryR.getD k 0#16)
          (arr.set! j (a + t)).set! (j + len) (a - t))
        cur)
    (· + 1) (kInit + ·) kInit (Nat.add_zero kInit) (fun b => (Nat.add_assoc kInit b 1).symm) p

private theorem ntt_butterfly_mod {a t : BitVec 16} {fj z fjl : Nat}
    (ha_mod : a.toInt % 3329 = (fj : Int) % 3329)
    (ht_mod : t.toInt % 3329 = ((z : Int) * (fjl : Int)) % 3329)
    (ha_b : -27000 ≤ a.toInt ∧ a.toInt ≤ 27000)
    (ht_b : -4800 ≤ t.toInt ∧ t.toInt ≤ 4800) :
    (a + t).toInt % 3329 = (((fj + (z * fjl) % mlkemQ) % mlkemQ : Nat) : Int) % 3329 ∧
    (a - t).toInt % 3329 = (((fj + mlkemQ - (z * fjl) % mlkemQ) % mlkemQ : Nat) : Int) % 3329 := by
  have hadd_int : (a + t).toInt = a.toInt + t.toInt := toInt_add_of_bounds (by omega) (by omega)
  have hsub_int : (a - t).toInt = a.toInt - t.toInt := toInt_sub_of_bounds (by omega) (by omega)
  set prod : Nat := z * fjl
  have hprod_cast : (prod : Int) = (z : Int) * (fjl : Int) := Int.natCast_mul z fjl
  rw [← hprod_cast] at ht_mod
  dsimp only [mlkemQ]
  exact ⟨by omega, by omega⟩

/-- Soundness & `B + 2496` bound growth for one forward Montgomery `neonNttStage16`. -/
theorem neonNttStage16_spec {B : Int} (len kInit : Nat) {p : Poly16} {f : Poly}
    (hbnd : PolyBounded16 B p) (hrep : PolyRepresents p f) (hf : f.size = 256)
    (hB0 : 0 ≤ B) (hBmax : B ≤ 27000)
    (hlen : 0 < len) (hdiv : 2 * len ∣ 256) (hk : kInit + 256 / (2 * len) ≤ 128) :
    (neonNttStage16 len kInit p).2 = kInit + 256 / (2 * len) ∧
    (nttStage len kInit f).2 = kInit + 256 / (2 * len) ∧
    (nttStage len kInit f).1.size = 256 ∧
    PolyBounded16 (B + 2496) (neonNttStage16 len kInit p).1 ∧
    PolyRepresents (neonNttStage16 len kInit p).1 (nttStage len kInit f).1 := by
  rw [neonNttStage16_eq_butterfly, nttStage_eq_butterfly]
  dsimp only
  let pairP : Nat → BitVec 16 → BitVec 16 → BitVec 16 × BitVec 16 := fun blk a b =>
    let t := neonMontgomeryMul16 b (zetasTimesMontgomeryR.getD (kInit + blk) 0#16)
    (a + t, a - t)
  let pairF : Nat → Nat → Nat → Nat × Nat := fun blk fj fjl =>
    let t := (fipsZetas.getD (kInit + blk) 0 * fjl) % mlkemQ
    ((fj + t) % mlkemQ, (fj + mlkemQ - t) % mlkemQ)
  have hsz_p := butterflyStage_size pairP 0#16 hbnd.1 hlen hdiv
  have hsz_f := butterflyStage_size pairF 0 hf hlen hdiv
  refine ⟨rfl, rfl, hsz_f, ⟨hsz_p, fun idx hidx => ?_⟩, ⟨hsz_p, fun idx hidx => ?_⟩⟩
  · rw [butterflyStage_getD pairP 0#16 hbnd.1 hlen hdiv hidx]
    dsimp only [pairP]
    have hblk : kInit + idx / (2 * len) < 128 := by
      have : idx / (2 * len) < 256 / (2 * len) :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_div_cancel' hdiv]; exact hidx)
      omega
    by_cases hhalf : idx % (2 * len) < len
    · simp only [hhalf, ↓reduceIte]
      have ha := hbnd.2 idx hidx
      have ht := neonMontgomeryMul16_zeta_spec hblk (p.getD (idx + len) 0#16)
      have hadd := toInt_add_of_bounds (a := p.getD idx 0#16)
        (b := neonMontgomeryMul16 (p.getD (idx + len) 0#16) (zetasTimesMontgomeryR.getD (kInit + idx / (2 * len)) 0#16))
        (by omega) (by omega)
      omega
    · simp only [hhalf, ↓reduceIte]
      have ha := hbnd.2 (idx - len) (by omega)
      have ht := neonMontgomeryMul16_zeta_spec hblk (p.getD idx 0#16)
      have hsub := toInt_sub_of_bounds (a := p.getD (idx - len) 0#16)
        (b := neonMontgomeryMul16 (p.getD idx 0#16) (zetasTimesMontgomeryR.getD (kInit + idx / (2 * len)) 0#16))
        (by omega) (by omega)
      omega
  · rw [butterflyStage_getD pairP 0#16 hbnd.1 hlen hdiv hidx,
      butterflyStage_getD pairF 0 hf hlen hdiv hidx]
    dsimp only [pairP, pairF]
    have hblk : kInit + idx / (2 * len) < 128 := by
      have : idx / (2 * len) < 256 / (2 * len) :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_div_cancel' hdiv]; exact hidx)
      omega
    by_cases hhalf : idx % (2 * len) < len
    · simp only [hhalf, ↓reduceIte]
      have hjl : idx + len < 256 := by
        have hq_lt : idx / (2 * len) < 256 / (2 * len) :=
          Nat.div_lt_of_lt_mul (by rw [Nat.mul_div_cancel' hdiv]; exact hidx)
        have hq_le : (idx / (2 * len) + 1) * (2 * len) ≤ 256 := by
          calc (idx / (2 * len) + 1) * (2 * len)
              ≤ (256 / (2 * len)) * (2 * len) := Nat.mul_le_mul_right _ hq_lt
            _ = 256 := by rw [Nat.mul_comm]; exact Nat.mul_div_cancel' hdiv
        have hsucc : (idx / (2 * len) + 1) * (2 * len) = (2 * len) * (idx / (2 * len)) + 2 * len := by
          rw [Nat.succ_mul, Nat.mul_comm]
        have hd := Nat.div_add_mod idx (2 * len)
        omega
      have ha_b := hbnd.2 idx hidx
      have ha_m := hrep.2 idx hidx
      have hb_m := hrep.2 (idx + len) hjl
      have ht := neonMontgomeryMul16_zeta_spec hblk (p.getD (idx + len) 0#16)
      have ht_mod : (neonMontgomeryMul16 (p.getD (idx + len) 0#16)
          (zetasTimesMontgomeryR.getD (kInit + idx / (2 * len)) 0#16)).toInt % 3329 =
          ((fipsZetas.getD (kInit + idx / (2 * len)) 0 : Int) * (f.getD (idx + len) 0 : Int)) % 3329 := by
        rw [ht.1, Int.mul_emod, hb_m, ← Int.mul_emod, Int.mul_comm (f.getD (idx + len) 0 : Int)]
      exact (ntt_butterfly_mod ha_m ht_mod ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).1
    · simp only [hhalf, ↓reduceIte]
      have hij : idx - len < 256 := by omega
      have ha_b := hbnd.2 (idx - len) hij
      have ha_m := hrep.2 (idx - len) hij
      have hb_m := hrep.2 idx hidx
      have ht := neonMontgomeryMul16_zeta_spec hblk (p.getD idx 0#16)
      have ht_mod : (neonMontgomeryMul16 (p.getD idx 0#16)
          (zetasTimesMontgomeryR.getD (kInit + idx / (2 * len)) 0#16)).toInt % 3329 =
          ((fipsZetas.getD (kInit + idx / (2 * len)) 0 : Int) * (f.getD idx 0 : Int)) % 3329 := by
        rw [ht.1, Int.mul_emod, hb_m, ← Int.mul_emod, Int.mul_comm (f.getD idx 0 : Int)]
      exact (ntt_butterfly_mod ha_m ht_mod ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).2

/-- Soundness & `4803` bound of binomial layer 7 (`mul · 0xf9c0#16`, `B ≤ 3`). -/
theorem neonNttBinomialLayer7_16_spec {p : Poly16} {f : Poly}
    (hbnd : PolyBounded16 3 p) (hrep : PolyRepresents p f) (hf : f.size = 256) :
    (nttStage 128 1 f).2 = 2 ∧
    (nttStage 128 1 f).1.size = 256 ∧
    PolyBounded16 4803 (neonNttBinomialLayer7_16 p) ∧
    PolyRepresents (neonNttBinomialLayer7_16 p) (nttStage 128 1 f).1 := by
  let pairB : Nat → BitVec 16 → BitVec 16 → BitVec 16 × BitVec 16 := fun _ a b =>
    let t := b * 0xf9c0#16; (a + t, a - t)
  let pairF : Nat → Nat → Nat → Nat × Nat := fun blk fj fjl =>
    let t := (fipsZetas.getD (1 + blk) 0 * fjl) % mlkemQ
    ((fj + t) % mlkemQ, (fj + mlkemQ - t) % mlkemQ)
  have heq_b : neonNttBinomialLayer7_16 p = butterflyStage 128 pairB 0#16 p := by
    unfold neonNttBinomialLayer7_16 butterflyStage
    simp only [Nat.reduceMul, Nat.reduceDiv, List.range_one, List.foldl_cons, List.foldl_nil,
      Nat.zero_add, pairB]
  rw [heq_b, nttStage_eq_butterfly]
  dsimp only
  have hdiv : 2 * 128 ∣ 256 := by decide
  have hsz_p := butterflyStage_size pairB 0#16 hbnd.1 (by omega) hdiv
  have hsz_f := butterflyStage_size pairF 0 hf (by omega) hdiv
  have hz1 : fipsZetas.getD 1 0 = 1729 :=
    (fipsZetas_getD (by decide : 1 < 128)).trans (by decide +kernel : fipsZetaAt 1 = 1729)
  have hm1600 : (0xf9c0#16 : BitVec 16).toInt = -1600 := rfl
  have hmul_b : ∀ b : BitVec 16, -3 ≤ b.toInt → b.toInt ≤ 3 →
      (b * 0xf9c0#16).toInt = b.toInt * (-1600) := by
    intro b h1 h2
    apply toInt_eq_of_emod_65536 (by omega) (by omega)
    rw [toInt_mul_emod_65536, hm1600]
  refine ⟨by decide, hsz_f, ⟨hsz_p, fun idx hidx => ?_⟩, ⟨hsz_p, fun idx hidx => ?_⟩⟩
  · rw [butterflyStage_getD pairB 0#16 hbnd.1 (by omega) hdiv hidx]
    dsimp only [pairB]
    by_cases hhalf : idx % (2 * 128) < 128
    · simp only [hhalf, ↓reduceIte]
      have ha := hbnd.2 idx hidx
      have hb := hbnd.2 (idx + 128) (by omega)
      have ht := hmul_b (p.getD (idx + 128) 0#16) hb.1 hb.2
      have hadd := toInt_add_of_bounds (a := p.getD idx 0#16)
        (b := p.getD (idx + 128) 0#16 * 0xf9c0#16) (by omega) (by omega)
      omega
    · simp only [hhalf, ↓reduceIte]
      have ha := hbnd.2 (idx - 128) (by omega)
      have hb := hbnd.2 idx hidx
      have ht := hmul_b (p.getD idx 0#16) hb.1 hb.2
      have hsub := toInt_sub_of_bounds (a := p.getD (idx - 128) 0#16)
        (b := p.getD idx 0#16 * 0xf9c0#16) (by omega) (by omega)
      omega
  · rw [butterflyStage_getD pairB 0#16 hbnd.1 (by omega) hdiv hidx,
      butterflyStage_getD pairF 0 hf (by omega) hdiv hidx]
    dsimp only [pairB, pairF]
    have hblk0 : idx / (2 * 128) = 0 := by omega
    rw [hblk0, Nat.add_zero, hz1]
    by_cases hhalf : idx % (2 * 128) < 128
    · simp only [hhalf, ↓reduceIte]
      have hjl : idx + 128 < 256 := by omega
      have ha_b := hbnd.2 idx hidx
      have hb_b := hbnd.2 (idx + 128) hjl
      have ha_m := hrep.2 idx hidx
      have hb_m := hrep.2 (idx + 128) hjl
      have ht := hmul_b (p.getD (idx + 128) 0#16) hb_b.1 hb_b.2
      have ht_mod : (p.getD (idx + 128) 0#16 * 0xf9c0#16).toInt % 3329 =
          ((1729 : Int) * (f.getD (idx + 128) 0 : Int)) % 3329 := by
        have hmod1729 : ((p.getD (idx + 128) 0#16).toInt * (-1600)) % 3329 =
            ((1729 : Int) * (p.getD (idx + 128) 0#16).toInt) % 3329 := by omega
        rw [ht, hmod1729, Int.mul_emod, hb_m, ← Int.mul_emod]
      exact (ntt_butterfly_mod ha_m ht_mod ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).1
    · simp only [hhalf, ↓reduceIte]
      have hij : idx - 128 < 256 := by omega
      have ha_b := hbnd.2 (idx - 128) hij
      have hb_b := hbnd.2 idx hidx
      have ha_m := hrep.2 (idx - 128) hij
      have hb_m := hrep.2 idx hidx
      have ht := hmul_b (p.getD idx 0#16) hb_b.1 hb_b.2
      have ht_mod : (p.getD idx 0#16 * 0xf9c0#16).toInt % 3329 =
          ((1729 : Int) * (f.getD idx 0 : Int)) % 3329 := by
        have hmod1729 : ((p.getD idx 0#16).toInt * (-1600)) % 3329 =
            ((1729 : Int) * (p.getD idx 0#16).toInt) % 3329 := by omega
        rw [ht, hmod1729, Int.mul_emod, hb_m, ← Int.mul_emod]
      exact (ntt_butterfly_mod ha_m ht_mod ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).2

/-- Full general 7-stage Montgomery NEON `NTT` (`PolyBounded16 3328` input → `PolyBounded16 1664` output). -/
theorem neonPolyNtt16_spec {p : Poly16} {f : Poly}
    (hbnd : PolyBounded16 3328 p) (hrep : PolyRepresents p f) (hf : f.size = 256) :
    (polyNtt f).size = 256 ∧
    PolyBounded16 1664 (neonPolyNtt16 p) ∧
    PolyRepresents (neonPolyNtt16 p) (polyNtt f) := by
  unfold neonPolyNtt16 polyNtt
  obtain ⟨hk1, hfk1, hfs1, hb1, hr1⟩ :=
    neonNttStage16_spec 128 1 hbnd hrep hf (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp1 : neonNttStage16 128 1 p with ⟨p1, kp1⟩
  rcases hf1 : nttStage 128 1 f with ⟨f1, kf1⟩
  rw [hp1] at hk1 hb1 hr1; rw [hf1] at hfk1 hfs1 hr1; dsimp only at *
  subst hk1; subst hfk1
  obtain ⟨hk2, hfk2, hfs2, hb2, hr2⟩ :=
    neonNttStage16_spec 64 2 hb1 hr1 hfs1 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp2 : neonNttStage16 64 2 p1 with ⟨p2, kp2⟩
  rcases hf2 : nttStage 64 2 f1 with ⟨f2, kf2⟩
  rw [hp2] at hk2 hb2 hr2; rw [hf2] at hfk2 hfs2 hr2; dsimp only at *
  subst hk2; subst hfk2
  obtain ⟨hk3, hfk3, hfs3, hb3, hr3⟩ :=
    neonNttStage16_spec 32 4 hb2 hr2 hfs2 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp3 : neonNttStage16 32 4 p2 with ⟨p3, kp3⟩
  rcases hf3 : nttStage 32 4 f2 with ⟨f3, kf3⟩
  rw [hp3] at hk3 hb3 hr3; rw [hf3] at hfk3 hfs3 hr3; dsimp only at *
  subst hk3; subst hfk3
  obtain ⟨hk4, hfk4, hfs4, hb4, hr4⟩ :=
    neonNttStage16_spec 16 8 hb3 hr3 hfs3 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp4 : neonNttStage16 16 8 p3 with ⟨p4, kp4⟩
  rcases hf4 : nttStage 16 8 f3 with ⟨f4, kf4⟩
  rw [hp4] at hk4 hb4 hr4; rw [hf4] at hfk4 hfs4 hr4; dsimp only at *
  subst hk4; subst hfk4
  obtain ⟨hk5, hfk5, hfs5, hb5, hr5⟩ :=
    neonNttStage16_spec 8 16 hb4 hr4 hfs4 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp5 : neonNttStage16 8 16 p4 with ⟨p5, kp5⟩
  rcases hf5 : nttStage 8 16 f4 with ⟨f5, kf5⟩
  rw [hp5] at hk5 hb5 hr5; rw [hf5] at hfk5 hfs5 hr5; dsimp only at *
  subst hk5; subst hfk5
  obtain ⟨hk6, hfk6, hfs6, hb6, hr6⟩ :=
    neonNttStage16_spec 4 32 hb5 hr5 hfs5 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp6 : neonNttStage16 4 32 p5 with ⟨p6, kp6⟩
  rcases hf6 : nttStage 4 32 f5 with ⟨f6, kf6⟩
  rw [hp6] at hk6 hb6 hr6; rw [hf6] at hfk6 hfs6 hr6; dsimp only at *
  subst hk6; subst hfk6
  obtain ⟨_, _, hfs7, _, hr7⟩ :=
    neonNttStage16_spec 2 64 hb6 hr6 hfs6 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp7 : neonNttStage16 2 64 p6 with ⟨p7, kp7⟩
  rcases hf7 : nttStage 2 64 f6 with ⟨f7, kf7⟩
  rw [hp7] at hr7; rw [hf7] at hfs7 hr7; dsimp only at *
  exact ⟨hfs7, neonBarrettReducePoly16_spec hr7⟩

/-- Full binomial 7-stage NEON `NTT` (`PolyBounded16 3` input → `PolyBounded16 1664` output, `B03`). -/
theorem neonPolyNttBinomial16_spec {p : Poly16} {f : Poly}
    (hbnd : PolyBounded16 3 p) (hrep : PolyRepresents p f) (hf : f.size = 256) :
    (polyNtt f).size = 256 ∧
    PolyBounded16 1664 (neonPolyNttBinomial16 p) ∧
    PolyRepresents (neonPolyNttBinomial16 p) (polyNtt f) := by
  unfold neonPolyNttBinomial16 polyNtt
  obtain ⟨hfk1, hfs1, hb1, hr1⟩ := neonNttBinomialLayer7_16_spec hbnd hrep hf
  rcases hf1 : nttStage 128 1 f with ⟨f1, kf1⟩
  rw [hf1] at hfk1 hfs1 hr1; dsimp only at *
  subst hfk1
  obtain ⟨hk2, hfk2, hfs2, hb2, hr2⟩ :=
    neonNttStage16_spec 64 2 hb1 hr1 hfs1 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp2 : neonNttStage16 64 2 (neonNttBinomialLayer7_16 p) with ⟨p2, kp2⟩
  rcases hf2 : nttStage 64 2 f1 with ⟨f2, kf2⟩
  rw [hp2] at hk2 hb2 hr2; rw [hf2] at hfk2 hfs2 hr2; dsimp only at *
  subst hk2; subst hfk2
  obtain ⟨hk3, hfk3, hfs3, hb3, hr3⟩ :=
    neonNttStage16_spec 32 4 hb2 hr2 hfs2 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp3 : neonNttStage16 32 4 p2 with ⟨p3, kp3⟩
  rcases hf3 : nttStage 32 4 f2 with ⟨f3, kf3⟩
  rw [hp3] at hk3 hb3 hr3; rw [hf3] at hfk3 hfs3 hr3; dsimp only at *
  subst hk3; subst hfk3
  obtain ⟨hk4, hfk4, hfs4, hb4, hr4⟩ :=
    neonNttStage16_spec 16 8 hb3 hr3 hfs3 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp4 : neonNttStage16 16 8 p3 with ⟨p4, kp4⟩
  rcases hf4 : nttStage 16 8 f3 with ⟨f4, kf4⟩
  rw [hp4] at hk4 hb4 hr4; rw [hf4] at hfk4 hfs4 hr4; dsimp only at *
  subst hk4; subst hfk4
  obtain ⟨hk5, hfk5, hfs5, hb5, hr5⟩ :=
    neonNttStage16_spec 8 16 hb4 hr4 hfs4 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp5 : neonNttStage16 8 16 p4 with ⟨p5, kp5⟩
  rcases hf5 : nttStage 8 16 f4 with ⟨f5, kf5⟩
  rw [hp5] at hk5 hb5 hr5; rw [hf5] at hfk5 hfs5 hr5; dsimp only at *
  subst hk5; subst hfk5
  obtain ⟨hk6, hfk6, hfs6, hb6, hr6⟩ :=
    neonNttStage16_spec 4 32 hb5 hr5 hfs5 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp6 : neonNttStage16 4 32 p5 with ⟨p6, kp6⟩
  rcases hf6 : nttStage 4 32 f5 with ⟨f6, kf6⟩
  rw [hp6] at hk6 hb6 hr6; rw [hf6] at hfk6 hfs6 hr6; dsimp only at *
  subst hk6; subst hfk6
  obtain ⟨_, _, hfs7, _, hr7⟩ :=
    neonNttStage16_spec 2 64 hb6 hr6 hfs6 (by omega) (by omega) (by decide) (by decide) (by decide)
  rcases hp7 : neonNttStage16 2 64 p6 with ⟨p7, kp7⟩
  rcases hf7 : nttStage 2 64 f6 with ⟨f7, kf7⟩
  rw [hp7] at hr7; rw [hf7] at hfs7 hr7; dsimp only at *
  exact ⟨hfs7, neonBarrettReducePoly16_spec hr7⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt

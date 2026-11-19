/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr

public section

set_option autoImplicit false

/-!
# Symbolic `RawVec` Doubling Potentials and `SessionGhost` Credit Bounds

Symbolic capacity schedules (`vecCap4Of`), `cumSmall` telescoping potentials, and `liveLarge` /
`peakLarge` upper bounds for `RawVec<T>::grow_one` (`initCap = 4`, doubling, `stride = 104, align = 8`
for `Chain` and `MessageKey`) and `SessionStructure` deallocation, parametric over
`(M : AllocCostModel) [HasFineReallocCredit M]`.
-/

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential

open CryptoGames.LibsignalSession (ReceiverChain SessionState)
open CryptoVerification.LibsignalSessionRepr (VecPin VecGhost MessageKeyGhost ChainGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost TailVecGhost SessionGhost)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FitsStep
  rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit stepEvents_rustAlloc_small stepEvents_rustAlloc_large
   stepEvents_rustRealloc_small_small stepEvents_rustRealloc_small_large
   stepEvents_rustRealloc_large_large stepEvents_rustDealloc_small stepEvents_rustDealloc_large)
export LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (fitsStep_of_fine_bounds)

/-! ## 1. Exact `RawVec` (`initCap = 4`) Doubling Schedule -/

/-- One `RawVec::grow_one` capacity transition (`0 ↦ 4`, `cap ↦ 2 * cap` for `cap > 0`). -/
@[expose] def vecCap4Next (cap : Nat) : Nat :=
  if cap = 0 then 4 else 2 * cap

/-- Capacity after pushing one element at current `(len, cap)`: grows iff `¬ (len < cap)`. -/
@[expose] def vecCap4Push (len cap : Nat) : Nat :=
  if len < cap then cap else vecCap4Next cap

/-- Exact `RawVec<T>::grow_one` capacity (`initCap = 4`, doubling) after pushing `n` elements
starting from `(len = 0, cap = 0)`. -/
@[expose] def vecCap4Of : Nat → Nat
  | 0 => 0
  | len + 1 => vecCap4Push len (vecCap4Of len)

/-- Reachable `RawVec` capacities with initial capacity `4`: `0` or `4 * 2 ^ j`. -/
@[expose] def IsPow2Cap4 (cap : Nat) : Prop :=
  cap = 0 ∨ ∃ j : Nat, cap = 4 * 2 ^ j

@[simp] theorem vecCap4Of_zero : vecCap4Of 0 = 0 := rfl

@[simp] theorem vecCap4Of_succ (len : Nat) :
    vecCap4Of (len + 1) = vecCap4Push len (vecCap4Of len) := rfl

@[simp] theorem vecCap4Of_one : vecCap4Of 1 = 4 := rfl

theorem le_vecCap4Of (n : Nat) : n ≤ vecCap4Of n := by
  induction n with
  | zero => omega
  | succ len ih =>
    rw [vecCap4Of_succ]
    unfold vecCap4Push vecCap4Next
    split
    · omega
    · split <;> omega

theorem isPow2Cap4_zero : IsPow2Cap4 0 := Or.inl rfl

theorem isPow2Cap4_four : IsPow2Cap4 4 := Or.inr ⟨0, by decide⟩

theorem isPow2Cap4_next {cap : Nat} (h : IsPow2Cap4 cap) : IsPow2Cap4 (vecCap4Next cap) := by
  unfold vecCap4Next
  rcases h with rfl | ⟨j, rfl⟩
  · simp only [↓reduceIte]
    exact isPow2Cap4_four
  · have hne : 4 * 2 ^ j ≠ 0 := by positivity
    simp only [hne, ↓reduceIte]
    refine Or.inr ⟨j + 1, ?_⟩
    rw [Nat.pow_succ]
    omega

theorem vecCap4Of_pow2 (n : Nat) : IsPow2Cap4 (vecCap4Of n) := by
  induction n with
  | zero => exact isPow2Cap4_zero
  | succ len ih =>
    rw [vecCap4Of_succ]
    unfold vecCap4Push
    split
    · exact ih
    · exact isPow2Cap4_next ih

theorem isPow2Cap4_zero_or_ge_four {cap : Nat} (h : IsPow2Cap4 cap) : cap = 0 ∨ 4 ≤ cap := by
  rcases h with rfl | ⟨j, rfl⟩
  · exact Or.inl rfl
  · have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    exact Or.inr (by omega)

theorem vecCap4Of_step_le (n : Nat) : vecCap4Of n ≤ vecCap4Of (n + 1) := by
  rw [vecCap4Of_succ]
  unfold vecCap4Push vecCap4Next
  split
  · omega
  · split <;> omega

theorem vecCap4Of_mono {m n : Nat} (hmn : m ≤ n) : vecCap4Of m ≤ vecCap4Of n := by
  induction hmn with
  | refl => omega
  | step _ ih => exact Nat.le_trans ih (vecCap4Of_step_le _)

theorem isPow2Cap4_next_le_of_lt {cap capMax : Nat}
    (hcap : IsPow2Cap4 cap) (hmax : IsPow2Cap4 capMax) (hlt : cap < capMax) :
    vecCap4Next cap ≤ capMax := by
  rcases hmax with rfl | ⟨j, rfl⟩
  · omega
  · unfold vecCap4Next
    rcases hcap with rfl | ⟨i, rfl⟩
    · simp only [↓reduceIte]
      have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
    · have hne : 4 * 2 ^ i ≠ 0 := by positivity
      simp only [hne, ↓reduceIte]
      have hpow_lt : 2 ^ i < 2 ^ j := by omega
      have hij : i < j := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hpow_lt
      have hpow_le : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hij
      rw [Nat.pow_succ] at hpow_le
      omega

theorem vecCap4Of_le_four_mul_pow {n : Nat} (j : Nat) (hn : n ≤ 4 * 2 ^ j) :
    vecCap4Of n ≤ 4 * 2 ^ j := by
  induction n with
  | zero => simp only [vecCap4Of_zero, Nat.zero_le]
  | succ len ih =>
    have ih' := ih (by omega)
    rw [vecCap4Of_succ]
    unfold vecCap4Push
    split
    · exact ih'
    · rename_i hge
      have hlen_le := le_vecCap4Of len
      have heq : vecCap4Of len = len := by omega
      have hlt : vecCap4Of len < 4 * 2 ^ j := by omega
      exact isPow2Cap4_next_le_of_lt (vecCap4Of_pow2 len) (Or.inr ⟨j, rfl⟩) hlt

theorem vecCap4Of_le_eight {n : Nat} (hn : n ≤ 8) : vecCap4Of n ≤ 8 :=
  vecCap4Of_le_four_mul_pow 1 (by simpa using hn)

theorem vecCap4Of_le_pow20 {n : Nat} (hn : n ≤ 2 ^ 20) : vecCap4Of n ≤ 2 ^ 20 :=
  vecCap4Of_le_four_mul_pow 18 (by omega)

/-- Tight non-power-of-two upper bound: for `k ≥ 5`, `vecCap4Of k ≤ 2 * k - 2`
(attained right after doubling at `k = 4 * 2 ^ j + 1`, where `vecCap4Of k = 8 * 2 ^ j = 2 * k - 2`). -/
theorem vecCap4Of_le_two_mul_sub_two {k : Nat} (hk : 5 ≤ k) :
    vecCap4Of k ≤ 2 * k - 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hm_le := le_vecCap4Of m
    rw [vecCap4Of_succ]
    unfold vecCap4Push vecCap4Next
    split
    · omega
    · split <;> omega

/-! ## 2. Per-Step `AllocEvent`s, Symbolic Potentials & Telescoping (`Vec<104>`) -/

/-- Exact `AllocEvent` list emitted by one `grow_one` step (`stride = 104, align = 8`) from `cap`
to `vecCap4Next cap`. -/
@[expose] def vec104GrowEvents (cap : Nat) : List AllocEvent :=
  if cap = 0 then rustAllocEvents (4 * 104) 8
  else rustReallocEvents (cap * 104) (2 * cap * 104) 8

/-- Per-step `cumSmall` charge of `vec104GrowEvents cap` under `HasFineReallocCredit M`. -/
@[expose] def vec104StepCumCost (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap = 0 then
    if 4 * 104 ≤ HasFineReallocCredit.smallMaxReq M then
      HasFineReallocCredit.smallAllocCost M (4 * 104)
    else
      HasFineReallocCredit.largeMetaCost M
  else
    if 2 * cap * 104 ≤ HasFineReallocCredit.smallMaxReq M then
      HasFineReallocCredit.smallReallocCost M (2 * cap * 104)
    else
      HasFineReallocCredit.largeMetaCost M

/-- Cumulative `cumSmall` upper bound along the doubling chain `0 → 4 → 8 → … → cap`. -/
@[expose] def vec104CumOfCap (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap < 4 then 0
  else if cap < 8 then vec104StepCumCost M 0
  else vec104CumOfCap M (cap / 2) + vec104StepCumCost M (cap / 2)
termination_by cap
decreasing_by omega

/-- Remaining `cumSmall` budget from current capacity `cap` up to target capacity `capMax`. -/
@[expose] def vec104CumRem (M : AllocCostModel) [HasFineReallocCredit M] (capMax cap : Nat) : Nat :=
  vec104CumOfCap M capMax - vec104CumOfCap M cap

/-- Direct-`mmap` live byte cost of a `Vec<104>` at capacity `cap`. -/
@[expose] def vec104LargeLive (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap * 104 ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M (cap * 104)

/-- Transient peak direct-`mmap` overlap across all `grow_one` doublings `0 → 4 → 8 → … → cap`. -/
@[expose] def vec104PeakLarge (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap < 4 then 0
  else if cap < 8 then vec104LargeLive M 4
  else max (vec104PeakLarge M (cap / 2))
    (vec104LargeLive M (cap / 2) + vec104LargeLive M cap)
termination_by cap
decreasing_by omega

/-- Direct-`mmap` live byte cost of a `Vec<u8>` (`align = 1`) at capacity `cap`. -/
@[expose] def bytesLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M cap

@[simp] theorem vec104CumOfCap_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    vec104CumOfCap M 0 = 0 := by
  unfold vec104CumOfCap
  simp only [Nat.reduceLT, ↓reduceIte]

@[simp] theorem vec104CumRem_zero (M : AllocCostModel) [HasFineReallocCredit M] (capMax : Nat) :
    vec104CumRem M capMax 0 = vec104CumOfCap M capMax := by
  simp only [vec104CumRem, vec104CumOfCap_zero, Nat.sub_zero]

@[simp] theorem vec104CumRem_self (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) :
    vec104CumRem M cap cap = 0 := by
  simp only [vec104CumRem, Nat.sub_self]

@[simp] theorem vec104LargeLive_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    vec104LargeLive M 0 = 0 := by
  unfold vec104LargeLive
  simp only [Nat.zero_mul, Nat.zero_le, ↓reduceIte]

@[simp] theorem vec104PeakLarge_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    vec104PeakLarge M 0 = 0 := by
  unfold vec104PeakLarge
  simp only [Nat.reduceLT, ↓reduceIte]

@[simp] theorem bytesLargeLive_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    bytesLargeLive M 0 = 0 := by
  unfold bytesLargeLive
  simp only [Nat.zero_le, ↓reduceIte]

theorem vec104CumOfCap_four (M : AllocCostModel) [HasFineReallocCredit M] :
    vec104CumOfCap M 4 = vec104StepCumCost M 0 := by
  unfold vec104CumOfCap
  simp only [Nat.reduceLT, ↓reduceIte]

theorem vec104CumOfCap_two_mul (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (hcap : 4 ≤ cap) :
    vec104CumOfCap M (2 * cap) = vec104CumOfCap M cap + vec104StepCumCost M cap := by
  conv_lhs => unfold vec104CumOfCap
  have h1 : ¬ (2 * cap < 4) := by omega
  have h2 : ¬ (2 * cap < 8) := by omega
  have hdiv : (2 * cap) / 2 = cap := by omega
  simp only [h1, h2, hdiv, ↓reduceIte]

theorem vec104CumOfCap_next (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (hcap : IsPow2Cap4 cap) :
    vec104CumOfCap M (vecCap4Next cap) = vec104CumOfCap M cap + vec104StepCumCost M cap := by
  rcases isPow2Cap4_zero_or_ge_four hcap with rfl | hge
  · simp only [vecCap4Next, ↓reduceIte, vec104CumOfCap_four, vec104CumOfCap_zero, Nat.zero_add]
  · have hne : cap ≠ 0 := by omega
    simp only [vecCap4Next, hne, ↓reduceIte]
    exact vec104CumOfCap_two_mul M hge

theorem vec104CumOfCap_pow2_mono (M : AllocCostModel) [HasFineReallocCredit M]
    {i j : Nat} (hij : i ≤ j) :
    vec104CumOfCap M (4 * 2 ^ i) ≤ vec104CumOfCap M (4 * 2 ^ j) := by
  induction hij with
  | refl => omega
  | step _ ih =>
    rename_i k _
    have hge : 4 ≤ 4 * 2 ^ k := by
      have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    have heq : 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by rw [Nat.pow_succ]; omega
    rw [heq, vec104CumOfCap_two_mul M hge]
    omega

theorem vec104CumOfCap_le_of_pow2 (M : AllocCostModel) [HasFineReallocCredit M]
    {cap capMax : Nat} (hcap : IsPow2Cap4 cap) (hmax : IsPow2Cap4 capMax) (hle : cap ≤ capMax) :
    vec104CumOfCap M cap ≤ vec104CumOfCap M capMax := by
  rcases hcap with rfl | ⟨i, rfl⟩
  · simp only [vec104CumOfCap_zero, Nat.zero_le]
  · rcases hmax with rfl | ⟨j, rfl⟩
    · have : 1 ≤ 2 ^ i := Nat.one_le_two_pow; omega
    · have hpow_le : 2 ^ i ≤ 2 ^ j := by omega
      have hij : i ≤ j := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hpow_le
      exact vec104CumOfCap_pow2_mono M hij

theorem vec104PeakLarge_four (M : AllocCostModel) [HasFineReallocCredit M] :
    vec104PeakLarge M 4 = vec104LargeLive M 4 := by
  unfold vec104PeakLarge
  simp only [Nat.reduceLT, ↓reduceIte]

theorem vec104PeakLarge_two_mul (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (hcap : 4 ≤ cap) :
    vec104PeakLarge M (2 * cap) =
      max (vec104PeakLarge M cap) (vec104LargeLive M cap + vec104LargeLive M (2 * cap)) := by
  conv_lhs => unfold vec104PeakLarge
  have h1 : ¬ (2 * cap < 4) := by omega
  have h2 : ¬ (2 * cap < 8) := by omega
  have hdiv : (2 * cap) / 2 = cap := by omega
  simp only [h1, h2, hdiv, ↓reduceIte]

theorem vec104PeakLarge_pow2_mono (M : AllocCostModel) [HasFineReallocCredit M]
    {i j : Nat} (hij : i ≤ j) :
    vec104PeakLarge M (4 * 2 ^ i) ≤ vec104PeakLarge M (4 * 2 ^ j) := by
  induction hij with
  | refl => omega
  | step _ ih =>
    rename_i k _
    have hge : 4 ≤ 4 * 2 ^ k := by
      have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    have heq : 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by rw [Nat.pow_succ]; omega
    rw [heq, vec104PeakLarge_two_mul M hge]
    exact Nat.le_trans ih (Nat.le_max_left _ _)

theorem vec104PeakLarge_le_of_pow2 (M : AllocCostModel) [HasFineReallocCredit M]
    {cap capMax : Nat} (hcap : IsPow2Cap4 cap) (hmax : IsPow2Cap4 capMax) (hle : cap ≤ capMax) :
    vec104PeakLarge M cap ≤ vec104PeakLarge M capMax := by
  rcases hcap with rfl | ⟨i, rfl⟩
  · simp only [vec104PeakLarge_zero, Nat.zero_le]
  · rcases hmax with rfl | ⟨j, rfl⟩
    · have : 1 ≤ 2 ^ i := Nat.one_le_two_pow; omega
    · have hpow_le : 2 ^ i ≤ 2 ^ j := by omega
      have hij : i ≤ j := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hpow_le
      exact vec104PeakLarge_pow2_mono M hij

theorem vec104LargeLive_le_peakLarge (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (hcap : IsPow2Cap4 cap) :
    vec104LargeLive M cap ≤ vec104PeakLarge M cap := by
  rcases hcap with rfl | ⟨j, rfl⟩
  · simp only [vec104LargeLive_zero, vec104PeakLarge_zero, Nat.le_refl]
  · cases j with
    | zero =>
      simp only [Nat.pow_zero, Nat.mul_one, vec104PeakLarge_four, Nat.le_refl]
    | succ k =>
      have hge : 4 ≤ 4 * 2 ^ k := by
        have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
      have heq : 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by rw [Nat.pow_succ]; omega
      rw [heq, vec104PeakLarge_two_mul M hge]
      omega

/-- 4-quadrant telescoping step lemma for `vec104GrowEvents cap` (`cap → vecCap4Next cap ≤ capMax`):
holds unconditionally for every `[HasFineReallocCredit M]` with zero threshold premises. -/
theorem stepEvents_vec104Grow_telescope (M : AllocCostModel) [HasFineReallocCredit M]
    {cap capMax C_max L_other P₀ : Nat} {st : M.σ}
    (hcap : IsPow2Cap4 cap) (hmax : IsPow2Cap4 capMax) (hlt : cap < capMax)
    (hcum : HasFineReallocCredit.cumSmall st + vec104CumRem M capMax cap ≤ C_max)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_other + vec104LargeLive M cap)
    (hpeak : HasFineReallocCredit.peakLarge st ≤ max P₀ (L_other + vec104PeakLarge M capMax)) :
    let st' := M.stepEvents (vec104GrowEvents cap) st
    let cap' := vecCap4Next cap
    HasFineReallocCredit.cumSmall st' + vec104CumRem M capMax cap' ≤ C_max ∧
    HasFineReallocCredit.liveLarge st' ≤ L_other + vec104LargeLive M cap' ∧
    HasFineReallocCredit.peakLarge st' ≤ max P₀ (L_other + vec104PeakLarge M capMax) := by
  have hnext_pow2 : IsPow2Cap4 (vecCap4Next cap) := isPow2Cap4_next hcap
  have hnext_le : vecCap4Next cap ≤ capMax := isPow2Cap4_next_le_of_lt hcap hmax hlt
  have hcum_next_eq : vec104CumOfCap M (vecCap4Next cap) =
      vec104CumOfCap M cap + vec104StepCumCost M cap := vec104CumOfCap_next M hcap
  have hcum_next_le : vec104CumOfCap M (vecCap4Next cap) ≤ vec104CumOfCap M capMax :=
    vec104CumOfCap_le_of_pow2 M hnext_pow2 hmax hnext_le
  have hpeak_next_le : vec104PeakLarge M (vecCap4Next cap) ≤ vec104PeakLarge M capMax :=
    vec104PeakLarge_le_of_pow2 M hnext_pow2 hmax hnext_le
  rcases isPow2Cap4_zero_or_ge_four hcap with rfl | hge4
  · -- `cap = 0 → cap' = 4`
    dsimp only [vec104GrowEvents, vecCap4Next, vec104StepCumCost] at hcum_next_eq hcum_next_le hpeak_next_le ⊢
    simp only [↓reduceIte] at hcum_next_eq hcum_next_le hpeak_next_le ⊢
    simp only [vec104LargeLive_zero, Nat.add_zero] at hlive
    by_cases hs : 4 * 104 ≤ HasFineReallocCredit.smallMaxReq M
    · rcases stepEvents_rustAlloc_small M (req := 4 * 104) (al := 8) st (by decide) (by decide) hs with
        ⟨hc, hl, hp⟩
      simp only [hs, ↓reduceIte] at hcum_next_eq
      simp only [vec104LargeLive, hs, ↓reduceIte, vec104CumRem] at hcum ⊢
      omega
    · have hgt : HasFineReallocCredit.smallMaxReq M < 4 * 104 := by omega
      rcases stepEvents_rustAlloc_large M (req := 4 * 104) (al := 8) st (by decide) hgt with ⟨hc, hl, hp⟩
      simp only [hs, ↓reduceIte] at hcum_next_eq
      have hlive4 : vec104LargeLive M 4 = HasFineReallocCredit.largeCost M (4 * 104) := by
        unfold vec104LargeLive
        simp only [hs, ↓reduceIte]
      have hp4 : HasFineReallocCredit.largeCost M (4 * 104) ≤ vec104PeakLarge M capMax := by
        rw [← hlive4, ← vec104PeakLarge_four M]
        exact hpeak_next_le
      rw [hlive4]
      simp only [vec104CumRem] at hcum ⊢
      omega
  · -- `4 ≤ cap → cap' = 2 * cap`
    have hne : cap ≠ 0 := by omega
    dsimp only [vec104GrowEvents, vecCap4Next] at hcum_next_eq hcum_next_le hpeak_next_le ⊢
    simp only [hne, ↓reduceIte] at hcum_next_eq hcum_next_le hpeak_next_le ⊢
    have hstep_cost : vec104StepCumCost M cap =
        (if 2 * cap * 104 ≤ HasFineReallocCredit.smallMaxReq M then
           HasFineReallocCredit.smallReallocCost M (2 * cap * 104)
         else HasFineReallocCredit.largeMetaCost M) := by
      unfold vec104StepCumCost
      simp only [hne, ↓reduceIte]
    have hpeak_ov :
        vec104LargeLive M cap + vec104LargeLive M (2 * cap) ≤ vec104PeakLarge M capMax := by
      rw [vec104PeakLarge_two_mul M hge4] at hpeak_next_le
      omega
    by_cases hold_s : cap * 104 ≤ HasFineReallocCredit.smallMaxReq M
    · have hlive_old : vec104LargeLive M cap = 0 := by
        unfold vec104LargeLive; simp only [hold_s, ↓reduceIte]
      rw [hlive_old] at hlive hpeak_ov
      by_cases hnew_s : 2 * cap * 104 ≤ HasFineReallocCredit.smallMaxReq M
      · -- Quadrant S → S
        rcases stepEvents_rustRealloc_small_small M
            (old := cap * 104) (new := 2 * cap * 104) (al := 8) st
            (by decide) (by omega) (by omega) hold_s (by omega) hnew_s with ⟨hc, hl, hp⟩
        have hlive_new : vec104LargeLive M (2 * cap) = 0 := by
          unfold vec104LargeLive; simp only [hnew_s, ↓reduceIte]
        simp only [hnew_s, ↓reduceIte] at hstep_cost
        rw [hlive_new]
        simp only [vec104CumRem] at hcum ⊢
        omega
      · -- Quadrant S → L
        have hnew_l : HasFineReallocCredit.smallMaxReq M < 2 * cap * 104 := by omega
        rcases stepEvents_rustRealloc_small_large M
            (old := cap * 104) (new := 2 * cap * 104) (al := 8) st
            (by decide) (by omega) (by omega) hold_s hnew_l with ⟨hc, hl, hp⟩
        have hlive_new : vec104LargeLive M (2 * cap) =
            HasFineReallocCredit.largeCost M (2 * cap * 104) := by
          unfold vec104LargeLive; simp only [hnew_s, ↓reduceIte]
        simp only [hnew_s, ↓reduceIte] at hstep_cost
        rw [hlive_new] at hpeak_ov ⊢
        simp only [vec104CumRem] at hcum ⊢
        omega
    · -- `smallMaxReq M < cap * 104 < 2 * cap * 104`: Quadrant L → L
      have hold_l : HasFineReallocCredit.smallMaxReq M < cap * 104 := by omega
      have hnew_l : HasFineReallocCredit.smallMaxReq M < 2 * cap * 104 := by omega
      have hnew_s : ¬ (2 * cap * 104 ≤ HasFineReallocCredit.smallMaxReq M) := by omega
      rcases stepEvents_rustRealloc_large_large M
          (old := cap * 104) (new := 2 * cap * 104) (al := 8) st
          (by decide) (by omega) hold_l hnew_l with ⟨hc, hl, hp⟩
      have hlive_old : vec104LargeLive M cap = HasFineReallocCredit.largeCost M (cap * 104) := by
        unfold vec104LargeLive; simp only [hold_s, ↓reduceIte]
      have hlive_new : vec104LargeLive M (2 * cap) =
          HasFineReallocCredit.largeCost M (2 * cap * 104) := by
        unfold vec104LargeLive; simp only [hnew_s, ↓reduceIte]
      simp only [hnew_s, ↓reduceIte] at hstep_cost
      rw [hlive_old] at hlive hpeak_ov
      rw [hlive_new] at hpeak_ov ⊢
      simp only [vec104CumRem] at hcum ⊢
      omega

/-- Unified push-step lemma along `len ↦ len + 1` up to `n` (`cap = vecCap4Of len`, `capMax = vecCap4Of n`):
when `len < cap` no allocation occurs (`st' = st`); when `len = cap` invokes `stepEvents_vec104Grow_telescope`. -/
theorem vec104Push_budget_step (M : AllocCostModel) [HasFineReallocCredit M]
    {len n C_max L_other P₀ : Nat} {st : M.σ}
    (hlen : len < n)
    (hcum : HasFineReallocCredit.cumSmall st + vec104CumRem M (vecCap4Of n) (vecCap4Of len) ≤ C_max)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_other + vec104LargeLive M (vecCap4Of len))
    (hpeak : HasFineReallocCredit.peakLarge st ≤ max P₀ (L_other + vec104PeakLarge M (vecCap4Of n))) :
    let cap := vecCap4Of len
    let st' := if len < cap then st else M.stepEvents (vec104GrowEvents cap) st
    HasFineReallocCredit.cumSmall st' + vec104CumRem M (vecCap4Of n) (vecCap4Of (len + 1)) ≤ C_max ∧
    HasFineReallocCredit.liveLarge st' ≤ L_other + vec104LargeLive M (vecCap4Of (len + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤ max P₀ (L_other + vec104PeakLarge M (vecCap4Of n)) := by
  dsimp only
  rw [vecCap4Of_succ]
  unfold vecCap4Push
  by_cases hlt : len < vecCap4Of len
  · simp only [hlt, ↓reduceIte]
    exact ⟨hcum, hlive, hpeak⟩
  · simp only [hlt, ↓reduceIte]
    have hle := le_vecCap4Of len
    have heq : vecCap4Of len = len := by omega
    have hn_le := le_vecCap4Of n
    have hcap_lt : vecCap4Of len < vecCap4Of n := by omega
    exact stepEvents_vec104Grow_telescope M
      (vecCap4Of_pow2 len) (vecCap4Of_pow2 n) hcap_lt hcum hlive hpeak

/-! ## 3. Symbolic Upper Bounds under `hsplit` & `hlarge` -/

/-! ## 4. Deallocation Credit Lemmas & `SessionGhost` / `SessionState` Live Potentials -/

/-- Deallocating a non-zero `Vec<104>` buffer (`align = 8`) credits `vec104LargeLive M cap` back
from `liveLarge` while leaving `cumSmall` and `peakLarge` non-increasing. -/
theorem stepEvents_free_vec104 (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (_hcap : cap ≠ 0) (st : M.σ) :
    let st' := M.stepEvents (rustDeallocEvents (cap * 104) 8) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st - vec104LargeLive M cap ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  unfold vec104LargeLive
  by_cases hs : cap * 104 ≤ HasFineReallocCredit.smallMaxReq M
  · simp only [hs, ↓reduceIte, Nat.sub_zero]
    exact stepEvents_rustDealloc_small M (req := cap * 104) (al := 8) st (by decide) hs
  · have hl : HasFineReallocCredit.smallMaxReq M < cap * 104 := by omega
    simp only [hs, ↓reduceIte]
    exact stepEvents_rustDealloc_large M (req := cap * 104) (al := 8) st (by decide) hl

/-- Deallocating a non-zero `Vec<u8>` buffer (`align = 1`) credits `bytesLargeLive M cap` back
from `liveLarge` while leaving `cumSmall` and `peakLarge` non-increasing. -/
theorem stepEvents_free_bytes (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (_hcap : cap ≠ 0) (st : M.σ) :
    let st' := M.stepEvents (rustDeallocEvents cap 1) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st - bytesLargeLive M cap ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  unfold bytesLargeLive
  by_cases hs : cap ≤ HasFineReallocCredit.smallMaxReq M
  · simp only [hs, ↓reduceIte, Nat.sub_zero]
    exact stepEvents_rustDealloc_small M (req := cap) (al := 1) st (by decide) hs
  · have hl : HasFineReallocCredit.smallMaxReq M < cap := by omega
    simp only [hs, ↓reduceIte]
    exact stepEvents_rustDealloc_large M (req := cap) (al := 1) st (by decide) hl

/-- Large-`mmap` bytes owned by a niche-capable `cap : BitVec 64` (`0` when `cap.slt 1#64 = true`,
i.e., `cap = 0#64` or `cap = noneCap`; else `bytesLargeLive M cap.toNat`). -/
@[expose] def sgnCapLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (cap : BitVec 64) : Nat :=
  if cap.slt 1#64 = true then 0 else bytesLargeLive M cap.toNat

/-- Direct-`mmap` live cost of one `MessageKeyGhost` (its four `Vec<u8>` buffers). -/
@[expose] def messageKeyLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (g : MessageKeyGhost) : Nat :=
  bytesLargeLive M g.cipher.cap.toNat +
  bytesLargeLive M g.mac.cap.toNat +
  bytesLargeLive M g.iv.cap.toNat +
  bytesLargeLive M g.seed.cap.toNat

/-- Direct-`mmap` live cost of one `(ChainGhost × ReceiverChain)` in `chainAt` (credited back
by one iteration of `drop_glue::<Vec<Chain>>`). -/
@[expose] def chainPairLargeLive (M : AllocCostModel) [HasFineReallocCredit M]
    (gc : ChainGhost × ReceiverChain) : Nat :=
  bytesLargeLive M gc.1.srk.cap.toNat +
  bytesLargeLive M gc.1.priv.cap.toNat +
  (match gc.2.chainKey with
   | none => 0
   | some _ => bytesLargeLive M gc.1.ck.cap.toNat) +
  vec104LargeLive M gc.1.mkCap.toNat +
  (gc.1.keys.map (messageKeyLargeLive M)).sum

/-- Purely ghost-indexed `ChainGhost` direct-`mmap` live cost (using `sgnCapLargeLive M cg.ck.cap`). -/
@[expose] def chainGhostLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (cg : ChainGhost) : Nat :=
  bytesLargeLive M cg.srk.cap.toNat +
  bytesLargeLive M cg.priv.cap.toNat +
  sgnCapLargeLive M cg.ck.cap +
  vec104LargeLive M cg.mkCap.toNat +
  (cg.keys.map (messageKeyLargeLive M)).sum

/-- Direct-`mmap` live cost of a `Some` `SenderChainGhost` at `ss + 0x90`. -/
@[expose] def senderChainLargeLive (M : AllocCostModel) [HasFineReallocCredit M]
    (sg : SenderChainGhost) : Nat :=
  bytesLargeLive M sg.srk.cap.toNat +
  bytesLargeLive M sg.priv.cap.toNat +
  bytesLargeLive M sg.ck.cap.toNat +
  vec104LargeLive M sg.mkCap.toNat

/-- Direct-`mmap` live cost of `Option TailVecGhost` (`pending_pre_key` / `pending_kyber_pre_key`). -/
@[expose] def optTailVecLargeLive (M : AllocCostModel) [HasFineReallocCredit M] : Option TailVecGhost → Nat
  | none => 0
  | some tg => bytesLargeLive M tg.vec.cap.toNat

/-- Exact direct-`mmap` live cost owned by `sessionStateAt A.repAlloc ss G st` and credited back
by `dropSessionStructureLocal1`. -/
@[expose] def ssStateLargeLive (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Nat :=
  bytesLargeLive M G.localIk.cap.toNat +
  bytesLargeLive M G.remoteIk.cap.toNat +
  bytesLargeLive M G.root.cap.toNat +
  (match G.sender with
   | none => 0
   | some sg => senderChainLargeLive M sg) +
  vec104LargeLive M G.chainsCap.toNat +
  ((G.chains.zip st.receiverChains).map (chainPairLargeLive M)).sum +
  optTailVecLargeLive M G.pending +
  optTailVecLargeLive M G.kyber +
  bytesLargeLive M G.alice.cap.toNat +
  bytesLargeLive M G.pq.cap.toNat

/-- Purely ghost-indexed `SessionGhost` direct-`mmap` live cost (`ssStateLargeLive` without `st`
when `none` chain-keys carry `ck.cap.slt 1#64 = true`, e.g. `0#64` or `noneCap`). -/
@[expose] def ssLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (G : SessionGhost) : Nat :=
  bytesLargeLive M G.localIk.cap.toNat +
  bytesLargeLive M G.remoteIk.cap.toNat +
  bytesLargeLive M G.root.cap.toNat +
  (match G.sender with
   | none => 0
   | some sg => senderChainLargeLive M sg) +
  vec104LargeLive M G.chainsCap.toNat +
  (G.chains.map (chainGhostLargeLive M)).sum +
  optTailVecLargeLive M G.pending +
  optTailVecLargeLive M G.kyber +
  bytesLargeLive M G.alice.cap.toNat +
  bytesLargeLive M G.pq.cap.toNat

/-- Transient direct-`mmap` peak during `FromRecord` exact-capacity cloning into `G'` (`__rust_alloc`
with exact lengths, no `realloc` doubling). -/
abbrev ssClonePeakLarge (M : AllocCostModel) [HasFineReallocCredit M] (G' : SessionGhost) : Nat :=
  ssLargeLive M G'

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential

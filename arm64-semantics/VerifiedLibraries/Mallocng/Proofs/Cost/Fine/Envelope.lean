/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Model

/-!
# Aggregate Stride-Sum Client Envelopes (`VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Envelope`)

- **Layer & Role**: `Role::Proof` (untrusted). Closed-form linear upper bounds on
  `mallocngFineCostModel.footprint`, `maxDynIvs`, and `stepReserve` parameterized solely by the
  aggregate peak nominal-stride byte sum `nomStrideSum bgt ≤ S` (and optional cross-class
  `realloc` stride sum `reallocStrideSum bgt ≤ R`, defaulting to `R = S` under `FineBudgetInv`
  when `realloc` is completely unrestricted), without requiring per-class counts across `0 .. 47`.
- **Key Exports**:
  - `nomStrideSum`, `reallocStrideSum`, `reallocStrideSum_le_nomStrideSum`;
  - `fineStrideSumFootprint`, `fineStrideSumMaxDynIvs`, `fineStrideSumStepReserve`;
  - `fine_footprint_le_of_strideSums`, `fine_maxDynIvs_le_of_strideSums`,
    `fine_stepReserve_le_of_strideSums`;
  - `fine_footprint_le_of_nomStrideSum`, `fine_maxDynIvs_le_of_nomStrideSum`,
    `fine_stepReserve_le_of_nomStrideSum`;
  - `fine_hashbrown_96MiB_strideSum_fits`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
  VerifiedLibraries.Mallocng.Proofs.Cost

/-! ## 1. Aggregate Nominal & Cross-Class `realloc` Stride Sums -/

/-- Aggregate peak slab stride bytes `∑_{kn < 48} slotStride kn * bgt.peakByNom[kn]`. -/
def nomStrideSum (bgt : FineBudget) : Nat :=
  ((List.range 48).map fun kn => slotStride kn * bgt.peakByNom.getD kn 0).sum

/-- Aggregate cross-class `realloc` peak slab stride bytes
    `∑_{kn < 48} slotStride kn * bgt.reallocPeakByNom[kn]`. -/
def reallocStrideSum (bgt : FineBudget) : Nat :=
  ((List.range 48).map fun kn => slotStride kn * bgt.reallocPeakByNom.getD kn 0).sum

private theorem sum_map_le_env {α : Type} {f g : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem sum_map_add_env {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem mul_sum_map_env {α : Type} (c : Nat) (f : α → Nat) (xs : List α) :
    c * (xs.map f).sum = (xs.map fun x => c * f x).sum := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, Nat.mul_add, ih]

private theorem sum_map_congr_env {α : Type} {xs : List α} {f g : α → Nat}
    (h : ∀ x ∈ xs, f x = g x) :
    (xs.map f).sum = (xs.map g).sum :=
  congrArg List.sum (List.map_congr_left h)

private theorem sum_comm_env {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    (xs.map fun x => (ys.map (f x)).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    clear f
    induction ys with
    | nil => simp
    | cons _ _ ihy => simp only [List.map_cons, List.sum_cons, ← ihy, Nat.add_zero]
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons, ih, ← sum_map_add_env]

/-- Under `FineBudgetInv bgt`, `reallocStrideSum bgt ≤ nomStrideSum bgt` automatically (requiring
    no separate `realloc` hypothesis from callers). -/
theorem reallocStrideSum_le_nomStrideSum {bgt : FineBudget} (hInv : FineBudgetInv bgt) :
    reallocStrideSum bgt ≤ nomStrideSum bgt := by
  unfold reallocStrideSum nomStrideSum
  exact sum_map_le_env fun kn hkn =>
    Nat.mul_le_mul_left _ (hInv.realloc_le_peak kn (List.mem_range.mp hkn))

/-! ## 2. Closed-Form Stride-Sum Envelope Expressions -/

/-- Closed-form upper bound on `fineSlabRootBytes` from `(nomStrideSum ≤ S, reallocStrideSum ≤ R)`
    with `excByClass = 0`. -/
def fineStrideSumSlabRootBytes (S R : Nat) : Nat :=
  (15378939904 + 2999 * S + 4113 * R) / 1024

/-- Closed-form upper bound on `fineSlabRootGroups` from `(S, R)` with `excByClass = 0`. -/
def fineStrideSumSlabRootGroups (S R : Nat) : Nat :=
  (402259968 + 668 * S + 529 * R) / 1048576

/-- Closed-form upper bound on `fineSlabGroups` from `(S, R)` with `excByClass = 0`. -/
def fineStrideSumSlabGroups (S R : Nat) : Nat :=
  (990511104 + 2458 * S + 2643 * R) / 1048576

/-- Closed-form `O(1)` footprint upper bound from `(nomStrideSum ≤ S, reallocStrideSum ≤ R)`. -/
def fineStrideSumFootprint (S R live63B live63C peak63C stradC ovB : Nat) : Nat :=
  let maxG := fineStrideSumSlabGroups S R + peak63C + stradC
  let maxM := 1 + (7 + maxG) / 101
  4096 * (3 * maxM + 2) + fineStrideSumSlabRootBytes S R +
    live63B + 8195 * live63C + 139246 * stradC + ovB

/-- Closed-form `O(1)` `maxDynIvs` upper bound from `(nomStrideSum ≤ S, reallocStrideSum ≤ R)`. -/
def fineStrideSumMaxDynIvs (S R peak63C stradC : Nat) : Nat :=
  let maxG := fineStrideSumSlabGroups S R + peak63C + stradC
  let maxM := 1 + (7 + maxG) / 101
  (3 * maxM + 2) + (fineStrideSumSlabRootGroups S R + peak63C + stradC)

/-- Closed-form `O(1)` `stepReserve` upper bound from `(nomStrideSum ≤ S, reallocStrideSum ≤ R)`. -/
def fineStrideSumStepReserve (S R peak63C stradC maxReq : Nat) : Nat :=
  let maxG := fineStrideSumSlabGroups S R + peak63C + stradC
  let maxM := 1 + (7 + maxG) / 101
  FineStepBound maxM maxReq

/-! ## 3. Pure-`Nat` Scaled Division & Fubini Reduction -/

private def ceilDiv (a b : Nat) : Nat :=
  (a + b - 1) / b

private theorem mul_div_le_ceilDiv_mul (M x d : Nat) (hd : 0 < d) :
    M * (x / d) ≤ ceilDiv M d * x := by
  unfold ceilDiv
  have hCeil : M ≤ ((M + d - 1) / d) * d := by
    have hDiv := Nat.div_add_mod (M + d - 1) d
    have hMod := Nat.mod_lt (M + d - 1) hd
    have hComm := Nat.mul_comm d ((M + d - 1) / d)
    omega
  calc
    M * (x / d)
      ≤ (((M + d - 1) / d) * d) * (x / d) := Nat.mul_le_mul_right _ hCeil
    _ = ((M + d - 1) / d) * (d * (x / d)) := by rw [Nat.mul_assoc]
    _ ≤ ((M + d - 1) / d) * x := Nat.mul_le_mul_left _ (Nat.mul_div_le x d)

private theorem point_eq_range_sum {n k : Nat} (hk : k < n) (f : Nat → Nat) :
    f k = ((List.range n).map fun i => if i == k then f i else 0).sum := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
    · have hZero : ((List.range k).map fun i => if i == k then f i else 0).sum = 0 := by
        have hEq0 : ((List.range k).map fun i => if i == k then f i else 0) =
            ((List.range k).map fun _ => 0) := by
          refine List.map_congr_left fun i hi => ?_
          have hne : i ≠ k := by have := List.mem_range.mp hi; omega
          simp [hne]
        rw [hEq0]
        clear hk ih hEq0
        induction k with
        | zero => simp
        | succ _ ihk => rw [List.range_succ, List.map_append, List.sum_append, ihk]; simp
      rw [hZero]
      simp
    · rw [← ih hlt]
      have hne : m ≠ k := by omega
      simp [hne]

private def nomCoeffOf (c : Nat → Nat) (kn : Nat) : Nat :=
  ((List.range 48).map fun sc =>
    (if kn == sc then c sc else 0) +
    (if 0 < sc && coarseBumpable (sc - 1) && kn == sc - 1 then c sc else 0)).sum

private def reallocCoeffOf (c : Nat → Nat) (kn : Nat) : Nat :=
  ((List.range 48).map fun sc =>
    if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then c sc else 0).sum

private theorem weighted_physCap_sum_le (c : Nat → Nat) (pk rp : Nat → Nat)
    {slopeS slopeR : Nat}
    (hSlopes : ∀ kn < 48,
      nomCoeffOf c kn ≤ slopeS * slotStride kn ∧
      reallocCoeffOf c kn ≤ slopeR * slotStride kn) :
    ((List.range 48).map fun sc => c sc * physCapOfNom pk rp (fun _ => 0) sc).sum ≤
      slopeS * ((List.range 48).map fun kn => slotStride kn * pk kn).sum +
      slopeR * ((List.range 48).map fun kn => slotStride kn * rp kn).sum := by
  have hExpand :
      ∀ sc ∈ List.range 48,
        c sc * physCapOfNom pk rp (fun _ => 0) sc =
          ((List.range 48).map fun kn =>
            ((if kn == sc then c sc else 0) +
             (if 0 < sc && coarseBumpable (sc - 1) && kn == sc - 1 then c sc else 0)) * pk kn +
            (if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then c sc else 0) * rp kn).sum := by
    intro sc hscR
    have hsc : sc < 48 := List.mem_range.mp hscR
    unfold physCapOfNom
    have hPk1 : pk sc = ((List.range 48).map fun kn => if kn == sc then pk kn else 0).sum :=
      point_eq_range_sum hsc pk
    have hPk2 :
        (if 0 < sc && coarseBumpable (sc - 1) then pk (sc - 1) else 0) =
          ((List.range 48).map fun kn =>
            if 0 < sc && coarseBumpable (sc - 1) && kn == sc - 1 then pk kn else 0).sum := by
      by_cases hB : (0 < sc && coarseBumpable (sc - 1)) = true
      · have hSubLt : sc - 1 < 48 := by omega
        have hPt := point_eq_range_sum hSubLt pk
        simp only [hB, ↓reduceIte, Bool.true_and]
        exact hPt
      · simp only [hB, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
        symm
        have : ((List.range 48).map fun (_ : Nat) => (0 : Nat)).sum = 0 := by decide
        exact this
    rw [Nat.add_zero, hPk1, hPk2, ← sum_map_add_env, ← sum_map_add_env, mul_sum_map_env]
    refine sum_map_congr_env fun kn _ => ?_
    simp only [Nat.mul_add, Nat.add_mul]
    congr 1
    · congr 1 <;> (split <;> simp)
    · split <;> simp
  rw [sum_map_congr_env hExpand, sum_comm_env]
  have hInnerAdd :
      ∀ kn ∈ List.range 48,
        ((List.range 48).map fun sc =>
          ((if kn == sc then c sc else 0) +
           (if 0 < sc && coarseBumpable (sc - 1) && kn == sc - 1 then c sc else 0)) * pk kn +
          (if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then c sc else 0) * rp kn).sum =
        ((List.range 48).map fun sc =>
          ((if kn == sc then c sc else 0) +
           (if 0 < sc && coarseBumpable (sc - 1) && kn == sc - 1 then c sc else 0)) * pk kn).sum +
        ((List.range 48).map fun sc =>
          (if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then c sc else 0) * rp kn).sum :=
    fun kn _ => sum_map_add_env _ _ _
  rw [sum_map_congr_env hInnerAdd, sum_map_add_env, mul_sum_map_env, mul_sum_map_env]
  refine Nat.add_le_add (sum_map_le_env fun kn hkn => ?_) (sum_map_le_env fun kn hkn => ?_)
  · have hFactor :
        ((List.range 48).map fun sc =>
          ((if kn == sc then c sc else 0) +
           (if 0 < sc && coarseBumpable (sc - 1) && kn == sc - 1 then c sc else 0)) * pk kn).sum =
        nomCoeffOf c kn * pk kn := by
      unfold nomCoeffOf
      rw [Nat.mul_comm, mul_sum_map_env]
      exact sum_map_congr_env fun _ _ => Nat.mul_comm _ _
    rw [hFactor, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (hSlopes kn (List.mem_range.mp hkn)).1
  · have hFactor :
        ((List.range 48).map fun sc =>
          (if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then c sc else 0) * rp kn).sum =
        reallocCoeffOf c kn * rp kn := by
      unfold reallocCoeffOf
      rw [Nat.mul_comm, mul_sum_map_env]
      exact sum_map_congr_env fun _ _ => Nat.mul_comm _ _
    rw [hFactor, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (hSlopes kn (List.mem_range.mp hkn)).2

/-! ## 4. Per-Class Linear Bounds on `rb`, `gr`, and `gsn + gst + gr` -/

private def occConst (sc : Nat) : Nat :=
  (fastClassParams sc).snSum +
  ((List.range 7).map fun csc => if fastSteadyParent csc == sc then 1 else 0).sum

private def rbBase1024 : Nat :=
  ((List.range 48).map fun sc =>
    let p := fastClassParams sc
    if p.hasRt then 1024 * (p.maxRb + p.ceilRs * occConst sc) else 0).sum

private def rbCapCoeff (sc : Nat) : Nat :=
  let p := fastClassParams sc
  (if p.hasRt then 1024 * p.ceilRs else 0) +
  (if sc < 7 then
    let pp := fastClassParams (fastSteadyParent sc)
    if pp.hasRt then ceilDiv (1024 * pp.ceilRs) p.stCnt else 0
   else 0)

private def grBase1M : Nat :=
  ((List.range 48).map fun sc =>
    let p := fastClassParams sc
    if p.hasRt then 1048576 + ceilDiv 1048576 p.cmRt * occConst sc else 0).sum

private def grCapCoeff (sc : Nat) : Nat :=
  let p := fastClassParams sc
  (if p.hasRt then ceilDiv 1048576 p.cmRt else 0) +
  (if sc < 7 then
    let pp := fastClassParams (fastSteadyParent sc)
    if pp.hasRt then ceilDiv (ceilDiv 1048576 pp.cmRt) p.stCnt else 0
   else 0)

private def gBase1M : Nat :=
  ((List.range 48).map fun sc =>
    let p := fastClassParams sc
    1048576 * p.msn +
    (if p.isSt then 1048576 else 0) +
    (if p.hasRt then 1048576 + ceilDiv 1048576 p.cmRt * occConst sc else 0)).sum

private def gCapCoeff (sc : Nat) : Nat :=
  let p := fastClassParams sc
  (if p.isSt then ceilDiv 1048576 p.stCnt else 0) + grCapCoeff sc

private def checkEnvelopeTables : Bool :=
  (rbBase1024 == 15378939904) &&
  (grBase1M == 402259968) &&
  (gBase1M == 990511104) &&
  ((List.range 48).all fun sc =>
    let p := fastClassParams sc
    (1 ≤ p.stCnt) && (1 ≤ p.cmRt) &&
    (if p.isSt then (sc < 7) && (occConst sc == 0) &&
      ((List.range 7).all fun csc => fastSteadyParent csc != sc)
     else true)) &&
  ((List.range 7).all fun csc => fastSteadyParent csc < 48) &&
  ((List.range 48).all fun kn =>
    (nomCoeffOf rbCapCoeff kn ≤ 2999 * slotStride kn) &&
    (reallocCoeffOf rbCapCoeff kn ≤ 4113 * slotStride kn) &&
    (nomCoeffOf grCapCoeff kn ≤ 668 * slotStride kn) &&
    (reallocCoeffOf grCapCoeff kn ≤ 529 * slotStride kn) &&
    (nomCoeffOf gCapCoeff kn ≤ 2458 * slotStride kn) &&
    (reallocCoeffOf gCapCoeff kn ≤ 2643 * slotStride kn))

private theorem checkEnvelopeTables_true : checkEnvelopeTables = true := by
  decide +kernel

private theorem envelope_table_props :
    rbBase1024 = 15378939904 ∧
    grBase1M = 402259968 ∧
    gBase1M = 990511104 ∧
    (∀ sc < 48, 1 ≤ (fastClassParams sc).stCnt ∧ 1 ≤ (fastClassParams sc).cmRt ∧
      ((fastClassParams sc).isSt = true →
        sc < 7 ∧ occConst sc = 0 ∧ ∀ csc < 7, (fastSteadyParent csc == sc) = false)) ∧
    (∀ csc < 7, fastSteadyParent csc < 48) ∧
    (∀ kn < 48,
      nomCoeffOf rbCapCoeff kn ≤ 2999 * slotStride kn ∧
      reallocCoeffOf rbCapCoeff kn ≤ 4113 * slotStride kn ∧
      nomCoeffOf grCapCoeff kn ≤ 668 * slotStride kn ∧
      reallocCoeffOf grCapCoeff kn ≤ 529 * slotStride kn ∧
      nomCoeffOf gCapCoeff kn ≤ 2458 * slotStride kn ∧
      reallocCoeffOf gCapCoeff kn ≤ 2643 * slotStride kn) := by
  have h := checkEnvelopeTables_true
  unfold checkEnvelopeTables at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, ?_, ?_, ?_⟩
  · intro sc hsc
    have hs := List.all_eq_true.mp h.1.1.2 sc (List.mem_range.mpr hsc)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    refine ⟨hs.1.1, hs.1.2, fun hIs => ?_⟩
    have hb := hs.2
    simp only [hIs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    refine ⟨hb.1.1, hb.1.2, fun csc hcsc => ?_⟩
    have hc := List.all_eq_true.mp hb.2 csc (List.mem_range.mpr hcsc)
    simpa [bne] using hc
  · intro csc hcsc
    have hc := List.all_eq_true.mp h.1.2 csc (List.mem_range.mpr hcsc)
    exact decide_eq_true_eq.mp hc
  · intro kn hkn
    have hk := List.all_eq_true.mp h.2 kn (List.mem_range.mpr hkn)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    exact ⟨hk.1.1.1.1.1, hk.1.1.1.1.2, hk.1.1.1.2, hk.1.1.2, hk.1.2, hk.2⟩

private theorem fineFastOcc_le_decomp (cap : Nat → Nat) (sc : Nat) :
    fineFastOcc cap sc ≤
      occConst sc + cap sc +
      ((List.range 7).map fun csc =>
        if fastSteadyParent csc == sc then cap csc / (fastClassParams csc).stCnt else 0).sum := by
  unfold fineFastOcc occConst fineFastSteadyGst
  dsimp only
  have hStLe :
      ((List.range 7).map fun csc =>
        if fastSteadyParent csc == sc then
          if cap csc == 0 then 0 else 1 + cap csc / (fastClassParams csc).stCnt
        else 0).sum ≤
      ((List.range 7).map fun csc => if fastSteadyParent csc == sc then 1 else 0).sum +
      ((List.range 7).map fun csc =>
        if fastSteadyParent csc == sc then cap csc / (fastClassParams csc).stCnt else 0).sum := by
    rw [← sum_map_add_env]
    refine sum_map_le_env fun csc _ => ?_
    split
    · by_cases hZ : (cap csc == 0) = true <;> simp [hZ]
    · simp
  omega

private theorem fineFastOcc_eq_cap_of_isSt (cap : Nat → Nat) {sc : Nat} (hsc : sc < 48)
    (hIs : (fastClassParams sc).isSt = true) :
    fineFastOcc cap sc = cap sc := by
  obtain ⟨_, _, _, hProps, _, _⟩ := envelope_table_props
  obtain ⟨_, hOcc0, hNoCsc⟩ := (hProps sc hsc).2.2 hIs
  unfold fineFastOcc
  dsimp only
  have hSn0 : (fastClassParams sc).snSum = 0 := by unfold occConst at hOcc0; omega
  have hSum0 :
      ((List.range 7).map fun csc =>
        if fastSteadyParent csc == sc then fineFastSteadyGst cap csc else 0).sum = 0 := by
    have hMap0 :
        ((List.range 7).map fun csc =>
          if fastSteadyParent csc == sc then fineFastSteadyGst cap csc else 0) =
        ((List.range 7).map fun _ => 0) := by
      refine List.map_congr_left fun csc hcsc => ?_
      simp [hNoCsc csc (List.mem_range.mp hcsc)]
    rw [hMap0]; decide
  omega

private theorem range_sum_le_of_le {m n : Nat} (h : m ≤ n) (f : Nat → Nat) :
    ((List.range m).map f).sum ≤ ((List.range n).map f).sum := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    omega

private theorem steady_child_sum_swap (cap : Nat → Nat) (w : Nat → Nat) :
    ((List.range 48).map fun sc =>
      ((List.range 7).map fun csc =>
        if fastSteadyParent csc == sc then
          w sc * (cap csc / (fastClassParams csc).stCnt)
        else 0).sum).sum ≤
    ((List.range 48).map fun sc =>
      (if sc < 7 then ceilDiv (w (fastSteadyParent sc)) (fastClassParams sc).stCnt else 0) *
        cap sc).sum := by
  obtain ⟨_, _, _, hProps, hParLt, _⟩ := envelope_table_props
  rw [sum_comm_env]
  have hRange7Sub :
      ((List.range 7).map fun csc =>
        ((List.range 48).map fun sc =>
          if fastSteadyParent csc == sc then w sc * (cap csc / (fastClassParams csc).stCnt) else 0).sum).sum =
    ((List.range 7).map fun csc =>
        w (fastSteadyParent csc) * (cap csc / (fastClassParams csc).stCnt)).sum := by
    refine sum_map_congr_env fun csc hcsc => ?_
    have hLt48 : fastSteadyParent csc < 48 := hParLt csc (List.mem_range.mp hcsc)
    have hPt := point_eq_range_sum hLt48 (fun sc => w sc * (cap csc / (fastClassParams csc).stCnt))
    rw [hPt]
    refine sum_map_congr_env fun sc _ => ?_
    rw [BEq.comm]
  rw [hRange7Sub]
  have hBound7 :
      ((List.range 7).map fun csc =>
        w (fastSteadyParent csc) * (cap csc / (fastClassParams csc).stCnt)).sum ≤
      ((List.range 7).map fun csc =>
        (if csc < 7 then ceilDiv (w (fastSteadyParent csc)) (fastClassParams csc).stCnt else 0) *
          cap csc).sum := by
    refine sum_map_le_env fun csc hcscR => ?_
    have hcsc : csc < 7 := List.mem_range.mp hcscR
    simp only [hcsc, ↓reduceIte]
    exact mul_div_le_ceilDiv_mul _ _ _ (hProps csc (by omega)).1
  exact Nat.le_trans hBound7 (range_sum_le_of_le (by omega) _)

private theorem scaled_rb_sum_le (cap : Nat → Nat) :
    1024 * fineFastSlabRootBytes cap ≤
      15378939904 + ((List.range 48).map fun sc => rbCapCoeff sc * cap sc).sum := by
  obtain ⟨hRbBase, _, _, hProps, _, _⟩ := envelope_table_props
  rw [← hRbBase]
  unfold fineFastSlabRootBytes rbBase1024
  dsimp only
  rw [mul_sum_map_env]
  have hPerSc :
      ∀ sc ∈ List.range 48,
        1024 * (fineFastEntry cap sc).rb ≤
          (if (fastClassParams sc).hasRt then
            1024 * ((fastClassParams sc).maxRb + (fastClassParams sc).ceilRs * occConst sc) else 0) +
          ((if (fastClassParams sc).hasRt then 1024 * (fastClassParams sc).ceilRs else 0) * cap sc +
           ((List.range 7).map fun csc =>
             if fastSteadyParent csc == sc then
               (if (fastClassParams sc).hasRt then 1024 * (fastClassParams sc).ceilRs else 0) *
                 (cap csc / (fastClassParams csc).stCnt)
             else 0).sum) := by
    intro sc _
    unfold fineFastEntry
    dsimp only
    by_cases hOcc0 : (fineFastOcc cap sc == 0) = true
    · simp [hOcc0, ClassFineBound.zero]
    · simp only [hOcc0, Bool.false_eq_true, ↓reduceIte]
      by_cases hRt : (fastClassParams sc).hasRt = true
      · simp only [hRt, ↓reduceIte, Nat.mul_add, ← Nat.mul_assoc]
        have hOcc := fineFastOcc_le_decomp cap sc
        have hMul := Nat.mul_le_mul_left (1024 * (fastClassParams sc).ceilRs) hOcc
        rw [Nat.mul_add, Nat.mul_add, mul_sum_map_env] at hMul
        have hEqMap :
            ((List.range 7).map fun csc =>
              1024 * (fastClassParams sc).ceilRs *
                (if fastSteadyParent csc == sc then cap csc / (fastClassParams csc).stCnt else 0)) =
            ((List.range 7).map fun csc =>
              if fastSteadyParent csc == sc then
                1024 * (fastClassParams sc).ceilRs * (cap csc / (fastClassParams csc).stCnt)
              else 0) := by
          refine List.map_congr_left fun csc _ => ?_
          split <;> simp
        rw [hEqMap] at hMul
        omega
      · simp [hRt]
  refine Nat.le_trans (sum_map_le_env hPerSc) ?_
  rw [sum_map_add_env, sum_map_add_env]
  have hSwap := steady_child_sum_swap cap
    (fun sc => if (fastClassParams sc).hasRt then 1024 * (fastClassParams sc).ceilRs else 0)
  have hCombine :
      ((List.range 48).map fun sc =>
        (if (fastClassParams sc).hasRt then 1024 * (fastClassParams sc).ceilRs else 0) * cap sc).sum +
      ((List.range 48).map fun sc =>
        (if sc < 7 then
          ceilDiv (if (fastClassParams (fastSteadyParent sc)).hasRt then
            1024 * (fastClassParams (fastSteadyParent sc)).ceilRs else 0) (fastClassParams sc).stCnt
         else 0) * cap sc).sum ≤
      ((List.range 48).map fun sc => rbCapCoeff sc * cap sc).sum := by
    rw [← sum_map_add_env]
    refine sum_map_le_env fun sc _ => ?_
    unfold rbCapCoeff
    dsimp only
    rw [Nat.add_mul]
    refine Nat.add_le_add (Nat.le_refl _) (Nat.mul_le_mul_right _ ?_)
    by_cases hLt7 : sc < 7
    · simp only [hLt7, ↓reduceIte]
      split
      · exact Nat.le_refl _
      · have hPos := (hProps sc (by omega)).1
        unfold ceilDiv
        exact Nat.le_of_eq (Nat.div_eq_of_lt (by omega))
    · simp [hLt7]
  exact Nat.add_le_add_left (Nat.le_trans (Nat.add_le_add_left hSwap _) hCombine) _

private theorem scaled_gr_sum_le (cap : Nat → Nat) :
    1048576 * fineFastSlabRootGroups cap ≤
      402259968 + ((List.range 48).map fun sc => grCapCoeff sc * cap sc).sum := by
  obtain ⟨_, hGrBase, _, hProps, _, _⟩ := envelope_table_props
  rw [← hGrBase]
  unfold fineFastSlabRootGroups grBase1M
  dsimp only
  rw [mul_sum_map_env]
  have hPerSc :
      ∀ sc ∈ List.range 48,
        1048576 * (fineFastEntry cap sc).gr ≤
          (if (fastClassParams sc).hasRt then
            1048576 + ceilDiv 1048576 (fastClassParams sc).cmRt * occConst sc else 0) +
          ((if (fastClassParams sc).hasRt then ceilDiv 1048576 (fastClassParams sc).cmRt else 0) * cap sc +
           ((List.range 7).map fun csc =>
             if fastSteadyParent csc == sc then
               (if (fastClassParams sc).hasRt then ceilDiv 1048576 (fastClassParams sc).cmRt else 0) *
                 (cap csc / (fastClassParams csc).stCnt)
             else 0).sum) := by
    intro sc hscR
    have hsc : sc < 48 := List.mem_range.mp hscR
    unfold fineFastEntry
    dsimp only
    by_cases hOcc0 : (fineFastOcc cap sc == 0) = true
    · simp [hOcc0, ClassFineBound.zero]
    · simp only [hOcc0, Bool.false_eq_true, ↓reduceIte]
      by_cases hRt : (fastClassParams sc).hasRt = true
      · simp only [hRt, ↓reduceIte, Nat.mul_add, Nat.mul_one]
        have hDiv := mul_div_le_ceilDiv_mul 1048576 (fineFastOcc cap sc)
          (fastClassParams sc).cmRt (hProps sc hsc).2.1
        have hOcc := fineFastOcc_le_decomp cap sc
        have hMul := Nat.mul_le_mul_left (ceilDiv 1048576 (fastClassParams sc).cmRt) hOcc
        rw [Nat.mul_add, Nat.mul_add, mul_sum_map_env] at hMul
        have hEqMap :
            ((List.range 7).map fun csc =>
              ceilDiv 1048576 (fastClassParams sc).cmRt *
                (if fastSteadyParent csc == sc then cap csc / (fastClassParams csc).stCnt else 0)) =
            ((List.range 7).map fun csc =>
              if fastSteadyParent csc == sc then
                ceilDiv 1048576 (fastClassParams sc).cmRt * (cap csc / (fastClassParams csc).stCnt)
              else 0) := by
          refine List.map_congr_left fun csc _ => ?_
          split <;> simp
        rw [hEqMap] at hMul
        omega
      · simp [hRt]
  refine Nat.le_trans (sum_map_le_env hPerSc) ?_
  rw [sum_map_add_env, sum_map_add_env]
  have hSwap := steady_child_sum_swap cap
    (fun sc => if (fastClassParams sc).hasRt then ceilDiv 1048576 (fastClassParams sc).cmRt else 0)
  have hCombine :
      ((List.range 48).map fun sc =>
        (if (fastClassParams sc).hasRt then ceilDiv 1048576 (fastClassParams sc).cmRt else 0) * cap sc).sum +
      ((List.range 48).map fun sc =>
        (if sc < 7 then
          ceilDiv (if (fastClassParams (fastSteadyParent sc)).hasRt then
            ceilDiv 1048576 (fastClassParams (fastSteadyParent sc)).cmRt else 0) (fastClassParams sc).stCnt
         else 0) * cap sc).sum ≤
      ((List.range 48).map fun sc => grCapCoeff sc * cap sc).sum := by
    rw [← sum_map_add_env]
    refine sum_map_le_env fun sc _ => ?_
    unfold grCapCoeff
    dsimp only
    rw [Nat.add_mul]
    refine Nat.add_le_add (Nat.le_refl _) (Nat.mul_le_mul_right _ ?_)
    by_cases hLt7 : sc < 7
    · simp only [hLt7, ↓reduceIte]
      split
      · exact Nat.le_refl _
      · have hPos := (hProps sc (by omega)).1
        unfold ceilDiv
        exact Nat.le_of_eq (Nat.div_eq_of_lt (by omega))
    · simp [hLt7]
  exact Nat.add_le_add_left (Nat.le_trans (Nat.add_le_add_left hSwap _) hCombine) _

private theorem gsnGst_base_eq :
    ((List.range 48).map fun sc =>
      1048576 * (fastClassParams sc).msn +
      (if (fastClassParams sc).isSt then 1048576 else 0)).sum + 402259968 = 990511104 := by
  decide +kernel

private theorem add_add_add_comm_env (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  omega

private theorem scaled_g_sum_le (cap : Nat → Nat) :
    1048576 * fineFastSlabGroups cap ≤
      990511104 + ((List.range 48).map fun sc => gCapCoeff sc * cap sc).sum := by
  obtain ⟨_, _, _, hProps, _, _⟩ := envelope_table_props
  have hGr := scaled_gr_sum_le cap
  unfold fineFastSlabGroups
  have hSplit :
      ((List.range 48).map fun sc =>
        let e := fineFastEntry cap sc
        e.gsn + e.gst + e.gr).sum =
      ((List.range 48).map fun sc => (fineFastEntry cap sc).gsn + (fineFastEntry cap sc).gst).sum +
      fineFastSlabRootGroups cap := by
    unfold fineFastSlabRootGroups
    rw [← sum_map_add_env]
  rw [hSplit, Nat.mul_add, mul_sum_map_env]
  have hGsnGst :
      ((List.range 48).map fun sc =>
        1048576 * ((fineFastEntry cap sc).gsn + (fineFastEntry cap sc).gst)).sum ≤
      ((List.range 48).map fun sc =>
        1048576 * (fastClassParams sc).msn +
        (if (fastClassParams sc).isSt then 1048576 else 0)).sum +
      ((List.range 48).map fun sc =>
        (if (fastClassParams sc).isSt then ceilDiv 1048576 (fastClassParams sc).stCnt else 0) * cap sc).sum := by
    rw [← sum_map_add_env]
    refine sum_map_le_env fun sc hscR => ?_
    have hsc : sc < 48 := List.mem_range.mp hscR
    unfold fineFastEntry
    dsimp only
    by_cases hOcc0 : (fineFastOcc cap sc == 0) = true
    · simp [hOcc0, ClassFineBound.zero]
    · simp only [hOcc0, Bool.false_eq_true, ↓reduceIte, Nat.mul_add]
      by_cases hIs : (fastClassParams sc).isSt = true
      · simp only [hIs, ↓reduceIte, Nat.mul_add, Nat.mul_one]
        rw [fineFastOcc_eq_cap_of_isSt cap hsc hIs]
        have hDiv := mul_div_le_ceilDiv_mul 1048576 (cap sc)
          (fastClassParams sc).stCnt (hProps sc hsc).1
        omega
      · simp [hIs]
  have hCoeffEq :
      ((List.range 48).map fun sc =>
        (if (fastClassParams sc).isSt then ceilDiv 1048576 (fastClassParams sc).stCnt else 0) * cap sc).sum +
      ((List.range 48).map fun sc => grCapCoeff sc * cap sc).sum =
      ((List.range 48).map fun sc => gCapCoeff sc * cap sc).sum := by
    rw [← sum_map_add_env]
    refine sum_map_congr_env fun sc _ => ?_
    unfold gCapCoeff
    dsimp only
    rw [Nat.add_mul]
  have hSum := Nat.add_le_add hGsnGst hGr
  rw [add_add_add_comm_env, gsnGst_base_eq, hCoeffEq] at hSum
  exact hSum

/-! ## 5. Public Stride-Sum Envelope Theorems -/

private theorem div_le_of_mul_le {M x y : Nat} (hM : 0 < M) (h : M * x ≤ y) :
    x ≤ y / M := by
  rw [Nat.le_div_iff_mul_le hM, Nat.mul_comm]
  exact h

private theorem rb_strideSum_bound {bgt : FineBudget} {S R : Nat}
    (hS : nomStrideSum bgt ≤ S) (hR : reallocStrideSum bgt ≤ R) :
    fineFastSlabRootBytes
        (physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
          (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0)) ≤
      fineStrideSumSlabRootBytes S R := by
  obtain ⟨_, _, _, _, _, hSlopes⟩ := envelope_table_props
  unfold fineStrideSumSlabRootBytes
  refine div_le_of_mul_le (by omega) ?_
  have h12 := Nat.le_trans
    (scaled_rb_sum_le (physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
      (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0)))
    (Nat.add_le_add_left
      (weighted_physCap_sum_le rbCapCoeff
        (fun kn => bgt.peakByNom.getD kn 0)
        (fun kn => bgt.reallocPeakByNom.getD kn 0)
        (fun kn hkn => ⟨(hSlopes kn hkn).1, (hSlopes kn hkn).2.1⟩)) _)
  unfold nomStrideSum at hS
  unfold reallocStrideSum at hR
  omega

private theorem gr_strideSum_bound {bgt : FineBudget} {S R : Nat}
    (hS : nomStrideSum bgt ≤ S) (hR : reallocStrideSum bgt ≤ R) :
    fineFastSlabRootGroups
        (physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
          (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0)) ≤
      fineStrideSumSlabRootGroups S R := by
  obtain ⟨_, _, _, _, _, hSlopes⟩ := envelope_table_props
  unfold fineStrideSumSlabRootGroups
  refine div_le_of_mul_le (by omega) ?_
  have h12 := Nat.le_trans
    (scaled_gr_sum_le (physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
      (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0)))
    (Nat.add_le_add_left
      (weighted_physCap_sum_le grCapCoeff
        (fun kn => bgt.peakByNom.getD kn 0)
        (fun kn => bgt.reallocPeakByNom.getD kn 0)
        (fun kn hkn => ⟨(hSlopes kn hkn).2.2.1, (hSlopes kn hkn).2.2.2.1⟩)) _)
  unfold nomStrideSum at hS
  unfold reallocStrideSum at hR
  omega

private theorem g_strideSum_bound {bgt : FineBudget} {S R : Nat}
    (hS : nomStrideSum bgt ≤ S) (hR : reallocStrideSum bgt ≤ R) :
    fineFastSlabGroups
        (physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
          (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0)) ≤
      fineStrideSumSlabGroups S R := by
  obtain ⟨_, _, _, _, _, hSlopes⟩ := envelope_table_props
  unfold fineStrideSumSlabGroups
  refine div_le_of_mul_le (by omega) ?_
  have h12 := Nat.le_trans
    (scaled_g_sum_le (physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
      (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0)))
    (Nat.add_le_add_left
      (weighted_physCap_sum_le gCapCoeff
        (fun kn => bgt.peakByNom.getD kn 0)
        (fun kn => bgt.reallocPeakByNom.getD kn 0)
        (fun kn hkn => ⟨(hSlopes kn hkn).2.2.2.2.1, (hSlopes kn hkn).2.2.2.2.2⟩)) _)
  unfold nomStrideSum at hS
  unfold reallocStrideSum at hR
  omega

/-- Footprint upper bound from `(nomStrideSum bgt ≤ S, reallocStrideSum bgt ≤ R)` with `excByClass = 0`. -/
theorem fine_footprint_le_of_strideSums {bgt : FineBudget}
    {S R live63B live63C peak63C stradC ovB : Nat}
    (hS : nomStrideSum bgt ≤ S)
    (hR : reallocStrideSum bgt ≤ R)
    (hExc : ∀ sc < 48, bgt.excByClass.getD sc 0 = 0)
    (hL63B : bgt.live63Bytes ≤ live63B) (hL63C : bgt.live63Count ≤ live63C)
    (hP63C : bgt.peak63Count ≤ peak63C) (hStr : bgt.straddle63Cum ≤ stradC)
    (hOv : bgt.overAlignCum ≤ ovB) :
    mallocngFineCostModel.footprint bgt ≤
      fineStrideSumFootprint S R live63B live63C peak63C stradC ovB := by
  have hCap : ∀ sc < 48, peakPhysOfBudget bgt sc ≤
      physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
        (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0) sc := fun sc hsc =>
    peakPhysOfBudget_le_physCapOfNom (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
      (fun c hc => Nat.le_of_eq (hExc c hc)) hsc
  have hFast := fine_footprint_le_of_physCap hCap hL63B hL63C hP63C hStr hOv
  have hRb := rb_strideSum_bound hS hR
  have hG := g_strideSum_bound hS hR
  refine Nat.le_trans hFast ?_
  unfold fineFastFootprint fineStrideSumFootprint
  dsimp only
  have hM : (7 + (fineFastSlabGroups (physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
        (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0)) + peak63C + stradC)) / 101 ≤
      (7 + (fineStrideSumSlabGroups S R + peak63C + stradC)) / 101 :=
    Nat.div_le_div_right (by omega)
  omega

/-- `maxDynIvs` upper bound from `(nomStrideSum bgt ≤ S, reallocStrideSum bgt ≤ R)` with `excByClass = 0`. -/
theorem fine_maxDynIvs_le_of_strideSums {bgt : FineBudget}
    {S R peak63C stradC : Nat}
    (hS : nomStrideSum bgt ≤ S)
    (hR : reallocStrideSum bgt ≤ R)
    (hExc : ∀ sc < 48, bgt.excByClass.getD sc 0 = 0)
    (hP63C : bgt.peak63Count ≤ peak63C) (hStr : bgt.straddle63Cum ≤ stradC) :
    mallocngFineCostModel.maxDynIvs bgt ≤
      fineStrideSumMaxDynIvs S R peak63C stradC := by
  have hCap : ∀ sc < 48, peakPhysOfBudget bgt sc ≤
      physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
        (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0) sc := fun sc hsc =>
    peakPhysOfBudget_le_physCapOfNom (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
      (fun c hc => Nat.le_of_eq (hExc c hc)) hsc
  have hFast := fine_maxDynIvs_le_of_physCap hCap hP63C hStr
  have hGr := gr_strideSum_bound hS hR
  have hG := g_strideSum_bound hS hR
  refine Nat.le_trans hFast ?_
  unfold fineFastMaxDynIvs fineStrideSumMaxDynIvs
  dsimp only
  have hM : (7 + (fineFastSlabGroups (physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
        (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0)) + peak63C + stradC)) / 101 ≤
      (7 + (fineStrideSumSlabGroups S R + peak63C + stradC)) / 101 :=
    Nat.div_le_div_right (by omega)
  omega

/-- `stepReserve` upper bound from `(nomStrideSum bgt ≤ S, reallocStrideSum bgt ≤ R)` with `excByClass = 0`. -/
theorem fine_stepReserve_le_of_strideSums {ev : AllocEvent} {bgt : FineBudget}
    {S R peak63C stradC maxReq : Nat}
    (hS : nomStrideSum bgt ≤ S)
    (hR : reallocStrideSum bgt ≤ R)
    (hExc : ∀ sc < 48, bgt.excByClass.getD sc 0 = 0)
    (hP63C : bgt.peak63Count ≤ peak63C) (hStr : bgt.straddle63Cum ≤ stradC)
    (hReq : evReqBytes ev ≤ maxReq) :
    mallocngFineCostModel.stepReserve ev bgt ≤
      fineStrideSumStepReserve S R peak63C stradC maxReq := by
  have hCap : ∀ sc < 48, peakPhysOfBudget bgt sc ≤
      physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
        (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0) sc := fun sc hsc =>
    peakPhysOfBudget_le_physCapOfNom (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
      (fun c hc => Nat.le_of_eq (hExc c hc)) hsc
  have hFast := fine_stepReserve_le_of_physCap hCap hP63C hStr hReq
  have hG := g_strideSum_bound hS hR
  refine Nat.le_trans hFast ?_
  unfold fineFastStepReserve fineStrideSumStepReserve
  dsimp only
  have hM : 1 + (7 + (fineFastSlabGroups (physCapOfNom (fun kn => bgt.peakByNom.getD kn 0)
        (fun kn => bgt.reallocPeakByNom.getD kn 0) (fun _ => 0)) + peak63C + stradC)) / 101 ≤
      1 + (7 + (fineStrideSumSlabGroups S R + peak63C + stradC)) / 101 :=
    Nat.add_le_add_left (Nat.div_le_div_right (by omega)) 1
  exact FineStepBound_mono hM (Nat.le_refl _)

/-- Single-parameter `nomStrideSum bgt ≤ S` footprint bound (unrestricted `realloc`, via `FineBudgetInv`). -/
theorem fine_footprint_le_of_nomStrideSum {bgt : FineBudget} (hInv : FineBudgetInv bgt)
    {S live63B live63C peak63C stradC ovB : Nat}
    (hS : nomStrideSum bgt ≤ S)
    (hExc : ∀ sc < 48, bgt.excByClass.getD sc 0 = 0)
    (hL63B : bgt.live63Bytes ≤ live63B) (hL63C : bgt.live63Count ≤ live63C)
    (hP63C : bgt.peak63Count ≤ peak63C) (hStr : bgt.straddle63Cum ≤ stradC)
    (hOv : bgt.overAlignCum ≤ ovB) :
    mallocngFineCostModel.footprint bgt ≤
      fineStrideSumFootprint S S live63B live63C peak63C stradC ovB :=
  fine_footprint_le_of_strideSums hS (Nat.le_trans (reallocStrideSum_le_nomStrideSum hInv) hS)
    hExc hL63B hL63C hP63C hStr hOv

/-- Single-parameter `nomStrideSum bgt ≤ S` `maxDynIvs` bound (unrestricted `realloc`). -/
theorem fine_maxDynIvs_le_of_nomStrideSum {bgt : FineBudget} (hInv : FineBudgetInv bgt)
    {S peak63C stradC : Nat}
    (hS : nomStrideSum bgt ≤ S)
    (hExc : ∀ sc < 48, bgt.excByClass.getD sc 0 = 0)
    (hP63C : bgt.peak63Count ≤ peak63C) (hStr : bgt.straddle63Cum ≤ stradC) :
    mallocngFineCostModel.maxDynIvs bgt ≤
      fineStrideSumMaxDynIvs S S peak63C stradC :=
  fine_maxDynIvs_le_of_strideSums hS (Nat.le_trans (reallocStrideSum_le_nomStrideSum hInv) hS)
    hExc hP63C hStr

/-- Single-parameter `nomStrideSum bgt ≤ S` `stepReserve` bound (unrestricted `realloc`). -/
theorem fine_stepReserve_le_of_nomStrideSum {ev : AllocEvent} {bgt : FineBudget}
    (hInv : FineBudgetInv bgt) {S peak63C stradC maxReq : Nat}
    (hS : nomStrideSum bgt ≤ S)
    (hExc : ∀ sc < 48, bgt.excByClass.getD sc 0 = 0)
    (hP63C : bgt.peak63Count ≤ peak63C) (hStr : bgt.straddle63Cum ≤ stradC)
    (hReq : evReqBytes ev ≤ maxReq) :
    mallocngFineCostModel.stepReserve ev bgt ≤
      fineStrideSumStepReserve S S peak63C stradC maxReq :=
  fine_stepReserve_le_of_strideSums hS (Nat.le_trans (reallocStrideSum_le_nomStrideSum hInv) hS)
    hExc hP63C hStr hReq

/-! ## 6. Hashbrown 96 MiB Aggregate-Stride-Sum Envelope (`1.28 GiB` RAM + 48-bit `VaRoom`) -/

/-- Hashbrown S2 `96 MiB` aggregate slab-stride envelope (`live63B ≤ 216 MiB`, `live63C, peak63C ≤ 32`,
    `maxReq ≤ 105 MiB`, `align ≤ 16`):
    - without cross-class `realloc` (`R = 0`), dynamic footprint `< 550 MiB` (`fp + step < 660 MiB`);
    - even with **completely unrestricted `realloc`** (`R = 96 MiB`), `fp + step < 1,080 MiB < 1,147 MiB`
      (`1,280 MiB` RAM minus `133 MiB` static image/stack) and 48-bit `VaRoom` holds! -/
theorem fine_hashbrown_96MiB_strideSum_fits :
    let S := 96 * 1048576
    fineStrideSumFootprint S 0 (216 * 1048576) 32 32 0 0 < 550 * 1048576 ∧
    fineStrideSumFootprint S S (216 * 1048576) 32 32 0 0 +
      fineStrideSumStepReserve S S 32 0 (105 * 1048576) < 1147 * 1048576 ∧
    VaRoom (133 * 1048576 + fineStrideSumFootprint S S (216 * 1048576) 32 32 0 0)
      (51 + fineStrideSumMaxDynIvs S S 32 0)
      (fineStrideSumStepReserve S S 32 0 (105 * 1048576)) := by
  dsimp only
  unfold VaRoom
  apply decide_eq_true_eq.mp
  decide +kernel

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine

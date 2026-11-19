/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Inv
public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Envelope
public import VerifiedLibraries.Mallocng.Proofs.Accounting

/-!
# Fine Dynamic Footprint & Lifecycle Lemmas (`VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Footprint`)

- **Layer & Role**: `Role::Proof` (untrusted). Connects `MallocngFineInv` + `MallocngWF` to
  `mallocngFineCostModel.footprint` and `mallocngFineCostModel.maxDynIvs`, and proves startup
  initialization, runtime splitting, `meta_area` growth (`fine_metaAreas_length_succ_le`), and
  tracked `auxv` startup/teardown for `mallocngFineIface`.
- **Key Exports**:
  - `fine_pages_le`, `fine_groups_length_le`, `fine_metaAreas_length_succ_le`
  - `fineHeap_footprint_bound`
  - `fineHeap_init_resources`, `finePlacedInit_ok`, `fineHeap_split_runtime`
  - `fineInitCore_tracked`, `fineCore_teardown_auxv`
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
  VerifiedLibraries.Mallocng.Proofs.Cost

/-! ## 1. Elementary List & Partition Combinators -/

private theorem sum_map_add_fp {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_map_zero_fp {α : Type} (xs : List α) :
    (xs.map fun _ => (0 : Nat)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]

private theorem range_point_sum_fp {N k : Nat} (hk : k < N) (v : Nat) :
    ((List.range N).map fun i => if k == i then v else 0).sum = v := by
  induction N with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | hEq
    · have hNe : (k == n) = false := beq_false_of_ne (by omega)
      simp only [List.map_singleton, List.sum_singleton, hNe, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero, ih hlt]
    · subst hEq
      have hZero : ((List.range k).map fun i => if k == i then v else 0).sum = 0 := by
        have hEqMap : ((List.range k).map fun i => if k == i then v else 0) =
            (List.range k).map (fun _ => 0) := by
          refine List.map_congr_left fun i hi => ?_
          have hltI := List.mem_range.mp hi
          have hNe : (k == i) = false := beq_false_of_ne (by omega)
          simp only [hNe, Bool.false_eq_true, ↓reduceIte]
        rw [hEqMap, sum_map_zero_fp]
      simp only [List.map_singleton, List.sum_singleton, beq_self_eq_true, ↓reduceIte, hZero,
        Nat.zero_add]

private theorem sum_by_sc_range (N : Nat) (w : GroupDesc → Nat) (gs : List GroupDesc)
    (hlt : ∀ g ∈ gs, g.sc < N) :
    (gs.map w).sum =
      ((List.range N).map fun sc => ((gs.filter (·.sc == sc)).map w).sum).sum := by
  induction gs with
  | nil =>
    simp only [List.map_nil, List.sum_nil, List.filter_nil]
    exact (sum_map_zero_fp (List.range N)).symm
  | cons g tl ih =>
    have hgLt : g.sc < N := hlt g List.mem_cons_self
    have hTl := ih fun x hx => hlt x (List.mem_cons_of_mem g hx)
    have hStep :
        ((List.range N).map fun sc => (((g :: tl).filter (·.sc == sc)).map w).sum) =
        ((List.range N).map fun sc =>
          (if g.sc == sc then w g else 0) + ((tl.filter (·.sc == sc)).map w).sum) := by
      refine List.map_congr_left fun sc _ => ?_
      by_cases h : (g.sc == sc) = true
      · simp [List.filter, h]
      · simp [List.filter, Bool.eq_false_iff.mpr h]
    simp only [List.map_cons, List.sum_cons]
    rw [hStep, sum_map_add_fp, range_point_sum_fp hgLt (w g), ← hTl]

private theorem length_eq_sum_ones {α : Type} (xs : List α) :
    xs.length = (xs.map fun _ => 1).sum := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, List.map_cons, List.sum_cons, ih]; omega

private theorem filter_filter_comm_eq {α : Type} (p q : α → Bool) (xs : List α) :
    (xs.filter p).filter q = xs.filter (fun x => q x && p x) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    by_cases hp : p x = true <;> by_cases hq : q x = true <;>
      simp [List.filter, hp, hq, Bool.eq_false_iff.mpr, ih]

private theorem filter_sub_sum_le {α : Type} {p q : α → Bool} (w : α → Nat) (xs : List α)
    (hImp : ∀ x ∈ xs, p x = true → q x = true) :
    ((xs.filter p).map w).sum ≤ ((xs.filter q).map w).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x tl ih =>
    have hTl := ih fun y hy => hImp y (List.mem_cons_of_mem x hy)
    by_cases hp : p x = true
    · have hq := hImp x List.mem_cons_self hp
      simp only [List.filter_cons, hp, hq, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · simp only [List.filter_cons, Bool.eq_false_iff.mpr hp, Bool.false_eq_true, ↓reduceIte]
      by_cases hq : q x = true
      · simp only [hq, ↓reduceIte, List.map_cons, List.sum_cons]; omega
      · simp only [Bool.eq_false_iff.mpr hq, Bool.false_eq_true, ↓reduceIte]; exact hTl

/-! ## 2. Metadata, Guard, and Available Page Bound (`fine_pages_le`) -/

private def checkFineMetaShiftBound : Bool :=
  (List.range 41).all fun m =>
    if 1 ≤ m then (m + 1) + (2 ^ m - 2) ≤ 2 * (2 ^ m - m) + 2 else true

private theorem checkFineMetaShiftBound_true : checkFineMetaShiftBound = true := by
  decide +kernel

/-- Total `metaAreas`, `guardPages`, and `availMetaPages` count is at most `fineMetaIvs bgt`
    (`3 * fineMaxMetaAreas bgt + 2`) whenever `st.metaAreas.length ≤ fineMaxMetaAreas bgt`. -/
theorem fine_pages_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {bgt : FineBudget}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hMetaLe : st.metaAreas.length ≤ fineMaxMetaAreas bgt) :
    st.metaAreas.length + st.guardPages.length + st.availMetaPages.length ≤ fineMetaIvs bgt := by
  unfold fineMetaIvs
  have ⟨_, hShift0, hShiftPos⟩ := hwf.meta_pages_bound
  by_cases hZero : st.ctx.metaAllocShift = 0#64
  · have ⟨hAvNil, hGdLe⟩ := hShift0 hZero
    have hAvLen : st.availMetaPages.length = 0 := by simp [hAvNil]
    omega
  · have hPos : 1 ≤ st.ctx.metaAllocShift.toNat := by
      have : st.ctx.metaAllocShift.toNat ≠ 0 := fun h0 => hZero (BitVec.eq_of_toNat_eq h0)
      omega
    have ⟨hmLe40, hPowLeMeta, _, hGdLe, hAvLe⟩ :=
      hShiftPos st.ctx.metaAllocShift.toNat hPos rfl
    have hCheck := List.all_eq_true.mp checkFineMetaShiftBound_true st.ctx.metaAllocShift.toNat
      (List.mem_range.mpr (by omega))
    simp only [hPos, ↓reduceIte, decide_eq_true_eq] at hCheck
    omega

/-! ## 3. Slab (`sc < 48`) and Individual-`mmap` (`sc = 63`) Group Bounds -/

private theorem group_kind_partition (g : GroupDesc) :
    (if isSmallNestedGroup g then 1 else 0) +
    (if isSteadyNestedGroup g then 1 else 0) +
    (if isRootGroup g then 1 else 0) = 1 := by
  unfold isSmallNestedGroup isSteadyNestedGroup isRootGroup
  by_cases hm : g.maplen = 0
  · simp only [hm, decide_true, Nat.lt_irrefl, decide_false, Bool.true_and]
    cases isSteadyNestedClass g.sc && decide (g.cnt = steadyCnt g.sc) <;> rfl
  · have hp : 0 < g.maplen := by omega
    simp [hm, hp]

private theorem class_groups_length_eq (st : MallocngSt) (sc : Nat) :
    (st.groups.filter (·.sc == sc)).length =
      (stClassBound st sc).gsn + (stClassBound st sc).gst + (stClassBound st sc).gr := by
  unfold stClassBound
  dsimp only
  have hStep : ∀ gs : List GroupDesc,
      (gs.filter (·.sc == sc)).length =
        (gs.filter fun g => (g.sc == sc) && isSmallNestedGroup g).length +
        (gs.filter fun g => (g.sc == sc) && isSteadyNestedGroup g).length +
        (gs.filter fun g => (g.sc == sc) && isRootGroup g).length := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g tl ih =>
      by_cases hsc : (g.sc == sc) = true
      · have hPart := group_kind_partition g
        simp only [List.filter_cons, hsc, Bool.true_and, ↓reduceIte, List.length_cons, ih]
        rcases hb1 : isSmallNestedGroup g <;> rcases hb2 : isSteadyNestedGroup g <;>
          rcases hb3 : isRootGroup g
        all_goals
          simp only [hb1, hb2, hb3, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hPart ⊢
          omega
      · have hf := Bool.eq_false_iff.mpr hsc
        simp [hf, ih]
  exact hStep st.groups

/-- Total slab groups (`sc < 48`, nested + root) are bounded by `fineSlabGroups (peakPhysOfBudget bgt)`. -/
theorem fine_slabGroups_length_le {st : MallocngSt} {bgt : FineBudget}
    (hClass : ∀ sc < 48, (stClassBound st sc).le (fineClassEntry (peakPhysOfBudget bgt) sc)) :
    (st.groups.filter fun g => decide (g.sc < 48)).length ≤
      fineSlabGroups (peakPhysOfBudget bgt) := by
  let slabGs := st.groups.filter fun g => decide (g.sc < 48)
  have hLen := sum_by_sc_range 48 (fun _ => 1) slabGs (fun g hg =>
    of_decide_eq_true (List.mem_filter.mp hg).2)
  rw [← length_eq_sum_ones] at hLen
  rw [hLen, fineSlabGroups_eq_range]
  refine accounting_sum_map_le fun sc hscR => ?_
  have hsc : sc < 48 := List.mem_range.mp hscR
  rw [← length_eq_sum_ones]
  have hEqF : slabGs.filter (·.sc == sc) = st.groups.filter (·.sc == sc) := by
    dsimp only [slabGs]
    rw [filter_filter_comm_eq]
    refine List.filter_congr fun g _ => ?_
    by_cases hEq : (g.sc == sc) = true
    · have := beq_iff_eq.mp hEq
      simp [hEq, show g.sc < 48 by omega]
    · simp [Bool.eq_false_iff.mpr hEq]
  rw [hEqF, class_groups_length_eq]
  have hB := hClass sc hsc
  exact Nat.add_le_add (Nat.add_le_add hB.1 hB.2.1) hB.2.2.1

/-- Slab root groups (`0 < maplen ∧ sc < 48`) count and mapped-byte sum are bounded by
    `fineSlabRootGroups` and `fineSlabRootBytes`. -/
theorem fine_slabRootGroups_bounds {st : MallocngSt} {bgt : FineBudget}
    (hClass : ∀ sc < 48, (stClassBound st sc).le (fineClassEntry (peakPhysOfBudget bgt) sc)) :
    let slabRoots := (st.groups.filter isRootGroup).filter (fun g => decide (g.sc < 48))
    slabRoots.length ≤ fineSlabRootGroups (peakPhysOfBudget bgt) ∧
    (slabRoots.map fun g => g.maplen * 4096).sum ≤ fineSlabRootBytes (peakPhysOfBudget bgt) := by
  dsimp only
  let slabRoots := (st.groups.filter isRootGroup).filter (fun g => decide (g.sc < 48))
  have hFilterEq : ∀ sc < 48,
      slabRoots.filter (·.sc == sc) =
        st.groups.filter (fun g => (g.sc == sc) && isRootGroup g) := by
    intro sc hsc
    dsimp only [slabRoots]
    rw [filter_filter_comm_eq, filter_filter_comm_eq]
    refine List.filter_congr fun g _ => ?_
    by_cases hEq : (g.sc == sc) = true
    · have := beq_iff_eq.mp hEq
      simp [hEq, show g.sc < 48 by omega]
    · simp [Bool.eq_false_iff.mpr hEq]
  constructor
  · have hLen := sum_by_sc_range 48 (fun _ => 1) slabRoots (fun g hg =>
      of_decide_eq_true (List.mem_filter.mp hg).2)
    rw [← length_eq_sum_ones] at hLen
    rw [hLen, fineSlabRootGroups_eq_range]
    refine accounting_sum_map_le fun sc hscR => ?_
    have hsc : sc < 48 := List.mem_range.mp hscR
    rw [← length_eq_sum_ones, hFilterEq sc hsc]
    exact (hClass sc hsc).2.2.1
  · have hBytes := sum_by_sc_range 48 (fun g => g.maplen * 4096) slabRoots (fun g hg =>
      of_decide_eq_true (List.mem_filter.mp hg).2)
    rw [hBytes, fineSlabRootBytes_eq_range]
    refine accounting_sum_map_le fun sc hscR => ?_
    have hsc : sc < 48 := List.mem_range.mp hscR
    rw [hFilterEq sc hsc]
    exact (hClass sc hsc).2.2.2

/-- Structure of a `g.sc = 63` group under `MallocngWFInflight`: single slot `g.slots = [s]` with
    `0 < g.maplen`, where `s` is either `.claimed` or `.liveUser p req eff` with
    `g.maplen * 4096 ≤ eff + 8195`. -/
private theorem sc63_group_single_slot {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hsc63 : g.sc = 63) :
    0 < g.maplen ∧
    ∃ s : SlotState, g.slots = [s] ∧
      (s = .claimed ∨ ∃ p req eff, s = .liveUser p req eff ∧ g.maplen * 4096 ≤ eff + 8195) := by
  have hGWf := hwf.groups_wf g hg
  have ⟨hLast0, hMapPos, _, _⟩ := hGWf.2.2.2.1 hsc63
  have hLen1 : g.slots.length = 1 := by
    have := hGWf.2.2.1
    simp [GroupDesc.cnt, hLast0] at this
    exact this
  have hIdx0 : 0 < g.slots.length := by omega
  have hSWf := hGWf.slot_wf 0 hIdx0
  obtain ⟨s, hsEq⟩ : ∃ s, g.slots = [s] := by
    cases hsl : g.slots with
    | nil => simp [hsl] at hLen1
    | cons s tl =>
      cases tl with
      | nil => exact ⟨s, rfl⟩
      | cons _ _ => simp [hsl] at hLen1
  have hGet0 : g.slots[0]'hIdx0 = s := by simp [hsEq]
  rw [hGet0] at hSWf
  refine ⟨hMapPos, s, hsEq, ?_⟩
  rcases hs : s with _ | _ | _ | cm | ⟨p, req, eff⟩
  · exfalso
    have hEmp : g.isEmpty = true := by simp [GroupDesc.isEmpty, hsEq, hs, SlotState.isFree]
    have ⟨_, _, hLe38, _⟩ := hwf.empty_groups_bound g hg hEmp
    omega
  · exfalso
    have hEmp : g.isEmpty = true := by simp [GroupDesc.isEmpty, hsEq, hs, SlotState.isFree]
    have ⟨_, _, hLe38, _⟩ := hwf.empty_groups_bound g hg hEmp
    omega
  · exact Or.inl rfl
  · exfalso
    rw [hs] at hSWf
    have hLt48 : g.sc < 48 := hSWf.2.2.2.2.1
    omega
  · refine Or.inr ⟨p, req, eff, rfl, ?_⟩
    rw [hs] at hSWf
    exact hSWf.2.2.2.2.2.2.2.2.2.2.2.1 hsc63

/-- Total active groups (`sc < 48` + `sc = 63`) at any `inflight` are bounded by
    `fineMaxGroups bgt + totalClaimedSlots st`. -/
theorem fine_groups_length_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {bgt : FineBudget}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hClass : ∀ sc < 48, (stClassBound st sc).le (fineClassEntry (peakPhysOfBudget bgt) sc))
    (hL63C : stLive63Count st ≤ bgt.peak63Count)
    (hStr : stStraddle63 st ≤ bgt.straddle63Cum) :
    st.groups.length ≤ fineMaxGroups bgt + totalClaimedSlots st := by
  have hPart := accounting_length_filter_partition (fun g : GroupDesc => decide (g.sc < 48)) st.groups
  have hSlab := fine_slabGroups_length_le hClass
  let largeGs := st.groups.filter (fun g => !decide (g.sc < 48))
  have hLargeEach : ∀ g ∈ largeGs,
      1 ≤ (g.slots.filter SlotState.isClaimed).length +
          (g.slots.map slotLive63Count).sum +
          (g.slots.map slotStraddle63).sum := by
    intro g hgL
    have ⟨hg, hNot48B⟩ := List.mem_filter.mp hgL
    have hsc63 : g.sc = 63 := by
      rcases (hwf.groups_wf g hg).1 with hlt | h63
      · simp [hlt] at hNot48B
      · exact h63
    obtain ⟨_, s, hsEq, hCases⟩ := sc63_group_single_slot hwf hg hsc63
    rcases hCases with rfl | ⟨p, req, eff, rfl, _⟩
    · rw [hsEq]; decide
    · simp only [hsEq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        slotLive63Count, slotStraddle63]
      by_cases hGt : MmapThresholdReq < req
      · have hNotLe : ¬ req ≤ MmapThresholdReq := by omega
        simp [hGt, hNotLe]
      · have hLe : req ≤ MmapThresholdReq := by omega
        simp [hGt, hLe]
  have hLargeLen :
      largeGs.length ≤
        (largeGs.map fun g => (g.slots.filter SlotState.isClaimed).length).sum +
        (largeGs.map fun g => (g.slots.map slotLive63Count).sum).sum +
        (largeGs.map fun g => (g.slots.map slotStraddle63).sum).sum := by
    rw [length_eq_sum_ones]
    have h1 := accounting_sum_map_le hLargeEach
    rw [sum_map_add_fp, sum_map_add_fp] at h1
    exact h1
  have hClaimSub :
      (largeGs.map fun g => (g.slots.filter SlotState.isClaimed).length).sum ≤
        totalClaimedSlots st := by
    unfold totalClaimedSlots
    have hP := accounting_sum_filter_partition (fun g : GroupDesc => decide (g.sc < 48))
      (fun g => (g.slots.filter SlotState.isClaimed).length) st.groups
    dsimp only [largeGs]
    omega
  have h63Sub :
      (largeGs.map fun g => (g.slots.map slotLive63Count).sum).sum ≤ stLive63Count st := by
    unfold stLive63Count
    have hP := accounting_sum_filter_partition (fun g : GroupDesc => decide (g.sc < 48))
      (fun g => (g.slots.map slotLive63Count).sum) st.groups
    dsimp only [largeGs]
    omega
  have hStrSub :
      (largeGs.map fun g => (g.slots.map slotStraddle63).sum).sum ≤ stStraddle63 st := by
    unfold stStraddle63
    refine filter_sub_sum_le (fun g => (g.slots.map slotStraddle63).sum) st.groups ?_
    intro g hg hNot48
    rcases (hwf.groups_wf g hg).1 with hlt | h63
    · simp [hlt] at hNot48
    · exact beq_iff_eq.mpr h63
  dsimp only [largeGs] at hLargeLen hClaimSub h63Sub hStrSub
  unfold fineMaxGroups
  omega

private theorem nodup_map_of_inj_on_fp {α β : Type} {f : α → β} {xs : List α}
    (hnd : xs.Nodup) (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    simp only [List.nodup_cons, List.map_cons] at hnd ⊢
    refine ⟨?_, ih hnd.2 fun a ha b hb =>
      hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb)⟩
    intro hMem
    obtain ⟨y, hyRest, hfy⟩ := List.mem_map.mp hMem
    have hxy := hinj y (List.mem_cons_of_mem x hyRest) x List.mem_cons_self hfy
    exact hnd.1 (hxy ▸ hyRest)

private theorem slotAddr_toNat_eq_fp (ma : MetaAreaDesc) (k : Nat)
    (hBound : ma.base.toNat + 4096 ≤ 2 ^ 48) (hk : k < 101) :
    (ma.slotAddr k).toNat = ma.base.toNat + (24 + 40 * k) := by
  have h24 : 24 + 40 * k < 2 ^ 64 := by omega
  have hSum : ma.base.toNat + (24 + 40 * k) < 2 ^ 64 := by omega
  simp only [MetaAreaDesc.slotAddr, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h24, Nat.mod_eq_of_lt hSum]

private theorem allMetaSlots_nodup_fp (mas : List MetaAreaDesc)
    (hMaNd : (mas.map (·.base)).Nodup)
    (hMaBounds : ∀ ma ∈ mas, 4096 ≤ ma.base.toNat ∧ ma.base.toNat % 4096 = 0 ∧
      ma.base.toNat + 4096 ≤ 2 ^ 48) :
    (mas.flatMap fun ma => (List.range 101).map ma.slotAddr).Nodup := by
  induction mas with
  | nil => exact List.nodup_nil
  | cons ma rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hMaNd
    simp only [List.flatMap_cons]
    have hMaB := hMaBounds ma List.mem_cons_self
    have hRestB : ∀ m' ∈ rest, 4096 ≤ m'.base.toNat ∧ m'.base.toNat % 4096 = 0 ∧
        m'.base.toNat + 4096 ≤ 2 ^ 48 :=
      fun m' hm' => hMaBounds m' (List.mem_cons_of_mem ma hm')
    have hHeadNd : ((List.range 101).map ma.slotAddr).Nodup := by
      refine nodup_map_of_inj_on_fp List.nodup_range fun k1 hk1 k2 hk2 hEq => ?_
      have hToNat := congrArg BitVec.toNat hEq
      rw [slotAddr_toNat_eq_fp ma k1 hMaB.2.2 (List.mem_range.mp hk1),
          slotAddr_toNat_eq_fp ma k2 hMaB.2.2 (List.mem_range.mp hk2)] at hToNat
      omega
    refine List.nodup_append.mpr ⟨hHeadNd, ih hMaNd.2 hRestB, fun a ha1 b hb2 hAb => ?_⟩
    subst hAb
    obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp ha1
    obtain ⟨ma2, hma2, ha2'⟩ := List.mem_flatMap.mp hb2
    obtain ⟨k2, hk2, hEq⟩ := List.mem_map.mp ha2'
    have hk1Lt : k1 < 101 := List.mem_range.mp hk1
    have hk2Lt : k2 < 101 := List.mem_range.mp hk2
    have hMa2B := hRestB ma2 hma2
    have hToNat := congrArg BitVec.toNat hEq
    rw [slotAddr_toNat_eq_fp ma k1 hMaB.2.2 hk1Lt,
        slotAddr_toNat_eq_fp ma2 k2 hMa2B.2.2 hk2Lt] at hToNat
    have hBaseNatEq : ma.base.toNat = ma2.base.toNat := by omega
    exact hMaNd.1 ((BitVec.eq_of_toNat_eq hBaseNatEq) ▸ List.mem_map_of_mem hma2)

/-- Activating one new `meta_area` page in `__malloc_alloc_meta` when `freeMetas = []` and
    `bumpMetas = []` at recursion depth `inflight ≤ 7` preserves `metaAreas.length + 1 ≤ fineMaxMetaAreas bgt`. -/
theorem fine_metaAreas_length_succ_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {bgt : FineBudget}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hInflight : inflight ≤ 7)
    (hNoFree : st.freeMetas = [])
    (hNoBump : st.bumpMetas = [])
    (hClass : ∀ sc < 48, (stClassBound st sc).le (fineClassEntry (peakPhysOfBudget bgt) sc))
    (hL63C : stLive63Count st ≤ bgt.peak63Count)
    (hStr : stStraddle63 st ≤ bgt.straddle63Cum) :
    st.metaAreas.length + 1 ≤ fineMaxMetaAreas bgt := by
  let usedAndFree :=
    st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas
  have ⟨_, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
  have hAllSlotsLen : (allMetaSlots st).length = 101 * st.metaAreas.length := by
    unfold allMetaSlots
    induction st.metaAreas with
    | nil => rfl
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
        List.length_cons]
      omega
  have hSlotNd : (allMetaSlots st).Nodup :=
    allMetaSlots_nodup_fp st.metaAreas hwf.metaAreas_wf.1
      (fun ma hma => ⟨(hwf.metaAreas_wf.2.1 ma hma).1, (hwf.metaAreas_wf.2.1 ma hma).2.1,
        (hwf.metaAreas_wf.2.1 ma hma).2.2.1⟩)
  have hSlotsLeUf : (allMetaSlots st).length ≤ usedAndFree.length :=
    nodup_length_le_of_subset hSlotNd (fun m hm => (hUfIff m).mpr hm)
  have hGsLe := fine_groups_length_le hwf hClass hL63C hStr
  have hInfBound := hwf.inflight_wf
  have hUfLen : usedAndFree.length = st.groups.length + st.reservedMetas.length := by
    simp [usedAndFree, hNoFree, hNoBump]
  unfold fineMaxMetaAreas
  omega

/-- Quiescent (`totalClaimedSlots st = 0`) bounds on `g.sc = 63` mapped root groups. -/
theorem fine_largeRootGroups_bounds {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {bgt : FineBudget}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    (hFine : MallocngFineInv bgt (dynamicRootRegions st) st) :
    let largeRoots := (st.groups.filter isRootGroup).filter (fun g => !decide (g.sc < 48))
    largeRoots.length ≤ bgt.peak63Count + bgt.straddle63Cum ∧
    (largeRoots.map fun g => g.maplen * 4096).sum ≤
      bgt.live63Bytes + 8195 * bgt.live63Count +
      139246 * bgt.straddle63Cum + bgt.overAlignCum := by
  dsimp only
  let largeRoots := (st.groups.filter isRootGroup).filter (fun g => !decide (g.sc < 48))
  have hClaim0 : totalClaimedSlots st = 0 := by have := hwf.inflight_wf; omega
  have hNoClaim : ∀ g ∈ st.groups, ∀ s ∈ g.slots, s ≠ .claimed := by
    intro g hg s hs hEq
    have hMemF : s ∈ g.slots.filter SlotState.isClaimed :=
      List.mem_filter.mpr ⟨hs, by simp [hEq, SlotState.isClaimed]⟩
    have hPos : 1 ≤ (g.slots.filter SlotState.isClaimed).length := List.length_pos_of_mem hMemF
    have hLe := accounting_le_sum_of_mem
      (List.mem_map_of_mem (f := fun h => (h.slots.filter SlotState.isClaimed).length) hg)
    unfold totalClaimedSlots at hClaim0
    omega
  have hSubGroups : ∀ p : GroupDesc → Bool, ∀ w : GroupDesc → Nat,
      (∀ g ∈ largeRoots, p g = true) →
      (largeRoots.map w).sum ≤ ((st.groups.filter p).map w).sum := by
    intro p w hImp
    dsimp only [largeRoots]
    rw [filter_filter_comm_eq]
    refine filter_sub_sum_le w st.groups fun g hg hCond => ?_
    exact hImp g (by dsimp only [largeRoots]; rw [filter_filter_comm_eq]; exact List.mem_filter.mpr ⟨hg, hCond⟩)
  have hSubAll : ∀ w : GroupDesc → Nat, (largeRoots.map w).sum ≤ (st.groups.map w).sum := by
    intro w
    have h := hSubGroups (fun _ => true) w (fun _ _ => rfl)
    have hFT : ∀ xs : List GroupDesc, xs.filter (fun _ => true) = xs := by
      intro xs; induction xs with | nil => rfl | cons _ _ ih => simp [List.filter, ih]
    rw [hFT] at h
    exact h
  have hEach : ∀ g ∈ largeRoots,
      1 ≤ (g.slots.map slotLive63Count).sum + (g.slots.map slotStraddle63).sum ∧
      g.maplen * 4096 ≤
        (g.slots.map slotLive63Bytes).sum +
        8195 * (g.slots.map slotLive63Count).sum +
        139246 * (g.slots.map slotStraddle63).sum +
        (g.slots.map slotOverAlign).sum := by
    intro g hgL
    have ⟨hgRoot, hNot48⟩ := List.mem_filter.mp hgL
    have hg : g ∈ st.groups := (List.mem_filter.mp hgRoot).1
    have hsc63 : g.sc = 63 := by
      rcases (hwf.groups_wf g hg).1 with hlt | h63
      · simp [hlt] at hNot48
      · exact h63
    obtain ⟨_, s, hsEq, hCases⟩ := sc63_group_single_slot hwf hg hsc63
    rcases hCases with rfl | ⟨p, req, eff, rfl, hMapLe⟩
    · exact False.elim (hNoClaim g hg .claimed (by simp [hsEq]) rfl)
    · simp only [hsEq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        slotLive63Count, slotLive63Bytes, slotStraddle63, slotOverAlign]
      by_cases hGt : MmapThresholdReq < req
      · have hNotLe : ¬ req ≤ MmapThresholdReq := by omega
        have hMaxEq : max req MallocngMinBlockCost = req := by
          unfold MmapThresholdReq at hGt
          unfold MallocngMinBlockCost
          omega
        simp only [hGt, hNotLe, ↓reduceIte, hMaxEq]
        omega
      · have hLe : req ≤ MmapThresholdReq := by omega
        have hMaxLe : max req MallocngMinBlockCost ≤ 131051 := by
          unfold MmapThresholdReq at hLe
          unfold MallocngMinBlockCost
          omega
        simp only [hGt, hLe, ↓reduceIte]
        omega
  have h63Imp : ∀ g ∈ largeRoots, (g.sc == 63) = true := by
    intro g hgL
    have ⟨hgRoot, hNot48⟩ := List.mem_filter.mp hgL
    have hg := (List.mem_filter.mp hgRoot).1
    rcases (hwf.groups_wf g hg).1 with hlt | h63
    · simp [hlt] at hNot48
    · exact beq_iff_eq.mpr h63
  constructor
  · rw [length_eq_sum_ones]
    have h1 := accounting_sum_map_le (fun g hg => (hEach g hg).1)
    rw [sum_map_add_fp] at h1
    have hC := hSubAll (fun g => (g.slots.map slotLive63Count).sum)
    have hS := hSubGroups (·.sc == 63) (fun g => (g.slots.map slotStraddle63).sum) h63Imp
    dsimp only [largeRoots] at h1 hC hS
    have hC' : (st.groups.map fun g => (g.slots.map slotLive63Count).sum).sum = stLive63Count st := rfl
    have hS' : ((st.groups.filter (·.sc == 63)).map fun g => (g.slots.map slotStraddle63).sum).sum =
        stStraddle63 st := rfl
    rw [hC'] at hC
    rw [hS'] at hS
    have hL63Le := Nat.le_trans hFine.live63Count_le hFine.budget_inv.live63Count_le
    have hStrLe := hFine.straddle63_le
    omega
  · have h1 := accounting_sum_map_le (fun g hg => (hEach g hg).2)
    rw [sum_map_add_fp, sum_map_add_fp, sum_map_add_fp] at h1
    have hB : (largeRoots.map fun g => (g.slots.map slotLive63Bytes).sum).sum ≤ stLive63Bytes st :=
      hSubAll (fun g => (g.slots.map slotLive63Bytes).sum)
    have hC :
        (largeRoots.map fun g => 8195 * (g.slots.map slotLive63Count).sum).sum ≤
          8195 * stLive63Count st := by
      have hMul : ∀ xs : List GroupDesc,
          (xs.map fun g => 8195 * (g.slots.map slotLive63Count).sum).sum =
            8195 * (xs.map fun g => (g.slots.map slotLive63Count).sum).sum := by
        intro xs; induction xs with
        | nil => rfl
        | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
      rw [hMul]
      exact Nat.mul_le_mul_left 8195 (hSubAll _)
    have hS :
        (largeRoots.map fun g => 139246 * (g.slots.map slotStraddle63).sum).sum ≤
          139246 * stStraddle63 st := by
      have hMul : ∀ xs : List GroupDesc,
          (xs.map fun g => 139246 * (g.slots.map slotStraddle63).sum).sum =
            139246 * (xs.map fun g => (g.slots.map slotStraddle63).sum).sum := by
        intro xs; induction xs with
        | nil => rfl
        | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
      rw [hMul]
      exact Nat.mul_le_mul_left 139246 (hSubGroups (·.sc == 63) _ h63Imp)
    have hO : (largeRoots.map fun g => (g.slots.map slotOverAlign).sum).sum ≤ stOverAlign st :=
      hSubAll (fun g => (g.slots.map slotOverAlign).sum)
    dsimp only [largeRoots] at h1 hB hC hS hO
    have := hFine.live63Bytes_le
    have := hFine.live63Count_le
    have := hFine.straddle63_le
    have := hFine.overAlign_le
    omega

/-! ## 4. Main Dynamic Footprint Bound (`fineHeap_footprint_bound`) -/

private theorem sum_snd_const_fp {α : Type} (f : α → BitVec 64) (c : Nat) (xs : List α) :
    ((xs.map fun x => (f x, c)).map Prod.snd).sum = c * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.mul_succ, Nat.add_comm]

private theorem holds_sepConj_right_fp {P Q : SepProp} {h : Heap}
    (hh : (P ∗ Q).holds h) : ∃ h₂, Q.holds h₂ := by
  rw [sepConj_comm] at hh
  exact SepProp.holds_sepConj_left hh

/-- Mode-parameterized dynamic footprint bound for `(mallocngFineCostModel, mallocngFineModeIface ro)`. -/
theorem fineHeapMode_footprint_bound (ro : Bool)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds ((mallocngFineModeIface ro).HeapM γ A tp brkStart brk bgt ivs) h) :
    ivs.length ≤ mallocngFineCostModel.maxDynIvs bgt ∧
    (ivs.map Prod.snd).sum ≤ mallocngFineCostModel.footprint bgt ∧
    ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48 := by
  have hFineH : (FineHeapModeImpl ro γ A tp brkStart brk bgt ivs).holds h := by
    have hEq : (mallocngFineModeIface ro).HeapM γ A tp brkStart brk bgt ivs =
        FineHeapModeImpl ro γ A tp brkStart brk bgt ivs := by
      cases ro <;> rfl
    rwa [← hEq]
  unfold FineHeapModeImpl FineCoreModeImpl MallocngCoreStModeA MallocngCoreStInflightModeA at hFineH
  obtain ⟨_, hCoreH⟩ := SepProp.holds_sepConj_left hFineH
  obtain ⟨_, hExSt⟩ := holds_sepConj_right_fp hCoreH
  obtain ⟨st, hExBc⟩ := SepProp.holds_sepExists hExSt
  obtain ⟨bCoarse, hPureAnd⟩ := SepProp.holds_sepExists hExBc
  obtain ⟨⟨_, hFine0⟩, hWfRest⟩ := SepProp.holds_pure_sepConj hPureAnd
  obtain ⟨hwf, _⟩ := SepProp.holds_pure_sepConj hWfRest
  have hIvsEq := hFine0.ivs_eq
  subst hIvsEq
  have hWrap : ∀ iv ∈ dynamicRootRegions st, iv.1.toNat + iv.2 ≤ 2 ^ 48 := by
    intro iv hiv
    unfold dynamicRootRegions at hiv
    simp only [List.mem_append, List.mem_map] at hiv
    rcases hiv with ((⟨ma, hma, rfl⟩ | ⟨gp, hgp, rfl⟩) | ⟨ap, hap, rfl⟩) | ⟨g, hgF, rfl⟩
    · exact (hwf.metaAreas_wf.2.1 ma hma).2.2.1
    · exact (hwf.guard_avail_wf.2.1 gp hgp).2.2
    · exact (hwf.guard_avail_wf.2.2.2 ap hap).2.2.1
    · have ⟨hg, hPosB⟩ := List.mem_filter.mp hgF
      have hPos : 0 < g.maplen := of_decide_eq_true hPosB
      have hTot := (hwf.groups_wf g hg).2.2.2.2.2.2.1
      simpa [GroupDesc.totalBytes, hPos] using hTot
  have hPages := fine_pages_le hwf hFine0.meta_le
  have ⟨hSlabGr, hSlabRb⟩ := fine_slabRootGroups_bounds hFine0.class_bounds
  have ⟨hLargeGr, hLargeRb⟩ := fine_largeRootGroups_bounds hwf hFine0
  have hRootLen := accounting_length_filter_partition (fun g => decide (g.sc < 48))
    (st.groups.filter isRootGroup)
  have hRootSum := accounting_sum_filter_partition (fun g => decide (g.sc < 48))
    (fun g => g.maplen * 4096) (st.groups.filter isRootGroup)
  have hDynLen :
      (dynamicRootRegions st).length =
        (st.metaAreas.length + st.guardPages.length + st.availMetaPages.length) +
        (st.groups.filter isRootGroup).length := by
    unfold dynamicRootRegions isRootGroup
    simp only [List.length_append, List.length_map]
  have hDynSum :
      ((dynamicRootRegions st).map Prod.snd).sum =
        4096 * (st.metaAreas.length + st.guardPages.length + st.availMetaPages.length) +
        ((st.groups.filter isRootGroup).map fun g => g.maplen * 4096).sum := by
    unfold dynamicRootRegions isRootGroup
    simp only [List.map_append, List.sum_append, sum_snd_const_fp]
    have hMapSnd :
        (((st.groups.filter fun g => decide (0 < g.maplen)).map fun g => (g.mem, g.maplen * 4096)).map Prod.snd) =
        ((st.groups.filter fun g => decide (0 < g.maplen)).map fun g => g.maplen * 4096) := by
      rw [List.map_map]; rfl
    rw [hMapSnd]
    omega
  refine ⟨?_, ?_, hWrap⟩
  · show (dynamicRootRegions st).length ≤ fineMaxDynIvs bgt
    unfold fineMaxDynIvs fineMaxRootGroups
    omega
  · show ((dynamicRootRegions st).map Prod.snd).sum ≤ fineFootprint bgt
    unfold fineFootprint
    omega

/-- Discharges `MallocngCostModelSound.heap_footprint_bound` for `(mallocngFineCostModel, mallocngFineIface)`. -/
theorem fineHeap_footprint_bound
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (mallocngFineIface.HeapM γ A tp brkStart brk bgt ivs) h) :
    ivs.length ≤ mallocngFineCostModel.maxDynIvs bgt ∧
    (ivs.map Prod.snd).sum ≤ mallocngFineCostModel.footprint bgt ∧
    ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48 :=
  fineHeapMode_footprint_bound false γ A tp brkStart brk bgt ivs h hHolds

/-- Discharges `MallocngCostModelSound.heap_footprint_bound` for `(mallocngFineCostModel, mallocngFineRoIface)`. -/
theorem fineHeapRo_footprint_bound
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (mallocngFineRoIface.HeapM γ A tp brkStart brk bgt ivs) h) :
    ivs.length ≤ mallocngFineCostModel.maxDynIvs bgt ∧
    (ivs.map Prod.snd).sum ≤ mallocngFineCostModel.footprint bgt ∧
    ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48 :=
  fineHeapMode_footprint_bound true γ A tp brkStart brk bgt ivs h hHolds

/-! ## 5. Startup, Runtime Split, and Tracked `auxv` Lifecycle Lemmas -/

/-- `FineHeapImpl` splits definitionally into `FineCoreImpl ∗ MallocngRuntime`. -/
theorem fineHeap_split_runtime
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    mallocngFineIface.HeapM γ A tp brkStart brk bgt ivs =
      (mallocngFineIface.CoreM γ A brkStart brk bgt ivs ∗ MallocngRuntime A tp) :=
  rfl

/-- Discharges `MallocngCostModelSound.init_resources` for `(mallocngFineCostModel, mallocngFineIface)`. -/
theorem fineHeap_init_resources
    (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (hTpGe : 0xa4 ≤ tp.toNat) (hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngStartupResources A tp ⊢
      |==> (∃∗ γ : GhostName, mallocngFineIface.HeapM γ A tp brkStart brkStart
        mallocngFineCostModel.init []) :=
  Entails.trans (mallocngInitResources_ok A tp brkStart hTpGe hTpLe hBrkWf)
    (bupd_mono (Entails.sepExists_mono fun γ => coarseZero_to_fineHeap γ A tp brkStart brkStart))

/-- Discharges `MallocngCostModelSound.init` for `(mallocngFineCostModel, mallocngFineIface)`. -/
theorem finePlacedInit_ok
    (mpl : Obj.MultiPlacement) (tp brkStart auxvPtr : BitVec 64) (R : SepProp) (m : Memory)
    (hTpGe : 0xa4 ≤ tp.toNat) (hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart)
    (hSat : m ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime (mallocngAddrsOfPlacement mpl) tp ∗
      (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      m ⊨ |==> (mallocngFineIface.HeapM γ (mallocngAddrsOfPlacement mpl) tp brkStart brkStart
        mallocngFineCostModel.init [] ∗ R) := by
  obtain ⟨γ, hγ⟩ := mallocngPlacedInit_ok mpl tp brkStart auxvPtr R m hTpGe hTpLe hBrkWf hSat
  exact ⟨γ, Satisfies.of_entails hγ (bupd_mono (sepConj_mono_left
    (coarseZero_to_fineHeap γ (mallocngAddrsOfPlacement mpl) tp brkStart brkStart)))⟩

/-- Tracked startup initialization for `mallocngFineIface.CoreM` (preserving concrete `auxv` ticket
    for C CLI teardown). -/
theorem fineInitCore_tracked
    (A : MallocngAddrs) (brkStart auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) (nullVal sec : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart)
    (hPreTags : ∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hSufTags : ∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hLen64 : preEntries.length + sufEntries.length ≤ 64)
    (hAuxvFit : auxvPtr.toNat + 16 * (preEntries.length + sufEntries.length + 2) ≤ 2 ^ 48)
    (hRandFit : randPtr.toNat + 16 ≤ 2 ^ 48) :
    MallocngRoTablesAt A ∗ (A.ctx ↦ₛ List.replicate 928 0#8) ∗ (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    (auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
      fun (t, v) => [t, v])) ∗ ((randPtr + 8#64) ↦₆₄ sec) ⊢
      |==> (∃∗ γ : GhostName,
        mallocngFineIface.CoreM γ A brkStart brkStart mallocngFineCostModel.init [] ∗
        MallocngAuxvTicket γ auxvPtr (preEntries, randPtr, sufEntries, nullVal, sec)) :=
  Entails.trans
    (mallocngInitCore_tracked A brkStart auxvPtr preEntries randPtr sufEntries nullVal sec
      hBrkWf hPreTags hSufTags hLen64 hAuxvFit hRandFit)
    (bupd_mono (Entails.sepExists_mono fun γ =>
      sepConj_mono_left (coarseZero_to_fineCore γ A brkStart brkStart)))

/-- Tracked `auxv` teardown for `mallocngFineIface.CoreM` paired with `MallocngAuxvTicket`. -/
theorem fineCore_teardown_auxv
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat))
    (auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) (nullVal sec : BitVec 64) :
    mallocngFineIface.CoreM γ A brkStart brk bgt ivs ∗
    MallocngAuxvTicket γ auxvPtr (preEntries, randPtr, sufEntries, nullVal, sec) ⊢
      ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
      (auxvPtr ↦₆₄*
        ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
          fun (t, v) => [t, v])) ∗
      ((randPtr + 8#64) ↦₆₄ sec) ∗
      ∃∗ R_dead : SepProp, R_dead := by
  refine Entails.trans (sepConj_mono_left (fineCore_to_coarse γ A brkStart brk bgt ivs)) ?_
  rw [sepExists_sepConj_left]
  exact Entails.sepExists_elim fun bCoarse =>
    mallocngCore_teardown_auxv γ A brkStart brk bCoarse ivs
      auxvPtr preEntries randPtr sufEntries nullVal sec

/-! ## 6. Duplicable-RO-`auxv` Startup & Runtime Split (`mallocngFineRoIface`) -/

/-- `FineHeapRoImpl` splits definitionally into `FineCoreRoImpl ∗ MallocngRuntime`. -/
theorem fineHeapRo_split_runtime
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    mallocngFineRoIface.HeapM γ A tp brkStart brk bgt ivs =
      (mallocngFineRoIface.CoreM γ A brkStart brk bgt ivs ∗ MallocngRuntime A tp) :=
  rfl

/-- Discharges `MallocngCostModelSound.init_resources` for `(mallocngFineCostModel, mallocngFineRoIface)`. -/
theorem fineHeapRo_init_resources
    (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (hTpGe : 0xa4 ≤ tp.toNat) (hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngStartupResources A tp ⊢
      |==> (∃∗ γ : GhostName, mallocngFineRoIface.HeapM γ A tp brkStart brkStart
        mallocngFineCostModel.init []) :=
  Entails.trans (mallocngRoInit_resources A tp brkStart hTpGe hTpLe hBrkWf)
    (bupd_mono (Entails.sepExists_mono fun γ => coarseZeroRo_to_fineHeapRo γ A tp brkStart brkStart))

/-- Discharges `MallocngCostModelSound.init` for `(mallocngFineCostModel, mallocngFineRoIface)`
    (backwards-compatible RW startup freezing `__libc.auxv` and `MallocngAuxvAt` to `.ro`). -/
theorem finePlacedRoInit_ok
    (mpl : Obj.MultiPlacement) (tp brkStart auxvPtr : BitVec 64) (R : SepProp) (m : Memory)
    (hTpGe : 0xa4 ≤ tp.toNat) (hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart)
    (hSat : m ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime (mallocngAddrsOfPlacement mpl) tp ∗
      (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      m ⊨ |==> (mallocngFineRoIface.HeapM γ (mallocngAddrsOfPlacement mpl) tp brkStart brkStart
        mallocngFineCostModel.init [] ∗ R) := by
  obtain ⟨γ, hγ⟩ := mallocngRoInit_ok mpl tp brkStart auxvPtr R m hTpGe hTpLe hBrkWf hSat
  exact ⟨γ, Satisfies.of_entails hγ (bupd_mono (sepConj_mono_left
    (coarseZeroRo_to_fineHeapRo γ (mallocngAddrsOfPlacement mpl) tp brkStart brkStart)))⟩

/-- Direct RO startup initialization for `mallocngFineRoIface` from already-frozen
    `((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗ MallocngAuxvRoAt auxvPtr`. -/
theorem fineRoInit_ro
    (mpl : Obj.MultiPlacement) (tp brkStart auxvPtr : BitVec 64) (R : SepProp) (m : Memory)
    (hTpGe : 0xa4 ≤ tp.toNat) (hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart)
    (hSat : m ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime (mallocngAddrsOfPlacement mpl) tp ∗
      (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
      MallocngAuxvRoAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      m ⊨ |==> (mallocngFineRoIface.HeapM γ (mallocngAddrsOfPlacement mpl) tp brkStart brkStart
        mallocngFineCostModel.init [] ∗ R) := by
  obtain ⟨γ, hγ⟩ := mallocngRoInit_ro mpl tp brkStart auxvPtr R m hTpGe hTpLe hBrkWf hSat
  exact ⟨γ, Satisfies.of_entails hγ (bupd_mono (sepConj_mono_left
    (coarseZeroRo_to_fineHeapRo γ (mallocngAddrsOfPlacement mpl) tp brkStart brkStart)))⟩

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine

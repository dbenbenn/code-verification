/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Model
public import VerifiedLibraries.Mallocng.Proofs.Cost.UsageForest
public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers

/-!
# Fine Heap Invariant & `MallocngCostModelIface` Witness (`…Proofs.Cost.Fine.Inv`)

- **Layer & Role**: `Role::Proof` (untrusted). Connects `FineBudget` (`Model.lean`) to the concrete
  allocator machine state `st : MallocngSt` (`Common.lean`) with **zero ghost lists**: every
  accounting field of `MallocngFineInv` is a direct finite sum over `st.groups`.
- **Key Exports**:
  - `GroupFineGeom`, `MallocngFineInv`, `MallocngFineInv.mono`, `mallocngFineInv_init`;
  - `stLiveUserInClass_le_peakPhys` (`D1.A` `ov > 0` vs `ov = 0` partition with
    `stReallocCrossByNom ≤ reallocPeakByNom` and `stOverAlignInClass ≤ excByClass`);
  - `childMetas_sum_le_of_bounds`, `childMetas_sum_le_childNested` (`F2`, via `UsageForest`),
    and `nonFreeSlots_eq_user_add_children`;
  - `FineCoreImpl`, `FineHeapImpl`, `mallocngFineIface`, `coarseZero_to_fineCore`,
    `coarseZero_to_fineHeap`, `fineCore_to_coarse`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
  VerifiedLibraries.Mallocng.Proofs.Cost

/-! ## 1. Direct Slot & Group Sums Over `st.groups` -/

/-- `1` for `.liveUser _ req _` with `req ≤ 131051` and `nomSc req = k`. -/
def slotLiveNom (k : Nat) : SlotState → Nat
  | .liveUser _ req _ => if req ≤ MmapThresholdReq && nomSc req == k then 1 else 0
  | _                 => 0

/-- `1` for `.liveUser _ req _` with `131051 < req`. -/
def slotLive63Count : SlotState → Nat
  | .liveUser _ req _ => if MmapThresholdReq < req then 1 else 0
  | _                 => 0

/-- `req` for `.liveUser _ req _` with `131051 < req`. -/
def slotLive63Bytes : SlotState → Nat
  | .liveUser _ req _ => if MmapThresholdReq < req then req else 0
  | _                 => 0

/-- `1` for `.liveUser _ req _` with `req ≤ 131051` (used on `g.sc = 63` straddlers). -/
def slotStraddle63 : SlotState → Nat
  | .liveUser _ req _ => if req ≤ MmapThresholdReq then 1 else 0
  | _                 => 0

/-- Over-alignment slack `eff - max req 65536` of a `.liveUser` slot. -/
def slotOverAlign : SlotState → Nat
  | .liveUser _ req eff => eff - max req MallocngMinBlockCost
  | _                   => 0

/-- `1` for `.liveUser _ req eff` with `max req 65536 < eff` (`ov > 0`, created only by
    `aligned_alloc` / `posix_memalign` with `align > 16`). -/
def slotHasOverAlign : SlotState → Nat
  | .liveUser _ req eff => if max req MallocngMinBlockCost < eff then 1 else 0
  | _                   => 0

/-- `1` for an `ov = 0` (`eff ≤ max req 65536`) `.liveUser` slot in physical class `sc` with
    `req ≤ 131051`, `nomSc req = kn`, and `!allowedPhysClass kn sc` (cross-class Stage-2 `realloc`). -/
def slotReallocCross (sc kn : Nat) : SlotState → Nat
  | .liveUser _ req eff =>
    if eff ≤ max req MallocngMinBlockCost && req ≤ MmapThresholdReq &&
        nomSc req == kn && !allowedPhysClass kn sc then 1
    else 0
  | _ => 0

def stLiveUserInClass (st : MallocngSt) (sc : Nat) : Nat :=
  ((st.groups.filter (·.sc == sc)).map fun g => (g.slots.map slotLiveCount).sum).sum

def stLiveByNom (st : MallocngSt) (k : Nat) : Nat :=
  (st.groups.map fun g => (g.slots.map (slotLiveNom k)).sum).sum

def stOverAlignInClass (st : MallocngSt) (sc : Nat) : Nat :=
  ((st.groups.filter (·.sc == sc)).map fun g => (g.slots.map slotHasOverAlign).sum).sum

def stReallocCrossByNom (st : MallocngSt) (kn : Nat) : Nat :=
  ((st.groups.filter (·.sc < 48)).map fun g =>
    (g.slots.map (slotReallocCross g.sc kn)).sum).sum

def stLive63Count (st : MallocngSt) : Nat :=
  (st.groups.map fun g => (g.slots.map slotLive63Count).sum).sum

def stLive63Bytes (st : MallocngSt) : Nat :=
  (st.groups.map fun g => (g.slots.map slotLive63Bytes).sum).sum

def stStraddle63 (st : MallocngSt) : Nat :=
  ((st.groups.filter (·.sc == 63)).map fun g => (g.slots.map slotStraddle63).sum).sum

def stOverAlign (st : MallocngSt) : Nat :=
  (st.groups.map fun g => (g.slots.map slotOverAlign).sum).sum

/-- Steady-nested slab group (`maplen = 0`, `isSteadyNestedClass g.sc`, `g.cnt = steadyCnt g.sc`). -/
def isSteadyNestedGroup (g : GroupDesc) : Bool :=
  decide (g.maplen = 0) && isSteadyNestedClass g.sc && decide (g.cnt = steadyCnt g.sc)

/-- Non-steady (low-usage `u < 128`) nested slab group (`maplen = 0`). -/
def isSmallNestedGroup (g : GroupDesc) : Bool :=
  decide (g.maplen = 0) && !(isSteadyNestedClass g.sc && decide (g.cnt = steadyCnt g.sc))

/-- Mapped root group (`0 < maplen`). -/
def isRootGroup (g : GroupDesc) : Bool :=
  decide (0 < g.maplen)

/-- Realized `(gsn, gst, gr, rb)` counts of `st.groups` in slab class `sc`. -/
def stClassBound (st : MallocngSt) (sc : Nat) : ClassFineBound where
  gsn := (st.groups.filter fun g => (g.sc == sc) && isSmallNestedGroup g).length
  gst := (st.groups.filter fun g => (g.sc == sc) && isSteadyNestedGroup g).length
  gr  := (st.groups.filter fun g => (g.sc == sc) && isRootGroup g).length
  rb  := ((st.groups.filter fun g => (g.sc == sc) && isRootGroup g).map fun g => g.maplen * 4096).sum

/-! ## 2. Per-Group Fine Geometry & `MallocngFineInv` -/

private def checkFineGeomTables : Bool :=
  ((List.range 48).all fun nom =>
    (List.range 48).all fun sc =>
      if allowedPhysClass nom sc then canHoldInPlaceRealloc nom sc else true) &&
  ((List.range 48).all fun sc =>
    (slotStride sc ≤ maxPossibleStride sc) &&
    ((reachableRootPairs sc).all fun p =>
      if p.1 == 1 then p.2 - 16 ≤ maxPossibleStride sc else true))

private theorem checkFineGeomTables_true : checkFineGeomTables = true := by
  decide +kernel

/-- Every `allowedPhysClass nom sc` placement automatically satisfies `canHoldInPlaceRealloc nom sc`. -/
theorem allowedPhysClass_imp_canHold {nom sc : Nat} (h : allowedPhysClass nom sc = true) :
    canHoldInPlaceRealloc nom sc = true := by
  have hAl : sc < 48 ∧ (sc = nom ∨ (coarseBumpable nom = true ∧ sc = nom + 1)) := by
    unfold allowedPhysClass at h
    exact decide_eq_true_eq.mp h
  have hNom48 : nom < 48 := by rcases hAl.2 with rfl | ⟨_, hEq⟩ <;> omega
  have hTab := checkFineGeomTables_true
  unfold checkFineGeomTables at hTab
  rw [Bool.and_eq_true] at hTab
  have h1 := List.all_eq_true.mp hTab.1 nom (List.mem_range.mpr hNom48)
  have h2 := List.all_eq_true.mp h1 sc (List.mem_range.mpr hAl.1)
  simpa only [h, ↓reduceIte] using h2

/-- Any slab group whose root `(cnt, bytes)` pair belongs to `reachableRootPairs g.sc` has
    `g.stride ≤ maxPossibleStride g.sc`. -/
theorem groupStride_le_maxPossibleStride {g : GroupDesc} (hsc : g.sc < 48)
    (hRoot : 0 < g.maplen → (g.cnt, g.maplen * 4096) ∈ reachableRootPairs g.sc) :
    g.stride ≤ maxPossibleStride g.sc := by
  have hAll := checkFineGeomTables_true
  unfold checkFineGeomTables at hAll
  rw [Bool.and_eq_true] at hAll
  have hTab := List.all_eq_true.mp hAll.2 g.sc (List.mem_range.mpr hsc)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hTab
  unfold GroupDesc.stride
  split
  · rename_i hCond
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hCond
    have hCnt1 : g.cnt = 1 := by simp [GroupDesc.cnt, hCond.1]
    have hMem := hRoot hCond.2
    rw [hCnt1] at hMem
    have hp := List.all_eq_true.mp hTab.2 (1, g.maplen * 4096) hMem
    simpa using hp
  · exact hTab.1

/-- Fine geometry of a group `g ∈ st.groups`:
    - for `g.sc < 48`:
      1. every `.liveUser _ req eff` slot in `g` has `req ≤ 131051`, and when `ov = 0`
         (`eff ≤ max req 65536`) satisfies `canHoldInPlaceRealloc (nomSc req) g.sc = true`;
      2. if `g.maplen = 0` (nested), `(g.sc, g.cnt)` is either steady-nested or `isSmallNestedCnt`,
         and its parent `pg ∈ st.groups` has exact class `sizeToClassUnits (g.cnt * sizeClass g.sc)`;
      3. if `0 < g.maplen` (root), `(g.cnt, g.maplen * 4096) ∈ reachableRootPairs g.sc`. -/
def GroupFineGeom (st : MallocngSt) (g : GroupDesc) : Prop :=
  g.sc < 48 →
    (∀ s ∈ g.slots, ∀ p req eff, s = .liveUser p req eff →
      req ≤ MmapThresholdReq ∧
      (eff ≤ max req MallocngMinBlockCost → canHoldInPlaceRealloc (nomSc req) g.sc = true)) ∧
    (g.maplen = 0 →
      ((isSteadyNestedClass g.sc = true ∧ g.cnt = steadyCnt g.sc) ∨
        (g.cnt ≤ 32 ∧ isSmallNestedCnt g.sc g.cnt = true)) ∧
      ∃ pg ∈ st.groups,
        g.parentMeta = some pg.metaPtr ∧
        pg.sc = sizeToClassUnits (g.cnt * sizeClass g.sc)) ∧
    (0 < g.maplen → (g.cnt, g.maplen * 4096) ∈ reachableRootPairs g.sc)

/-- Fine per-size-class machine invariant linking `bgt : FineBudget` to `st : MallocngSt`. -/
structure MallocngFineInv (bgt : FineBudget) (ivs : List (BitVec 64 × Nat))
    (st : MallocngSt) : Prop where
  budget_inv      : FineBudgetInv bgt
  ivs_eq          : ivs = dynamicRootRegions st
  meta_le         : st.metaAreas.length ≤ fineMaxMetaAreas bgt
  groups_geom     : ∀ g ∈ st.groups, GroupFineGeom st g
  class_bounds    : ∀ sc < 48, (stClassBound st sc).le (fineClassEntry (peakPhysOfBudget bgt) sc)
  liveNom_le      : ∀ k < 48, stLiveByNom st k ≤ bgt.liveByNom.getD k 0
  reallocCross_le : ∀ k < 48, stReallocCrossByNom st k ≤ bgt.reallocPeakByNom.getD k 0
  exc_le          : ∀ sc < 48, stOverAlignInClass st sc ≤ bgt.excByClass.getD sc 0
  live63Count_le  : stLive63Count st ≤ bgt.live63Count
  live63Bytes_le  : stLive63Bytes st ≤ bgt.live63Bytes
  straddle63_le   : stStraddle63 st ≤ bgt.straddle63Cum
  overAlign_le    : stOverAlign st ≤ bgt.overAlignCum

/-- Budget-monotonicity of `MallocngFineInv` when `st` is unchanged and all relevant counters of
    `b1` are dominated by `b2`. -/
theorem MallocngFineInv.mono {b1 b2 : FineBudget} {ivs : List (BitVec 64 × Nat)} {st : MallocngSt}
    (h : MallocngFineInv b1 ivs st)
    (hInv2 : FineBudgetInv b2)
    (hPeaks : FinePeaksLe b1 b2)
    (hLiveNom : ∀ k < 48, b1.liveByNom.getD k 0 ≤ b2.liveByNom.getD k 0)
    (hL63C : b1.live63Count ≤ b2.live63Count)
    (hL63B : b1.live63Bytes ≤ b2.live63Bytes) :
    MallocngFineInv b2 ivs st where
  budget_inv         := hInv2
  ivs_eq             := h.ivs_eq
  meta_le            := Nat.le_trans h.meta_le (fineMaxMetaAreas_mono hPeaks)
  groups_geom        := h.groups_geom
  class_bounds sc hs := ClassFineBound.le_trans (h.class_bounds sc hs)
    (fineClassEntry_mono (fun _ hlt => peakPhysOfBudget_mono hPeaks hlt) hs)
  liveNom_le k hk    := Nat.le_trans (h.liveNom_le k hk) (hLiveNom k hk)
  reallocCross_le k hk := Nat.le_trans (h.reallocCross_le k hk) (hPeaks.realloc_le k hk)
  exc_le sc hs       := Nat.le_trans (h.exc_le sc hs) (hPeaks.exc_le sc hs)
  live63Count_le     := Nat.le_trans h.live63Count_le hL63C
  live63Bytes_le     := Nat.le_trans h.live63Bytes_le hL63B
  straddle63_le      := Nat.le_trans h.straddle63_le hPeaks.straddle_le
  overAlign_le       := Nat.le_trans h.overAlign_le hPeaks.overAlign_le

/-! ## 3. User-Slot (`D1.A`) & Nested-Slot (`F2`) Occupancy Bounds -/

private theorem sum_map_le_inv {α : Type} {f g : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem sum_map_add_inv {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem filter_sum_le_sum {α : Type} (p : α → Bool) (f : α → Nat) (xs : List α) :
    ((xs.filter p).map f).sum ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons _ _ ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    split
    · simp only [List.map_cons, List.sum_cons]; omega
    · omega

private theorem filter_imp_sum_le {α : Type} {p q : α → Bool} (f : α → Nat) (xs : List α)
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    ((xs.filter p).map f).sum ≤ ((xs.filter q).map f).sum := by
  induction xs with
  | nil => simp
  | cons x tl ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    by_cases hp : p x = true
    · have hq := h x List.mem_cons_self hp
      simp only [List.filter_cons, hp, hq, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      split
      · simp only [List.map_cons, List.sum_cons]; omega
      · exact ih'

/-- Every cross-class `realloc` slot of nominal class `kn` is a live user slot of nominal class `kn`. -/
theorem stReallocCrossByNom_le_stLiveByNom (st : MallocngSt) (kn : Nat) :
    stReallocCrossByNom st kn ≤ stLiveByNom st kn := by
  unfold stReallocCrossByNom stLiveByNom
  refine Nat.le_trans ?_ (filter_sum_le_sum (fun g => decide (g.sc < 48))
    (fun g => (g.slots.map (slotLiveNom kn)).sum) st.groups)
  refine sum_map_le_inv fun g _ => sum_map_le_inv fun s _ => ?_
  cases s with
  | freeAvail | freeInactive | claimed | liveNested _ => simp [slotReallocCross, slotLiveNom]
  | liveUser p req eff =>
    unfold slotReallocCross slotLiveNom
    by_cases hCond :
        (decide (eff ≤ max req MallocngMinBlockCost) && decide (req ≤ MmapThresholdReq) &&
          (nomSc req == kn) && !allowedPhysClass kn g.sc) = true
    · have hSub : (decide (req ≤ MmapThresholdReq) && (nomSc req == kn)) = true := by
        simp only [Bool.and_eq_true] at hCond ⊢
        exact ⟨hCond.1.1.2, hCond.1.2⟩
      simp only [hCond, hSub, ↓reduceIte]
      exact Nat.le_refl 1
    · simp only [hCond, Bool.false_eq_true, ↓reduceIte]
      exact Nat.zero_le _

private theorem sum_comm_range48 {α : Type} (xs : List α) (f : α → Nat → Nat) :
    (xs.map fun x => ((List.range 48).map (f x)).sum).sum =
      ((List.range 48).map fun k => (xs.map fun x => f x k).sum).sum := by
  induction xs with
  | nil =>
    have h0 : ((List.range 48).map fun (_ : Nat) => (0 : Nat)).sum = 0 := by decide
    simpa using h0.symm
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons, ih, ← sum_map_add_inv]

private theorem le_sum_of_mem_inv {α : Type} {k : α} {ks : List α} (hk : k ∈ ks) (f : α → Nat) :
    f k ≤ (ks.map f).sum := by
  induction ks with
  | nil => cases hk
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hk with rfl | hmem
    · omega
    · have := ih hmem; omega

private def rTermAux (sc : Nat) (s : SlotState) : Nat :=
  ((List.range 48).map fun kn =>
    if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
      slotReallocCross sc kn s
    else 0).sum

private def bTermAux (sc : Nat) (s : SlotState) : Nat :=
  if 0 < sc && coarseBumpable (sc - 1) then slotLiveNom (sc - 1) s else 0

/-- `D1.A` slot decomposition in slab class `sc < 48`: every `.liveUser` slot is accounted for in
    `stLiveByNom st sc`, `stLiveByNom st (sc - 1)` (if `coarseBumpable (sc - 1)`),
    `stReallocCrossByNom st kn` (`canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc`), or
    `stOverAlignInClass st sc` (`ov > 0`). -/
theorem stLiveUserInClass_le_parts {st : MallocngSt} {sc : Nat} (hsc : sc < 48)
    (hGeom : ∀ g ∈ st.groups, GroupFineGeom st g) :
    stLiveUserInClass st sc ≤
      stLiveByNom st sc +
      (if 0 < sc && coarseBumpable (sc - 1) then stLiveByNom st (sc - 1) else 0) +
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
          stReallocCrossByNom st kn
        else 0).sum +
      stOverAlignInClass st sc := by
  have hGroupDecomp :
      ∀ g ∈ st.groups.filter (·.sc == sc),
        (g.slots.map slotLiveCount).sum ≤
          (g.slots.map (slotLiveNom sc)).sum +
          (g.slots.map (bTermAux sc)).sum +
          (g.slots.map (rTermAux sc)).sum +
          (g.slots.map slotHasOverAlign).sum := by
    intro g hgF
    obtain ⟨hgMem, hgScB⟩ := List.mem_filter.mp hgF
    have hgSc : g.sc = sc := by simpa [beq_iff_eq] using hgScB
    have hSlotGeom := (hGeom g hgMem (hgSc ▸ hsc)).1
    have hSlot :
        ∀ s ∈ g.slots,
          slotLiveCount s ≤
            slotLiveNom sc s + bTermAux sc s + rTermAux sc s + slotHasOverAlign s := by
      intro s hs
      cases s with
      | freeAvail | freeInactive | claimed | liveNested _ => simp [slotLiveCount]
      | liveUser p req eff =>
        obtain ⟨hr, hHold0⟩ := hSlotGeom _ hs p req eff rfl
        rw [hgSc] at hHold0
        by_cases hOv : max req MallocngMinBlockCost < eff
        · have hHasOv : slotHasOverAlign (.liveUser p req eff) = 1 := by
            simp [slotHasOverAlign, hOv]
          simp only [slotLiveCount, hHasOv]; omega
        · have hOvLe : eff ≤ max req MallocngMinBlockCost := Nat.not_lt.mp hOv
          have hHold : canHoldInPlaceRealloc (nomSc req) sc = true := hHold0 hOvLe
          by_cases hAl : allowedPhysClass (nomSc req) sc = true
          · have hAl' : sc = nomSc req ∨ (coarseBumpable (nomSc req) = true ∧ sc = nomSc req + 1) := by
              unfold allowedPhysClass at hAl
              exact (decide_eq_true_eq.mp hAl).2
            rcases hAl' with hEq | ⟨hCb, hEq1⟩
            · have hn1 : slotLiveNom sc (.liveUser p req eff) = 1 := by
                simp [slotLiveNom, hr, ← hEq]
              simp only [slotLiveCount, hn1]; omega
            · have hPos : 0 < sc := by omega
              have hSub : sc - 1 = nomSc req := by omega
              have hb1 : bTermAux sc (.liveUser p req eff) = 1 := by
                simp [bTermAux, slotLiveNom, hr, hPos, hSub, hCb]
              simp only [slotLiveCount, hb1]; omega
          · have hNot : (!allowedPhysClass (nomSc req) sc) = true := by
              cases hB : allowedPhysClass (nomSc req) sc
              · rfl
              · exact absurd hB hAl
            have hKnMem : nomSc req ∈ List.range 48 := List.mem_range.mpr (nomSc_lt_48 hr)
            have hr1 : 1 ≤ rTermAux sc (.liveUser p req eff) := by
              unfold rTermAux
              have hAt := le_sum_of_mem_inv hKnMem (fun kn =>
                if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
                  slotReallocCross sc kn (.liveUser p req eff)
                else 0)
              have hOne : (if canHoldInPlaceRealloc (nomSc req) sc && !allowedPhysClass (nomSc req) sc then
                  slotReallocCross sc (nomSc req) (.liveUser p req eff) else 0) = 1 := by
                simp [hHold, hNot, slotReallocCross, hOvLe, hr]
              rwa [hOne] at hAt
            simp only [slotLiveCount]; omega
    calc
      (g.slots.map slotLiveCount).sum
        ≤ (g.slots.map fun s =>
            slotLiveNom sc s + bTermAux sc s + rTermAux sc s + slotHasOverAlign s).sum :=
          sum_map_le_inv hSlot
      _ = (g.slots.map (slotLiveNom sc)).sum +
          (g.slots.map (bTermAux sc)).sum +
          (g.slots.map (rTermAux sc)).sum +
          (g.slots.map slotHasOverAlign).sum := by
        rw [sum_map_add_inv, sum_map_add_inv, sum_map_add_inv]
  unfold stLiveUserInClass stOverAlignInClass
  let gs := st.groups.filter (·.sc == sc)
  have h1 := sum_map_le_inv hGroupDecomp
  rw [sum_map_add_inv, sum_map_add_inv, sum_map_add_inv] at h1
  have hNom1 : (gs.map fun g => (g.slots.map (slotLiveNom sc)).sum).sum ≤ stLiveByNom st sc :=
    filter_sum_le_sum _ _ _
  have hNom2 :
      (gs.map fun g => (g.slots.map (bTermAux sc)).sum).sum ≤
        (if 0 < sc && coarseBumpable (sc - 1) then stLiveByNom st (sc - 1) else 0) := by
    by_cases hCond : (0 < sc && coarseBumpable (sc - 1)) = true
    · have hEq : ∀ g : GroupDesc, (g.slots.map (bTermAux sc)).sum = (g.slots.map (slotLiveNom (sc - 1))).sum :=
        fun g => by unfold bTermAux; simp [hCond]
      simp only [hCond, ↓reduceIte, hEq]
      exact filter_sum_le_sum _ _ _
    · have hEq : ∀ g : GroupDesc, (g.slots.map (bTermAux sc)).sum = 0 := fun g => by
        unfold bTermAux; simp only [hCond, Bool.false_eq_true, ↓reduceIte]
        induction g.slots <;> simp_all
      have h0 : (gs.map fun (_ : GroupDesc) => (0 : Nat)).sum = 0 := by induction gs <;> simp_all
      simp only [hCond, Bool.false_eq_true, ↓reduceIte, hEq, h0]
      exact Nat.le_refl 0
  have hCross :
      (gs.map fun g => (g.slots.map (rTermAux sc)).sum).sum ≤
        ((List.range 48).map fun kn =>
          if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
            stReallocCrossByNom st kn
          else 0).sum := by
    have hGSwap : ∀ g : GroupDesc, (g.slots.map (rTermAux sc)).sum =
        ((List.range 48).map fun kn =>
          if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
            (g.slots.map (slotReallocCross sc kn)).sum
          else 0).sum := by
      intro g
      unfold rTermAux
      rw [sum_comm_range48]
      congr 1
      refine List.map_congr_left fun kn _ => ?_
      split
      · rfl
      · induction g.slots <;> simp_all
    simp only [hGSwap]
    rw [sum_comm_range48]
    refine sum_map_le_inv fun kn _ => ?_
    by_cases hC : (canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc) = true
    · simp only [hC, ↓reduceIte]
      have hGSc :
          (gs.map fun g => (g.slots.map (slotReallocCross sc kn)).sum) =
          (gs.map fun g => (g.slots.map (slotReallocCross g.sc kn)).sum) := by
        refine List.map_congr_left fun g hg => ?_
        have hgSc : g.sc = sc := by simpa [gs, beq_iff_eq] using (List.mem_filter.mp hg).2
        rw [hgSc]
      rw [hGSc]
      exact filter_imp_sum_le (p := fun x => x.sc == sc) (q := fun x => decide (x.sc < 48))
        (fun g => (g.slots.map (slotReallocCross g.sc kn)).sum) st.groups
        (fun g _ hgSc => by
          have hgSc' : g.sc = sc := by simpa [beq_iff_eq] using hgSc
          exact decide_eq_true (hgSc' ▸ hsc))
    · simp only [hC, Bool.false_eq_true, ↓reduceIte]
      have : (gs.map fun _ => (0 : Nat)).sum = 0 := by induction gs <;> simp_all
      omega
  exact Nat.le_trans h1 (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hNom1 hNom2) hCross) (Nat.le_refl _))

theorem stLiveUserInClass_le_peakPhys {bgt : FineBudget} {ivs : List (BitVec 64 × Nat)}
    {st : MallocngSt} (hFine : MallocngFineInv bgt ivs st) {sc : Nat} (hsc : sc < 48) :
    stLiveUserInClass st sc ≤ peakPhysOfBudget bgt sc := by
  have hParts := stLiveUserInClass_le_parts hsc hFine.groups_geom
  unfold peakPhysOfBudget
  have hLivePeak := hFine.budget_inv.live_le_peak
  have h1 : stLiveByNom st sc ≤ bgt.peakByNom.getD sc 0 :=
    Nat.le_trans (hFine.liveNom_le sc hsc) (hLivePeak sc hsc)
  have h2 :
      (if 0 < sc && coarseBumpable (sc - 1) then stLiveByNom st (sc - 1) else 0) ≤
      (if 0 < sc && coarseBumpable (sc - 1) then bgt.peakByNom.getD (sc - 1) 0 else 0) := by
    split
    · exact Nat.le_trans (hFine.liveNom_le (sc - 1) (by omega)) (hLivePeak (sc - 1) (by omega))
    · exact Nat.le_refl 0
  have h3 :
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
          stReallocCrossByNom st kn
        else 0).sum ≤
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
          bgt.reallocPeakByNom.getD kn 0
        else 0).sum := by
    refine sum_map_le_inv fun kn hkn => ?_
    split
    · exact hFine.reallocCross_le kn (List.mem_range.mp hkn)
    · exact Nat.le_refl 0
  have h4 := hFine.exc_le sc hsc
  omega

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] {xs : List α}
    (hnd : xs.Nodup) : ∀ {ys : List α}, (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length := by
  induction xs with
  | nil => intro _ _; exact Nat.zero_le _
  | cons x tl ih =>
    intro ys hsub
    obtain ⟨hxNotMem, hndTl⟩ := List.nodup_cons.mp hnd
    have hxMem : x ∈ ys := hsub x List.mem_cons_self
    have hSubErase : ∀ z ∈ tl, z ∈ ys.erase x := by
      intro z hz
      have hne : z ≠ x := fun hEq => hxNotMem (hEq ▸ hz)
      exact (List.mem_erase_of_ne hne).mpr (hsub z (List.mem_cons_of_mem x hz))
    have hLenTl := ih hndTl hSubErase
    have hEraseLen := List.length_erase_of_mem hxMem
    have hPos : 1 ≤ ys.length := List.length_pos_of_mem hxMem
    simp only [List.length_cons]
    omega

private theorem length_le_one_of_nodup_eq {α : Type} {xs : List α} (hnd : xs.Nodup)
    (heq : ∀ a ∈ xs, ∀ b ∈ xs, a = b) : xs.length ≤ 1 := by
  rcases xs with _ | ⟨a, _ | ⟨b, tl⟩⟩
  · simp
  · simp
  · have hab : a = b := heq a List.mem_cons_self b (List.mem_cons_of_mem a List.mem_cons_self)
    subst hab
    exact absurd List.mem_cons_self (List.nodup_cons.mp hnd).1

private theorem length_disjoint_filters_le {α β : Type} (P : β → α → Bool) (Q : α → Bool)
    (xs : List α) {ys : List β} (hnd : ys.Nodup)
    (hdisj : ∀ x ∈ xs, ∀ y₁ ∈ ys, ∀ y₂ ∈ ys, P y₁ x = true → P y₂ x = true → y₁ = y₂)
    (hsub : ∀ x ∈ xs, ∀ y ∈ ys, P y x = true → Q x = true) :
    (ys.map fun y => (xs.filter (P y)).length).sum ≤ (xs.filter Q).length := by
  induction xs with
  | nil =>
    clear hdisj hsub hnd
    induction ys with
    | nil => simp
    | cons _ _ ihy => simpa using ihy
  | cons x rest ih =>
    have ih' := ih
      (fun z hz => hdisj z (List.mem_cons_of_mem x hz))
      (fun z hz => hsub z (List.mem_cons_of_mem x hz))
    have hSplit :
        (ys.map fun y => ((x :: rest).filter (P y)).length) =
        (ys.map fun y => (if P y x then 1 else 0) + (rest.filter (P y)).length) := by
      refine List.map_congr_left fun y _ => ?_
      by_cases h : P y x = true <;> simp [h]; try omega
    rw [hSplit, sum_map_add_inv]
    have hHead : (ys.map fun y => if P y x then 1 else 0).sum =
        (ys.filter fun y => P y x).length := by
      clear hSplit ih ih' hdisj hsub hnd
      induction ys with
      | nil => simp
      | cons y tl ihy => by_cases h : P y x = true <;> simp [h, ihy]; try omega
    rw [hHead]
    have hLen1 : (ys.filter fun y => P y x).length ≤ 1 :=
      length_le_one_of_nodup_eq (hnd.filter _) (fun a ha b hb => by
        obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
        obtain ⟨hb1, hb2⟩ := List.mem_filter.mp hb
        exact hdisj x List.mem_cons_self a ha1 b hb1 ha2 hb2)
    by_cases hQ : Q x = true
    · simp only [List.filter_cons, hQ, ↓reduceIte, List.length_cons]
      omega
    · have hZero : (ys.filter fun y => P y x).length = 0 := by
        rcases hL : ys.filter (fun y => P y x) with _ | ⟨y, _⟩
        · rfl
        · have hy : y ∈ ys.filter (fun y => P y x) := hL ▸ List.mem_cons_self
          obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
          exact absurd (hsub x List.mem_cons_self y hy1 hy2) hQ
      simp only [List.filter_cons, hQ, Bool.false_eq_true, ↓reduceIte, hZero, Nat.zero_add]
      exact ih'

private theorem range_indicator_sum {n k : Nat} (hk : k < n) :
    ((List.range n).map fun i => if k == i then 1 else 0).sum = 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with hEq | hlt
    · subst k
      have hZero : ((List.range m).map fun i => if m == i then 1 else 0).sum = 0 := by
        have hEq0 : ((List.range m).map fun i => if m == i then 1 else 0) =
            ((List.range m).map fun _ => 0) := by
          refine List.map_congr_left fun i hi => ?_
          have hne : (m == i) = false := beq_false_of_ne (by have := List.mem_range.mp hi; omega)
          simp [hne]
        rw [hEq0]
        clear hk ih hEq0
        induction m with
        | zero => simp
        | succ _ ihm => rw [List.range_succ, List.map_append, List.sum_append, ihm]; simp
      rw [hZero]
      simp
    · rw [ih hlt]
      have hne : k ≠ m := by omega
      simp [hne]

private theorem filter_length_partition_sc (sc : Nat) (Q : GroupDesc → Bool) (gs : List GroupDesc)
    (hLt : ∀ g ∈ gs, Q g = true → g.sc < sc) :
    (gs.filter Q).length =
      ((List.range sc).map fun csc => (gs.filter fun g => (g.sc == csc) && Q g).length).sum := by
  induction gs with
  | nil =>
    have h0 : ∀ n, ((List.range n).map fun (_ : Nat) => (0 : Nat)).sum = 0 := by
      intro n; induction n with
      | zero => simp
      | succ m ihm => rw [List.range_succ, List.map_append, List.sum_append, ihm]; simp
    simpa using (h0 sc).symm
  | cons g tl ih =>
    have ih' := ih fun x hx => hLt x (List.mem_cons_of_mem g hx)
    by_cases hQ : Q g = true
    · have hgLt : g.sc < sc := hLt g List.mem_cons_self hQ
      have hStep :
          ((List.range sc).map fun csc =>
            ((g :: tl).filter fun x => (x.sc == csc) && Q x).length) =
          ((List.range sc).map fun csc =>
            (if g.sc == csc then 1 else 0) +
            (tl.filter fun x => (x.sc == csc) && Q x).length) := by
        refine List.map_congr_left fun csc _ => ?_
        by_cases hc : (g.sc == csc) = true <;> simp [hc, hQ]; try omega
      rw [hStep, sum_map_add_inv, range_indicator_sum hgLt]
      simp only [List.filter_cons, hQ, ↓reduceIte, List.length_cons, ih']
      omega
    · have hStep :
          ((List.range sc).map fun csc =>
            ((g :: tl).filter fun x => (x.sc == csc) && Q x).length) =
          ((List.range sc).map fun csc =>
            (tl.filter fun x => (x.sc == csc) && Q x).length) := by
        refine List.map_congr_left fun csc _ => ?_
        simp [hQ]
      rw [hStep, List.filter_cons]
      simp only [hQ, Bool.false_eq_true, ↓reduceIte, ih']

private theorem filter_or_disjoint_length {α : Type} (p q : α → Bool) (xs : List α)
    (hdisj : ∀ x ∈ xs, ¬ (p x = true ∧ q x = true)) :
    (xs.filter fun x => p x || q x).length = (xs.filter p).length + (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x tl ih =>
    have ih' := ih fun y hy => hdisj y (List.mem_cons_of_mem x hy)
    have hNx := hdisj x List.mem_cons_self
    by_cases hp : p x = true
    · have hq : q x = false := Bool.eq_false_iff.mpr fun hqt => hNx ⟨hp, hqt⟩
      simp [hp, hq, ih']; omega
    · by_cases hq : q x = true <;> simp [hp, hq, ih']; try omega

/-- `F2` nested-child bound parameterized by an arbitrary lower-class bound `B : Nat → ClassFineBound`:
    every `.liveNested` slot in a class-`sc` parent (`sc < 48`) points to a unique child group
    `cg ∈ st.groups` of class `csc < sc` that is either small-nested (`canSmallNestIn csc sc`) or
    steady-nested (`steadyParent csc == sc && isSteadyNestedClass csc`). -/
theorem childMetas_sum_le_of_bounds {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hGeom : ∀ g ∈ st.groups, GroupFineGeom st g)
    {sc : Nat} (hsc : sc < 48)
    {B : Nat → ClassFineBound} (hB : ∀ csc < sc, (stClassBound st csc).le (B csc)) :
    ((st.groups.filter (·.sc == sc)).map fun pg => (childMetas pg).length).sum ≤
      ((List.range sc).map fun csc =>
        (if canSmallNestIn csc sc then (B csc).gsn else 0) +
        (if steadyParent csc == sc && isSteadyNestedClass csc then (B csc).gst else 0)).sum := by
  let P (pm : BitVec 64) (cg : GroupDesc) : Bool :=
    decide (cg.maplen = 0) && (cg.parentMeta == some pm)
  let Q (cg : GroupDesc) : Bool :=
    decide (cg.sc < sc) &&
      ((canSmallNestIn cg.sc sc && isSmallNestedGroup cg) ||
       (steadyParent cg.sc == sc && isSteadyNestedClass cg.sc && isSteadyNestedGroup cg))
  let parents := st.groups.filter (·.sc == sc)
  have hEachPg : ∀ pg ∈ parents, (childMetas pg).length ≤ (st.groups.filter (P pg.metaPtr)).length := by
    intro pg hpgF
    have hpg : pg ∈ st.groups := (List.mem_filter.mp hpgF).1
    have hSub : ∀ cm ∈ childMetas pg, cm ∈ (st.groups.filter (P pg.metaPtr)).map (·.metaPtr) := by
      intro cm hcm
      obtain ⟨cg, hcg, hcgM, hcgPar, _, _⟩ := child_info hwf hpg hcm
      have hMap0 : cg.maplen = 0 := by
        by_cases hPos : 0 < cg.maplen
        · have hNone := (hwf.groups_wf cg hcg).2.2.2.2.2.2.2.2.2.2.1.mp hPos
          rw [hcgPar] at hNone; cases hNone
        · omega
      exact hcgM ▸ List.mem_map_of_mem (List.mem_filter.mpr ⟨hcg, by simp [P, hMap0, hcgPar]⟩)
    calc
      (childMetas pg).length
        ≤ ((st.groups.filter (P pg.metaPtr)).map (·.metaPtr)).length :=
          nodup_length_le_of_subset (childMetas_nodup hwf hpg) hSub
      _ = (st.groups.filter (P pg.metaPtr)).length := List.length_map _
  have hStep1 :
      (parents.map fun pg => (childMetas pg).length).sum ≤
      ((parents.map (·.metaPtr)).map fun pm => (st.groups.filter (P pm)).length).sum := by
    rw [List.map_map]
    exact sum_map_le_inv hEachPg
  have hPmNd : (parents.map (·.metaPtr)).Nodup :=
    (List.filter_sublist.map _).nodup hwf.groups_nodup.1
  have hStep2 :
      ((parents.map (·.metaPtr)).map fun pm => (st.groups.filter (P pm)).length).sum ≤
      (st.groups.filter Q).length := by
    refine length_disjoint_filters_le P Q st.groups hPmNd ?_ ?_
    · intro cg _ pm1 _ pm2 _ hp1 hp2
      simp only [P, Bool.and_eq_true, beq_iff_eq] at hp1 hp2
      exact Option.some.inj (hp1.2.symm.trans hp2.2)
    · intro cg hcg pm hpm hp
      obtain ⟨pg, hpgF, rfl⟩ := List.mem_map.mp hpm
      obtain ⟨hpg, hpgScB⟩ := List.mem_filter.mp hpgF
      have hpgSc : pg.sc = sc := by simpa [beq_iff_eq] using hpgScB
      simp only [P, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
      obtain ⟨_, pg', hpg', _, _, hPar', _, hLt', _⟩ :=
        (hwf.groups_wf cg hcg).2.2.2.2.2.2.2.2.2.2.2.2.1 hp.1
      have hpgEq : pg' = pg :=
        mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg' hpg (Option.some.inj (hPar'.symm.trans hp.2))
      subst pg'
      have hcgLt : cg.sc < sc := hpgSc ▸ hLt'
      obtain ⟨hKind, pg2, hpg2, hPar2, hPscEq⟩ := (hGeom cg hcg (by omega)).2.1 hp.1
      have hpg2Eq : pg2 = pg :=
        mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg2 hpg (Option.some.inj (hPar2.symm.trans hp.2))
      subst pg2
      have hScEq : sc = sizeToClassUnits (cg.cnt * sizeClass cg.sc) := hpgSc.symm.trans hPscEq
      rcases hKind with ⟨hSt, hCntEq⟩ | ⟨hCnt32, hSm⟩
      · have hSp : steadyParent cg.sc = sc := by simp [steadyParent, ← hCntEq, ← hScEq]
        have hGrp : isSteadyNestedGroup cg = true := by
          simp [isSteadyNestedGroup, hp.1, hSt, hCntEq]
        simp [Q, hcgLt, hSp, hSt, hGrp]
      · have hCan : canSmallNestIn cg.sc sc = true :=
          hScEq ▸ (smallNestedCnt_props (by omega) hCnt32 hSm).2.2.2.2.2
        have hNotSt : ¬ (isSteadyNestedClass cg.sc = true ∧ cg.cnt = steadyCnt cg.sc) := by
          unfold isSmallNestedCnt at hSm
          rw [Bool.and_eq_true, decide_eq_true_eq] at hSm
          exact hSm.1.2
        have hGrp : isSmallNestedGroup cg = true := by
          unfold isSmallNestedGroup
          rw [Bool.and_eq_true]
          refine ⟨decide_eq_true hp.1, ?_⟩
          cases hB1 : isSteadyNestedClass cg.sc && decide (cg.cnt = steadyCnt cg.sc)
          · rfl
          · rw [Bool.and_eq_true, decide_eq_true_eq] at hB1
            exact absurd hB1 hNotSt
        simp [Q, hcgLt, hCan, hGrp]
  have hStep3 :
      (st.groups.filter Q).length =
      ((List.range sc).map fun csc => (st.groups.filter fun cg => (cg.sc == csc) && Q cg).length).sum :=
    filter_length_partition_sc sc Q st.groups (fun cg _ hq => by
      simp only [Q, Bool.and_eq_true, decide_eq_true_eq] at hq; exact hq.1)
  have hStep4 :
      ∀ csc ∈ List.range sc,
        (st.groups.filter fun cg => (cg.sc == csc) && Q cg).length ≤
          (if canSmallNestIn csc sc then (B csc).gsn else 0) +
          (if steadyParent csc == sc && isSteadyNestedClass csc then (B csc).gst else 0) := by
    intro csc hcscR
    have hcsc : csc < sc := List.mem_range.mp hcscR
    let pSm (cg : GroupDesc) : Bool := (cg.sc == csc) && canSmallNestIn csc sc && isSmallNestedGroup cg
    let pSt (cg : GroupDesc) : Bool :=
      (cg.sc == csc) && (steadyParent csc == sc && isSteadyNestedClass csc) && isSteadyNestedGroup cg
    have hFilterEq :
        (st.groups.filter fun cg => (cg.sc == csc) && Q cg) =
        (st.groups.filter fun cg => pSm cg || pSt cg) := by
      refine List.filter_congr fun cg _ => ?_
      by_cases hEq : cg.sc = csc
      · simp [Q, pSm, pSt, hEq, hcsc]
      · have hF : (cg.sc == csc) = false := beq_false_of_ne hEq
        simp [pSm, pSt, hF]
    rw [hFilterEq, filter_or_disjoint_length pSm pSt st.groups (fun cg _ ⟨h1, h2⟩ => by
      simp only [pSm, pSt, isSmallNestedGroup, isSteadyNestedGroup, Bool.and_eq_true] at h1 h2
      have hStPart : (isSteadyNestedClass cg.sc && decide (cg.cnt = steadyCnt cg.sc)) = true := by
        rw [Bool.and_eq_true]
        exact ⟨h2.2.1.2, h2.2.2⟩
      rw [hStPart] at h1
      simp at h1)]
    have hBc := hB csc hcsc
    have hSmLe : (st.groups.filter pSm).length ≤ if canSmallNestIn csc sc then (B csc).gsn else 0 := by
      by_cases hCan : canSmallNestIn csc sc = true
      · simp only [hCan, ↓reduceIte]
        have hEqSm : st.groups.filter pSm =
            st.groups.filter (fun cg => (cg.sc == csc) && isSmallNestedGroup cg) :=
          List.filter_congr fun cg _ => by simp [pSm, hCan]
        rw [hEqSm]
        exact hBc.1
      · have hEqNil : (st.groups.filter pSm).length = 0 := by
          have : st.groups.filter pSm = st.groups.filter (fun _ => false) :=
            List.filter_congr fun cg _ => by simp [pSm, hCan]
          rw [this]; simp
        simp [hCan, hEqNil]
    have hStLe : (st.groups.filter pSt).length ≤
        if steadyParent csc == sc && isSteadyNestedClass csc then (B csc).gst else 0 := by
      by_cases hSp : (steadyParent csc == sc && isSteadyNestedClass csc) = true
      · simp only [hSp, ↓reduceIte]
        have hEqSt : st.groups.filter pSt =
            st.groups.filter (fun cg => (cg.sc == csc) && isSteadyNestedGroup cg) :=
          List.filter_congr fun cg _ => by simp [pSt, hSp]
        rw [hEqSt]
        exact hBc.2.1
      · have hEqNil : (st.groups.filter pSt).length = 0 := by
          have : st.groups.filter pSt = st.groups.filter (fun _ => false) :=
            List.filter_congr fun cg _ => by simp [pSt, hSp]
          rw [this]; simp
        simp [hSp, hEqNil]
    omega
  exact Nat.le_trans hStep1 (Nat.le_trans hStep2 (hStep3 ▸ sum_map_le_inv hStep4))

/-- `F2` corollary: total `.liveNested` children in class-`sc` parent groups is bounded by
    `fineChildNested peakPhys sc`. -/
theorem childMetas_sum_le_childNested {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hGeom : ∀ g ∈ st.groups, GroupFineGeom st g)
    {peakPhys : Nat → Nat} {sc : Nat} (hsc : sc < 48)
    (hBounds : ∀ csc < sc, (stClassBound st csc).le (fineClassEntry peakPhys csc)) :
    ((st.groups.filter (·.sc == sc)).map fun pg => (childMetas pg).length).sum ≤
      fineChildNested peakPhys sc :=
  childMetas_sum_le_of_bounds hwf hGeom hsc hBounds

/-- When `totalClaimedSlots st = 0`, `nonFreeSlots st sc` splits into `stLiveUserInClass st sc` plus
    the `.liveNested` child counts `(childMetas pg).length` (`UsageForest.groupNonFree_eq`). -/
theorem nonFreeSlots_eq_user_add_children {st : MallocngSt} (hClaimed0 : totalClaimedSlots st = 0)
    (sc : Nat) :
    nonFreeSlots st sc =
      stLiveUserInClass st sc +
      ((st.groups.filter (·.sc == sc)).map fun pg => (childMetas pg).length).sum := by
  unfold nonFreeSlots stLiveUserInClass
  rw [← sum_map_add_inv]
  congr 1
  refine List.map_congr_left fun g hg => ?_
  rw [groupNonFree_eq]
  have hgMem : g ∈ st.groups := (List.mem_filter.mp hg).1
  have hNoClaim : (g.slots.filter SlotState.isClaimed).length = 0 := by
    unfold totalClaimedSlots at hClaimed0
    have hLe := le_sum_of_mem_inv hgMem (fun x => (x.slots.filter SlotState.isClaimed).length)
    omega
  have hLeafEq : groupLeaf g = (g.slots.map slotLiveCount).sum := by
    unfold groupLeaf
    congr 1
    refine List.map_congr_left fun s hs => ?_
    cases s with
    | claimed =>
      have : SlotState.claimed ∈ g.slots.filter SlotState.isClaimed :=
        List.mem_filter.mpr ⟨hs, rfl⟩
      have := List.length_pos_of_mem this
      omega
    | freeAvail | freeInactive | liveNested _ | liveUser _ _ _ =>
      rfl
  rw [hLeafEq]

/-! ## 4. Separation-Logic Predicates & `mallocngFineIface` -/

/-- Mode-parameterized core heap resource (`ro = false` matches `FineCoreImpl`;
    `ro = true` is `FineCoreRoImpl` with duplicable `.ro` `__libc.auxv` / `auxv`). -/
def FineCoreModeImpl (ro : Bool) (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  MallocngRoTablesA A ∗
  ∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
    ⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
    MallocngCoreStModeA ro γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st

/-- Core heap resource of `mallocngFineIface`, pairing `MallocngCountIvsWF` (for some coarse
    `bCoarse`) with `MallocngFineInv bgt ivs st`. -/
def FineCoreImpl (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  MallocngRoTablesA A ∗
  ∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
    ⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
    MallocngCoreStA γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st

/-- Duplicable-RO-`auxv` core heap resource of `mallocngFineRoIface`. -/
def FineCoreRoImpl (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  FineCoreModeImpl true γ A brkStart brk bgt ivs

/-- Full heap resource of `mallocngFineIface` (`FineCoreImpl ∗ MallocngRuntime`). -/
def FineHeapImpl (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  FineCoreImpl γ A brkStart brk bgt ivs ∗ MallocngRuntime A tp

/-- Mode-parameterized full heap resource (`FineCoreModeImpl ro ∗ MallocngRuntime`). -/
def FineHeapModeImpl (ro : Bool) (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  FineCoreModeImpl ro γ A brkStart brk bgt ivs ∗ MallocngRuntime A tp

/-- Duplicable-RO-`auxv` full heap resource of `mallocngFineRoIface`. -/
def FineHeapRoImpl (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  FineHeapModeImpl true γ A tp brkStart brk bgt ivs

theorem FineCoreModeImpl_false (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    FineCoreModeImpl false γ A brkStart brk bgt ivs =
      FineCoreImpl γ A brkStart brk bgt ivs := rfl

theorem FineHeapModeImpl_false (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    FineHeapModeImpl false γ A tp brkStart brk bgt ivs =
      FineHeapImpl γ A tp brkStart brk bgt ivs := rfl

theorem fineBlock_wf (γ : GhostName) (p : BitVec 64) (n a : Nat) :
    MallocngTightBlock γ p n a ⊢ ⌜MallocngBlockWf p n⌝ ∗ MallocngTightBlock γ p n a := by
  unfold MallocngTightBlock
  refine Entails.sepExists_elim fun k => Entails.pure_left fun hk => ?_
  unfold MallocngBlockTokenK
  refine Entails.pure_left fun hwf => Entails.pure_right hwf ?_
  exact Entails.sepExists_right (Q := fun k => ⌜k ≤ a - 16⌝ ∗ ⌜MallocngBlockWf p n⌝ ∗
    ghostMapElem (liveGhost γ) p (natPair k n)) k
    (Entails.pure_right hk (Entails.pure_right hwf (Entails.refl _)))

theorem fineBlock_noWrap (γ : GhostName) (p : BitVec 64) (n a : Nat) :
    MallocngTightBlock γ p n a ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ MallocngTightBlock γ p n a :=
  Entails.trans (fineBlock_wf γ p n a) (Entails.pure_left fun hwf =>
    Entails.pure_right (Nat.le_trans hwf.2.2.1 (by decide)) (Entails.refl _))

theorem fineBlock_exclusive (γ : GhostName)
    (p₁ : BitVec 64) (n₁ a₁ : Nat) (p₂ : BitVec 64) (n₂ a₂ : Nat) :
    MallocngTightBlock γ p₁ n₁ a₁ ∗ MallocngTightBlock γ p₂ n₂ a₂ ⊢
      ⌜p₁ ≠ p₂⌝ ∗ MallocngTightBlock γ p₁ n₁ a₁ ∗ MallocngTightBlock γ p₂ n₂ a₂ := by
  by_cases hne : p₁ = p₂
  · subst hne
    refine Entails.trans (sepConj_mono (mallocngTightBlock_to_token γ p₁ n₁ a₁)
      (mallocngTightBlock_to_token γ p₁ n₂ a₂)) ?_
    refine Entails.trans (mallocngBlock_exclusive γ p₁ n₁ p₁ n₂) ?_
    exact Entails.pure_left fun h => absurd rfl h
  · exact Entails.pure_right hne (Entails.refl _)

/-- `MallocngCostModelIface` witness for `mallocngFineCostModel`. -/
def mallocngFineIface : MallocngCostModelIface mallocngFineCostModel where
  HeapM := FineHeapImpl
  CoreM := FineCoreImpl
  BlockM γ p n a := MallocngTightBlock γ p n a
  block_noWrap γ p n a := fineBlock_noWrap γ p n a

/-- Duplicable-RO-`auxv` `MallocngCostModelIface` witness for `mallocngFineCostModel`. -/
def mallocngFineRoIface : MallocngCostModelIface mallocngFineCostModel where
  HeapM := FineHeapRoImpl
  CoreM := FineCoreRoImpl
  BlockM γ p n a := MallocngTightBlock γ p n a
  block_noWrap γ p n a := fineBlock_noWrap γ p n a

/-- Mode-indexed fine interface (`false` = RW `mallocngFineIface`, `true` = RO `mallocngFineRoIface`). -/
def mallocngFineModeIface : Bool → MallocngCostModelIface mallocngFineCostModel
  | false => mallocngFineIface
  | true  => mallocngFineRoIface

theorem mallocngFineModeIface_core_eq (ro : Bool)
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    (mallocngFineModeIface ro).CoreM γ A brkStart brk bgt ivs =
      FineCoreModeImpl ro γ A brkStart brk bgt ivs := by
  cases ro <;> rfl

theorem mallocngFineModeIface_heap_eq (ro : Bool)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    (mallocngFineModeIface ro).HeapM γ A tp brkStart brk bgt ivs =
      ((mallocngFineModeIface ro).CoreM γ A brkStart brk bgt ivs ∗ MallocngRuntime A tp) := by
  cases ro <;> rfl

theorem mallocngFineModeIface_block_eq (ro : Bool) :
    (mallocngFineModeIface ro).BlockM = MallocngTightBlock := by
  cases ro <;> rfl

/-- Base case of `MallocngFineInv` on any empty-heap state (`metaAreas = []`, `groups = []`,
    `dynamicRootRegions st = []`). -/
theorem mallocngFineInv_init {st : MallocngSt}
    (hDyn : dynamicRootRegions st = []) (hMa : st.metaAreas = []) (hGs : st.groups = []) :
    MallocngFineInv fineInit [] st where
  budget_inv         := fineBudgetInv_init
  ivs_eq             := hDyn.symm
  meta_le            := by simp [hMa, fineMaxMetaAreas]
  groups_geom        := by intro g hg; rw [hGs] at hg; cases hg
  class_bounds sc _  := by simp [stClassBound, hGs, ClassFineBound.le]
  liveNom_le k _     := by simp [stLiveByNom, hGs]
  reallocCross_le k _ := by simp [stReallocCrossByNom, hGs]
  exc_le sc _        := by simp [stOverAlignInClass, hGs]
  live63Count_le     := by simp [stLive63Count, hGs]
  live63Bytes_le     := by simp [stLive63Bytes, hGs]
  straddle63_le      := by simp [stStraddle63, hGs]
  overAlign_le       := by simp [stOverAlign, hGs]

/-- Non-vacuity witness for `MallocngFineInv` (`inv-audit`). -/
theorem MallocngFineInv_init : ∃ st : MallocngSt, MallocngFineInv fineInit [] st :=
  ⟨{ ctx := emptyCtxFields, auxvPtr := 0#64, metaAreas := [], mmapMetaAreas := [],
     guardPages := [], mmapGuardPages := [], availMetaPages := [], freeMetas := [],
     bumpMetas := [], reservedMetas := [], groups := [], activeLists := [],
     masterDom := [], byteVal := fun _ => 0#8, liveMap := .empty },
   mallocngFineInv_init (by simp [dynamicRootRegions]) rfl rfl⟩

/-- Non-vacuity witness for `FineBudgetInv` (`inv-audit`). -/
theorem FineBudgetInv_init : FineBudgetInv fineInit :=
  fineBudgetInv_init

/-- Every empty-`ivs` coarse state (`MallocngCountIvsWF mallocngZeroBudget [] st` + `MallocngWF`)
    has `st.metaAreas = []` and `st.groups = []`, hence satisfies `MallocngFineInv fineInit [] st`. -/
theorem fineInv_of_coarseZero {base brkStart brk : BitVec 64} {st : MallocngSt}
    (hCount : MallocngCountIvsWF mallocngZeroBudget [] st)
    (hwf : MallocngWF base brkStart brk 0 0 st) :
    MallocngFineInv fineInit [] st := by
  have hDynNil : dynamicRootRegions st = [] := hCount.2.2.1.symm
  have hMaNil : st.metaAreas = [] := by
    unfold dynamicRootRegions at hDynNil
    cases hm : st.metaAreas with
    | nil => rfl
    | cons ma tl => rw [hm] at hDynNil; simp at hDynNil
  have hAllSlotsNil : allMetaSlots st = [] := by simp [allMetaSlots, hMaNil]
  have hGsNil : st.groups = [] := by
    cases hg : st.groups with
    | nil => rfl
    | cons g tl =>
      have hMemUf : g.metaPtr ∈
          st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas := by
        rw [hg]; simp
      have hMemAll := (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp hMemUf
      rw [hAllSlotsNil] at hMemAll; cases hMemAll
  exact mallocngFineInv_init hDynNil hMaNil hGsNil

/-- Upgrade empty-heap `mallocngIface.MallocngCore` (`mallocngZeroBudget`, `[]`) to `FineCoreImpl`. -/
theorem coarseZero_to_fineCore (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64) :
    mallocngIface.MallocngCore γ A brkStart brk mallocngZeroBudget [] ⊢
      FineCoreImpl γ A brkStart brk fineInit [] := by
  show MallocngCoreImpl γ A brkStart brk mallocngZeroBudget [] ⊢ _
  rw [MallocngCoreImpl_eq]
  unfold FineCoreImpl
  refine sepConj_mono_right (Entails.sepExists_mono fun st => ?_)
  refine Entails.pure_left fun hCount => ?_
  unfold MallocngCoreStA MallocngCoreStInflightA
  refine Entails.pure_left fun hwf => ?_
  have hFine := fineInv_of_coarseZero hCount hwf
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun bC =>
        ⌜MallocngCountIvsWF bC [] st ∧ MallocngFineInv fineInit [] st⌝ ∗
        MallocngCoreStA γ A brkStart brk bC.liveCost bC.peakCost st)
      mallocngZeroBudget)
  rw [pure_sepConj_of_true ⟨hCount, hFine⟩]
  unfold MallocngCoreStA MallocngCoreStInflightA
  rw [pure_sepConj_of_true hwf]
  exact Entails.refl _

/-- Upgrade empty-heap `mallocngIface.MallocngHeap` (`mallocngZeroBudget`, `[]`) to `FineHeapImpl`. -/
theorem coarseZero_to_fineHeap (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) :
    mallocngIface.MallocngHeap γ A tp brkStart brk mallocngZeroBudget [] ⊢
      FineHeapImpl γ A tp brkStart brk fineInit [] := by
  show MallocngHeapImpl γ A tp brkStart brk mallocngZeroBudget [] ⊢ _
  rw [MallocngHeapImpl_eq]
  exact sepConj_mono_left (coarseZero_to_fineCore γ A brkStart brk)

/-- Project `FineCoreImpl` back to `mallocngIface.MallocngCore` (preserving `auxv` teardown). -/
theorem fineCore_to_coarse (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    FineCoreImpl γ A brkStart brk bgt ivs ⊢
      ∃∗ bCoarse : MallocngBudget, mallocngIface.MallocngCore γ A brkStart brk bCoarse ivs := by
  unfold FineCoreImpl
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun st => ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_mono fun bCoarse => ?_
  show _ ⊢ MallocngCoreImpl γ A brkStart brk bCoarse ivs
  rw [MallocngCoreImpl_eq]
  refine sepConj_mono_right ?_
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun st' =>
        ⌜MallocngCountIvsWF bCoarse ivs st'⌝ ∗
        MallocngCoreStA γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st')
      st)
  exact sepConj_mono_left (Entails.pure_mono And.left)

/-- Project `FineHeapImpl` back to `mallocngIface.MallocngHeap`. -/
theorem fineHeap_to_coarse (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    FineHeapImpl γ A tp brkStart brk bgt ivs ⊢
      ∃∗ bCoarse : MallocngBudget, mallocngIface.MallocngHeap γ A tp brkStart brk bCoarse ivs := by
  unfold FineHeapImpl
  refine Entails.trans (sepConj_mono_left (fineCore_to_coarse γ A brkStart brk bgt ivs)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun bCoarse => ?_
  show _ ⊢ MallocngHeapImpl γ A tp brkStart brk bCoarse ivs
  rw [MallocngHeapImpl_eq]
  exact Entails.refl _

/-- Upgrade empty-heap `(mallocngModeIface ro).MallocngCore` to `FineCoreModeImpl ro`. -/
theorem coarseZeroMode_to_fineCore (ro : Bool) (γ : GhostName) (A : MallocngAddrs)
    (brkStart brk : BitVec 64) :
    (mallocngModeIface ro).MallocngCore γ A brkStart brk mallocngZeroBudget [] ⊢
      FineCoreModeImpl ro γ A brkStart brk fineInit [] := by
  rw [mallocngModeIface_core_eq]
  unfold FineCoreModeImpl
  refine sepConj_mono_right (Entails.sepExists_mono fun st => ?_)
  refine Entails.pure_left fun hCount => ?_
  unfold MallocngCoreStModeA MallocngCoreStInflightModeA
  refine Entails.pure_left fun hwf => ?_
  have hFine := fineInv_of_coarseZero hCount hwf
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun bC =>
        ⌜MallocngCountIvsWF bC [] st ∧ MallocngFineInv fineInit [] st⌝ ∗
        MallocngCoreStModeA ro γ A brkStart brk bC.liveCost bC.peakCost st)
      mallocngZeroBudget)
  rw [pure_sepConj_of_true ⟨hCount, hFine⟩]
  unfold MallocngCoreStModeA MallocngCoreStInflightModeA
  rw [pure_sepConj_of_true hwf]
  exact Entails.refl _

/-- Upgrade empty-heap `(mallocngModeIface ro).MallocngHeap` to `FineHeapModeImpl ro`. -/
theorem coarseZeroMode_to_fineHeap (ro : Bool) (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) :
    (mallocngModeIface ro).MallocngHeap γ A tp brkStart brk mallocngZeroBudget [] ⊢
      FineHeapModeImpl ro γ A tp brkStart brk fineInit [] := by
  rw [mallocngModeIface_heap_eq]
  exact sepConj_mono_left (coarseZeroMode_to_fineCore ro γ A brkStart brk)

/-- Upgrade empty-heap `mallocngRoIface.MallocngCore` (`mallocngZeroBudget`, `[]`) to
    `FineCoreRoImpl`. -/
theorem coarseZeroRo_to_fineCoreRo (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64) :
    mallocngRoIface.MallocngCore γ A brkStart brk mallocngZeroBudget [] ⊢
      FineCoreRoImpl γ A brkStart brk fineInit [] :=
  coarseZeroMode_to_fineCore true γ A brkStart brk

/-- Upgrade empty-heap `mallocngRoIface.MallocngHeap` (`mallocngZeroBudget`, `[]`) to
    `FineHeapRoImpl`. -/
theorem coarseZeroRo_to_fineHeapRo (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) :
    mallocngRoIface.MallocngHeap γ A tp brkStart brk mallocngZeroBudget [] ⊢
      FineHeapRoImpl γ A tp brkStart brk fineInit [] :=
  coarseZeroMode_to_fineHeap true γ A tp brkStart brk

private theorem fine_mallocngWFInflight_with_auxvPtr {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {p : BitVec 64} :
    MallocngWFInflight inflight base brkStart brk liveCost peakCost { st with auxvPtr := p } =
      MallocngWFInflight inflight base brkStart brk liveCost peakCost st := by
  have hRw : OwnedRwByte { st with auxvPtr := p } = OwnedRwByte st := by funext a; rfl
  have hPn : OwnedProtNoneByte { st with auxvPtr := p } = OwnedProtNoneByte st := by funext a; rfl
  have hMp : OwnedMappedByte { st with auxvPtr := p } = OwnedMappedByte st := by funext a; rfl
  have hDyn : dynamicRootRegions { st with auxvPtr := p } = dynamicRootRegions st := rfl
  apply propext
  constructor <;> intro h <;> exact {
    base_wf := h.base_wf
    brk_bounds := h.brk_bounds
    ctx_lens := h.ctx_lens
    initDone_wf := h.initDone_wf
    initZero_wf := h.initZero_wf
    bounces_wf := h.bounces_wf
    usage_wf := h.usage_wf
    brk_mode_wf := h.brk_mode_wf
    metaAreas_wf := h.metaAreas_wf
    guard_avail_wf := h.guard_avail_wf
    inflight_wf := h.inflight_wf
    free_bump_metas_wf := h.free_bump_metas_wf
    groups_nodup := h.groups_nodup
    groups_wf := h.groups_wf
    regions_disjoint := h.regions_disjoint
    active_wf := h.active_wf
    liveMap_wf := h.liveMap_wf
    live_le_peak := h.live_le_peak
    effCost_le_live := h.effCost_le_live
    meta_pages_bound := h.meta_pages_bound
    empty_groups_bound := h.empty_groups_bound
    masterDom_wf := by simpa only [hRw, hPn, hMp, hDyn] using h.masterDom_wf
  }

private theorem fine_roTablesA_dup (A : MallocngAddrs) :
    (MallocngRoTablesA A ∗ MallocngRoTablesA A) = MallocngRoTablesA A := by
  unfold MallocngRoTablesA MallocngRoTablesAt
  exact sepConj_dup (pointsToBytesRO_dup _ _)
    (sepConj_dup (pointsToBytesRO_dup _ _)
      (sepConj_dup (pointsToBytesRO_dup _ _)
        (sepConj_dup (pointsToBytesRO_dup _ _) (pointsToBytesRO_dup _ _))))

private theorem fine_noRO_mallocngRuntime (A : MallocngAddrs) (tp : BitVec 64) :
    SepProp.NoRO (MallocngRuntime A tp) := by
  unfold MallocngRuntime
  exact SepProp.NoRO.sepConj
    (SepProp.NoRO.sepExists fun _ => SepProp.NoRO.pointsTo32 _ _)
    (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo8 _ _) (SepProp.NoRO.pointsTo64 _ _))

private theorem fine_noRO_mallocngCoreStNoAuxvA (γ : GhostName) (A : MallocngAddrs)
    (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt) :
    SepProp.NoRO (MallocngCoreStNoAuxvA γ A brkStart brk liveCost peakCost st) := by
  unfold MallocngCoreStNoAuxvA
  exact SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
    (SepProp.NoRO.sepConj (noRO_mallocngLiveAuth _ _)
      (SepProp.NoRO.sepConj (SepProp.NoRO.pointsToBytes _ _)
        (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
          (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
            (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
              (SepProp.NoRO.sepConj (ByteMap_noRO _ _ _)
                (SepProp.NoRO.sepConj (ProtNoneByteMap_noRO _ _ _)
                  (MappedSet_noRO _ _))))))))

/-- Factoring equivalence for `FineCoreRoImpl`: separates the duplicable RO tables and RO
    `__libc.auxv`/`auxv` bundle outside the `∃∗ st, ∃∗ bCoarse` quantifiers. -/
theorem fineCoreRo_factor
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    FineCoreRoImpl γ A brkStart brk bgt ivs =
      ((MallocngRoTablesA A ∗ MallocngLibcAuxvRoAt A) ∗
       (∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
         ⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
         MallocngCoreStNoAuxvA γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st)) := by
  unfold FineCoreRoImpl FineCoreModeImpl
  apply SepProp.eq_of_entails
  · rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun st => ?_
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bCoarse => ?_
    unfold MallocngCoreStModeA MallocngCoreStInflightModeA MallocngAuxvPtrCell MallocngAuxvStateRo
      MallocngCoreStNoAuxvA MallocngLibcAuxvRoAt
    simp only [↓reduceIte]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (MallocngRoTablesA A ∗ (((A.libc + 8#64) ↦₆₄ᵣ st.auxvPtr) ∗ MallocngAuxvRoAt st.auxvPtr)) ∗
        (⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
         ⌜MallocngWFInflight 0 A.base brkStart brk bCoarse.liveCost bCoarse.peakCost st⌝ ∗
         MallocngLiveAuth γ st.liveMap ∗
         (A.ctx ↦ₛ st.ctx.toBytes) ∗
         (A.lock ↦₃₂ 0#32) ∗
         (A.replaced ↦₃₂ 0#32) ∗
         (A.aaReplaced ↦₃₂ 0#32) ∗
         ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MappedSet st.masterDom (OwnedMappedByte st)) by ac_rfl))
      ?_
    refine sepConj_mono (sepConj_mono_right (Entails.sepExists_right st.auxvPtr (Entails.refl _))) ?_
    exact Entails.sepExists_right st (Entails.sepExists_right bCoarse (Entails.refl _))
  · unfold MallocngLibcAuxvRoAt
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun st => ?_
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bCoarse => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun auxvPtr => ?_
    let st' : MallocngSt := { st with auxvPtr := auxvPtr }
    have hCountEq : MallocngCountIvsWF bCoarse ivs st' = MallocngCountIvsWF bCoarse ivs st := rfl
    have hFineEq : MallocngFineInv bgt ivs st' = MallocngFineInv bgt ivs st := by
      apply propext
      constructor <;> intro h <;> exact {
        budget_inv := h.budget_inv
        ivs_eq := h.ivs_eq
        meta_le := h.meta_le
        groups_geom := h.groups_geom
        class_bounds := h.class_bounds
        liveNom_le := h.liveNom_le
        reallocCross_le := h.reallocCross_le
        exc_le := h.exc_le
        live63Count_le := h.live63Count_le
        live63Bytes_le := h.live63Bytes_le
        straddle63_le := h.straddle63_le
        overAlign_le := h.overAlign_le
      }
    have hWfEq : MallocngWFInflight 0 A.base brkStart brk bCoarse.liveCost bCoarse.peakCost st' =
        MallocngWFInflight 0 A.base brkStart brk bCoarse.liveCost bCoarse.peakCost st :=
      fine_mallocngWFInflight_with_auxvPtr
    have hBM : ByteMap st.masterDom (OwnedRwByte st') st.byteVal =
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal := rfl
    have hPN : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st') st.byteVal =
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := rfl
    have hMS : MappedSet st.masterDom (OwnedMappedByte st') =
        MappedSet st.masterDom (OwnedMappedByte st) := rfl
    have hStep :
        ((MallocngRoTablesA A ∗ (((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗ MallocngAuxvRoAt auxvPtr)) ∗
         ⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
         MallocngCoreStNoAuxvA γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st) =
        (MallocngRoTablesA A ∗
         (⌜MallocngCountIvsWF bCoarse ivs st' ∧ MallocngFineInv bgt ivs st'⌝ ∗
          MallocngCoreStModeA true γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st')) := by
      unfold MallocngCoreStModeA MallocngCoreStInflightModeA MallocngAuxvPtrCell MallocngAuxvStateRo
        MallocngCoreStNoAuxvA
      simp only [↓reduceIte]
      have hPtr : st'.auxvPtr = auxvPtr := rfl
      have hMap : st'.liveMap = st.liveMap := rfl
      have hCtx : st'.ctx = st.ctx := rfl
      have hDom : st'.masterDom = st.masterDom := rfl
      have hBv : st'.byteVal = st.byteVal := rfl
      rw [hCountEq, hFineEq, hWfEq, hPtr, hMap, hCtx, hDom, hBv, hBM, hPN, hMS]
      ac_rfl
    rw [hStep]
    exact sepConj_mono_right (Entails.sepExists_right st' (Entails.sepExists_right bCoarse (Entails.refl _)))

/-- Duplicable RO / no-RO split for `mallocngFineRoIface.HeapM`. -/
theorem fineHeapRo_roSplit
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    ∃ Ro Rw : SepProp,
      mallocngFineRoIface.HeapM γ A tp brkStart brk bgt ivs = (Ro ∗ Rw) ∧
      (Ro ∗ Ro) = Ro ∧
      ∀ (h : Heap) (a : BitVec 64) (v : BitVec 8), SepProp.Holds Rw h → h a ≠ some (.ro v) := by
  refine ⟨MallocngRoTablesA A ∗ MallocngLibcAuxvRoAt A,
    (∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
      ⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
      MallocngCoreStNoAuxvA γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st) ∗
      MallocngRuntime A tp,
    ?_, sepConj_dup (fine_roTablesA_dup A) (mallocngLibcAuxvRoAt_dup A), ?_⟩
  · show FineCoreRoImpl γ A brkStart brk bgt ivs ∗ MallocngRuntime A tp = _
    rw [fineCoreRo_factor, sepConj_assoc]
  · exact SepProp.NoRO.sepConj
      (SepProp.NoRO.sepExists fun st =>
        SepProp.NoRO.sepExists fun bCoarse =>
          SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
            (fine_noRO_mallocngCoreStNoAuxvA γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st))
      (fine_noRO_mallocngRuntime A tp)

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Footprint
public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.GroupsFreeMono
public import VerifiedLibraries.Mallocng.Proofs.Cost.UsageBound

/-!
# Fine Cost-Model Transition Bridge (`VerifiedLibraries.Mallocng.Proofs.Cost.Fine.FreeBridge`)

- **Role**: `Role::Proof` (untrusted).
- **Purpose**: Pure invariant-preservation lemmas across `GroupsFreeMono`, slot release (`free`),
  `alloc_meta`, `alloc_group` (root & nested), `alloc_slot`, `__libc_malloc_impl` enframe &
  large-`mmap`, `aligned_alloc` reframe, and `realloc` Stage-2 in-place / Stage-3 `mremap`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.Mallocng.Proofs.Cost

/-! ## 1. Split-Budget Invariant `FineSplitInv` & `FineGroupsInv` -/

/-- Split-budget group invariant for intermediate pre-enframe states during an allocation /
    `aligned_alloc` / `realloc` transition:
    - all `.liveUser` slot sums (`stLiveByNom`, `stReallocCrossByNom`, `stOverAlignInClass`,
      `stLive63Count`, `stLive63Bytes`, `stStraddle63`, `stOverAlign`) remain bounded by `bgtLive`;
    - group / meta capacity (`metaAreas.length`, `stClassBound`) is bounded by `bgtPeak`, with
      `peaks_le : FinePeaksLe bgtLive bgtPeak`. -/
structure FineSplitInv (bgtLive bgtPeak : FineBudget) (st : MallocngSt) : Prop where
  live_inv        : FineBudgetInv bgtLive
  peak_inv        : FineBudgetInv bgtPeak
  peaks_le        : FinePeaksLe bgtLive bgtPeak
  meta_le         : st.metaAreas.length ≤ fineMaxMetaAreas bgtPeak
  groups_geom     : ∀ g ∈ st.groups, GroupFineGeom st g
  class_bounds    : ∀ sc < 48, (stClassBound st sc).le (fineClassEntry (peakPhysOfBudget bgtPeak) sc)
  liveNom_le      : ∀ k < 48, stLiveByNom st k ≤ bgtLive.liveByNom.getD k 0
  reallocCross_le : ∀ k < 48, stReallocCrossByNom st k ≤ bgtLive.reallocPeakByNom.getD k 0
  exc_le          : ∀ sc < 48, stOverAlignInClass st sc ≤ bgtLive.excByClass.getD sc 0
  live63Count_le  : stLive63Count st ≤ bgtLive.live63Count
  live63Bytes_le  : stLive63Bytes st ≤ bgtLive.live63Bytes
  straddle63_le   : stStraddle63 st ≤ bgtLive.straddle63Cum
  overAlign_le    : stOverAlign st ≤ bgtLive.overAlignCum

/-- Quiescent single-budget group invariant (`FineSplitInv bgt bgt st`). -/
abbrev FineGroupsInv (bgt : FineBudget) (st : MallocngSt) : Prop :=
  FineSplitInv bgt bgt st

theorem MallocngFineInv.toGroupsInv {bgt : FineBudget} {ivs : List (BitVec 64 × Nat)}
    {st : MallocngSt} (h : MallocngFineInv bgt ivs st) : FineGroupsInv bgt st where
  live_inv        := h.budget_inv
  peak_inv        := h.budget_inv
  peaks_le        := FinePeaksLe.refl bgt
  meta_le         := h.meta_le
  groups_geom     := h.groups_geom
  class_bounds    := h.class_bounds
  liveNom_le      := h.liveNom_le
  reallocCross_le := h.reallocCross_le
  exc_le          := h.exc_le
  live63Count_le  := h.live63Count_le
  live63Bytes_le  := h.live63Bytes_le
  straddle63_le   := h.straddle63_le
  overAlign_le    := h.overAlign_le

theorem FineGroupsInv.toFineInv {bgt : FineBudget} {ivs : List (BitVec 64 × Nat)}
    {st : MallocngSt} (h : FineGroupsInv bgt st) (hIvs : ivs = dynamicRootRegions st) :
    MallocngFineInv bgt ivs st where
  budget_inv      := h.live_inv
  ivs_eq          := hIvs
  meta_le         := h.meta_le
  groups_geom     := h.groups_geom
  class_bounds    := h.class_bounds
  liveNom_le      := h.liveNom_le
  reallocCross_le := h.reallocCross_le
  exc_le          := h.exc_le
  live63Count_le  := h.live63Count_le
  live63Bytes_le  := h.live63Bytes_le
  straddle63_le   := h.straddle63_le
  overAlign_le    := h.overAlign_le

theorem FineGroupsInv.toSplit {bgt0 bgtPeak : FineBudget} {st : MallocngSt}
    (h : FineGroupsInv bgt0 st) (hPeakInv : FineBudgetInv bgtPeak)
    (hPeaks : FinePeaksLe bgt0 bgtPeak) : FineSplitInv bgt0 bgtPeak st where
  live_inv        := h.live_inv
  peak_inv        := hPeakInv
  peaks_le        := hPeaks
  meta_le         := Nat.le_trans h.meta_le (fineMaxMetaAreas_mono hPeaks)
  groups_geom     := h.groups_geom
  class_bounds    := fun sc hsc => ClassFineBound.le_trans (h.class_bounds sc hsc)
    (fineClassEntry_mono (fun _ hj => peakPhysOfBudget_mono hPeaks hj) hsc)
  liveNom_le      := h.liveNom_le
  reallocCross_le := h.reallocCross_le
  exc_le          := h.exc_le
  live63Count_le  := h.live63Count_le
  live63Bytes_le  := h.live63Bytes_le
  straddle63_le   := h.straddle63_le
  overAlign_le    := h.overAlign_le

theorem FineGroupsInv.mono {b1 b2 : FineBudget} {st : MallocngSt}
    (h : FineGroupsInv b1 st)
    (hInv2 : FineBudgetInv b2)
    (hPeaks : FinePeaksLe b1 b2)
    (hLiveNom : ∀ k < 48, b1.liveByNom.getD k 0 ≤ b2.liveByNom.getD k 0)
    (hL63C : b1.live63Count ≤ b2.live63Count)
    (hL63B : b1.live63Bytes ≤ b2.live63Bytes) :
    FineGroupsInv b2 st :=
  (h.toFineInv rfl).mono hInv2 hPeaks hLiveNom hL63C hL63B |>.toGroupsInv

private theorem groupFineGeom_congr_groups {st1 st2 : MallocngSt} {g : GroupDesc}
    (hGs : st2.groups = st1.groups) (h : GroupFineGeom st1 g) : GroupFineGeom st2 g := by
  unfold GroupFineGeom at h ⊢
  rw [hGs]
  exact h

theorem FineSplitInv.of_eq {bL bP : FineBudget} {st st' : MallocngSt}
    (h : FineSplitInv bL bP st)
    (hMa : st'.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hGs : st'.groups = st.groups) : FineSplitInv bL bP st' where
  live_inv        := h.live_inv
  peak_inv        := h.peak_inv
  peaks_le        := h.peaks_le
  meta_le         := hMa
  groups_geom     := fun g hg => groupFineGeom_congr_groups hGs (h.groups_geom g (hGs ▸ hg))
  class_bounds    := fun sc hsc => by unfold stClassBound; rw [hGs]; exact h.class_bounds sc hsc
  liveNom_le      := fun k hk => by unfold stLiveByNom; rw [hGs]; exact h.liveNom_le k hk
  reallocCross_le := fun k hk => by unfold stReallocCrossByNom; rw [hGs]; exact h.reallocCross_le k hk
  exc_le          := fun sc hsc => by unfold stOverAlignInClass; rw [hGs]; exact h.exc_le sc hsc
  live63Count_le  := by unfold stLive63Count; rw [hGs]; exact h.live63Count_le
  live63Bytes_le  := by unfold stLive63Bytes; rw [hGs]; exact h.live63Bytes_le
  straddle63_le   := by unfold stStraddle63; rw [hGs]; exact h.straddle63_le
  overAlign_le    := by unfold stOverAlign; rw [hGs]; exact h.overAlign_le

theorem FineSplitInv.metaAreas_succ_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {bL bP : FineBudget}
    (h : FineSplitInv bL bP st)
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hInflight : inflight ≤ 7) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = []) :
    st.metaAreas.length + 1 ≤ fineMaxMetaAreas bP :=
  fine_metaAreas_length_succ_le hwf hInflight hNoFree hNoBump h.class_bounds
    (Nat.le_trans h.live63Count_le
      (Nat.le_trans h.live_inv.live63Count_le h.peaks_le.peak63Count_le))
    (Nat.le_trans h.straddle63_le h.peaks_le.straddle_le)

theorem FineSplitInv.liveUserInClass_le_peakPhys {bL bP : FineBudget} {st : MallocngSt}
    (h : FineSplitInv bL bP st) {sc : Nat} (hsc : sc < 48) :
    stLiveUserInClass st sc ≤ peakPhysOfBudget bP sc := by
  have hParts := stLiveUserInClass_le_parts hsc h.groups_geom
  have h1 : stLiveByNom st sc ≤ bL.peakByNom.getD sc 0 :=
    Nat.le_trans (h.liveNom_le sc hsc) (h.live_inv.live_le_peak sc hsc)
  have h2 :
      (if 0 < sc && coarseBumpable (sc - 1) then stLiveByNom st (sc - 1) else 0) ≤
        (if 0 < sc && coarseBumpable (sc - 1) then bL.peakByNom.getD (sc - 1) 0 else 0) := by
    split
    · exact Nat.le_trans (h.liveNom_le (sc - 1) (by omega)) (h.live_inv.live_le_peak (sc - 1) (by omega))
    · exact Nat.le_refl 0
  have h3 :
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then stReallocCrossByNom st kn
        else 0).sum ≤
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then bL.reallocPeakByNom.getD kn 0
        else 0).sum := by
    refine accounting_sum_map_le fun kn hkn => ?_
    have hkn48 : kn < 48 := List.mem_range.mp hkn
    split
    · exact h.reallocCross_le kn hkn48
    · exact Nat.le_refl 0
  have h4 := h.exc_le sc hsc
  have hLeL : stLiveUserInClass st sc ≤ peakPhysOfBudget bL sc := by
    unfold peakPhysOfBudget; omega
  exact Nat.le_trans hLeL (peakPhysOfBudget_mono h.peaks_le hsc)

/-! ## 2. Elementary List / Nodup Injection Combinators for `GroupsFreeMono` -/

private theorem slotUserWeight_le_of_sub {w : SlotState → Nat}
    (hNonUser0 : ∀ s, (∀ p req eff, s ≠ .liveUser p req eff) → w s = 0)
    {ss' ss : List SlotState} (hSub : SlotUserSub ss' ss) :
    (ss'.map w).sum ≤ (ss.map w).sum := by
  induction ss' generalizing ss with
  | nil => exact Nat.zero_le _
  | cons x tl' ih =>
    obtain ⟨hLen, hImp⟩ := hSub
    cases ss with
    | nil => simp at hLen
    | cons y tl =>
      simp only [List.length_cons] at hLen
      have hSubTl : SlotUserSub tl' tl :=
        ⟨by omega, fun i hi' hi p req eff hEq =>
          hImp (i + 1) (Nat.succ_lt_succ hi') (Nat.succ_lt_succ hi) p req eff hEq⟩
      have hHead : w x ≤ w y := by
        cases hx : x with
        | liveUser p req eff =>
          have hy := hImp 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) p req eff
            (by simp [hx])
          simp only [List.getElem_cons_zero] at hy
          rw [hy]; exact Nat.le_refl _
        | freeAvail | freeInactive | claimed | liveNested _ =>
          rw [hNonUser0 _ (by intro _ _ _ h; cases h)]
          exact Nat.zero_le _
      have hRec := ih hSubTl
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem nodup_mem_eq_of_metaPtr {gs : List GroupDesc}
    (hNd : (gs.map (·.metaPtr)).Nodup) {g1 g2 : GroupDesc}
    (hg1 : g1 ∈ gs) (hg2 : g2 ∈ gs) (hEq : g1.metaPtr = g2.metaPtr) : g1 = g2 := by
  induction gs with
  | nil => cases hg1
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNd
    rcases List.mem_cons.mp hg1 with rfl | hg1'
    · rcases List.mem_cons.mp hg2 with rfl | hg2'
      · rfl
      · exact False.elim (hNd.1 (hEq ▸ List.mem_map_of_mem hg2'))
    · rcases List.mem_cons.mp hg2 with rfl | hg2'
      · exact False.elim (hNd.1 (hEq.symm ▸ List.mem_map_of_mem hg1'))
      · exact ih hNd.2 hg1' hg2'

private theorem sum_le_of_nodup_inj {gs gs' : List GroupDesc} {w w' : GroupDesc → Nat}
    (hNd : (gs.map (·.metaPtr)).Nodup)
    (hNd' : (gs'.map (·.metaPtr)).Nodup)
    (hMap : ∀ g' ∈ gs', ∃ g ∈ gs, g'.metaPtr = g.metaPtr ∧ w' g' ≤ w g) :
    (gs'.map w').sum ≤ (gs.map w).sum := by
  induction gs' generalizing gs with
  | nil => exact Nat.zero_le _
  | cons g' tl' ih =>
    simp only [List.map_cons, List.nodup_cons] at hNd'
    obtain ⟨g, hg, hMetaEq, hwLe⟩ := hMap g' List.mem_cons_self
    obtain ⟨pre, suf, hSplit⟩ := List.append_of_mem hg
    subst hSplit
    have hNdApp : ((pre ++ suf).map (·.metaPtr)).Nodup := by
      rw [List.map_append] at hNd ⊢
      simp only [List.map_cons] at hNd
      exact (List.Nodup.sublist (by simp) hNd)
    have hTlMap : ∀ h' ∈ tl', ∃ h ∈ pre ++ suf, h'.metaPtr = h.metaPtr ∧ w' h' ≤ w h := by
      intro h' hh'
      obtain ⟨h, hh, hmEq, hwH⟩ := hMap h' (List.mem_cons_of_mem g' hh')
      rw [List.mem_append, List.mem_cons] at hh
      rcases hh with hPre | rfl | hSuf
      · exact ⟨h, List.mem_append_left _ hPre, hmEq, hwH⟩
      · exfalso
        apply hNd'.1
        rw [hMetaEq, ← hmEq]
        exact List.mem_map_of_mem hh'
      · exact ⟨h, List.mem_append_right _ hSuf, hmEq, hwH⟩
    have hRec := ih hNdApp hNd'.2 hTlMap
    simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at hRec ⊢
    omega

private theorem filter_sum_le_of_groupsFreeMono {gs gs' : List GroupDesc}
    (p : GroupDesc → Bool) (w : GroupDesc → Nat)
    (hpCongr : ∀ g' g : GroupDesc,
      g'.sc = g.sc → g'.cnt = g.cnt → g'.maplen = g.maplen → p g' = p g)
    (hwLe : ∀ g' g : GroupDesc,
      g'.sc = g.sc → g'.cnt = g.cnt → g'.maplen = g.maplen →
      SlotUserSub g'.slots g.slots → w g' ≤ w g)
    (hNd : (gs.map (·.metaPtr)).Nodup) (hNd' : (gs'.map (·.metaPtr)).Nodup)
    (hMono : GroupsFreeMono gs gs') :
    ((gs'.filter p).map w).sum ≤ ((gs.filter p).map w).sum := by
  have hSubNd : ∀ xs : List GroupDesc, (xs.map (·.metaPtr)).Nodup →
      ((xs.filter p).map (·.metaPtr)).Nodup :=
    fun xs h => List.Nodup.sublist ((List.filter_sublist).map _) h
  refine sum_le_of_nodup_inj (hSubNd gs hNd) (hSubNd gs' hNd') fun g' hg' => ?_
  have ⟨hg'In, hp'⟩ := List.mem_filter.mp hg'
  obtain ⟨g, hgIn, hM, hSc, hCnt, hMl, _, hSl⟩ := hMono g' hg'In
  have hpG : p g = true := (hpCongr g' g hSc hCnt hMl).symm.trans hp'
  exact ⟨g, List.mem_filter.mpr ⟨hgIn, hpG⟩, hM, hwLe g' g hSc hCnt hMl hSl⟩

private theorem filter_len_le_of_groupsFreeMono {gs gs' : List GroupDesc}
    (p : GroupDesc → Bool)
    (hpCongr : ∀ g' g : GroupDesc,
      g'.sc = g.sc → g'.cnt = g.cnt → g'.maplen = g.maplen → p g' = p g)
    (hNd : (gs.map (·.metaPtr)).Nodup) (hNd' : (gs'.map (·.metaPtr)).Nodup)
    (hMono : GroupsFreeMono gs gs') :
    (gs'.filter p).length ≤ (gs.filter p).length := by
  have hLenOne : ∀ xs : List GroupDesc, xs.length = (xs.map fun _ => 1).sum := by
    intro xs; induction xs with | nil => rfl | cons _ tl ih => simp [ih]; omega
  rw [hLenOne, hLenOne]
  exact filter_sum_le_of_groupsFreeMono p (fun _ => 1) hpCongr
    (fun _ _ _ _ _ _ => Nat.le_refl 1) hNd hNd' hMono

theorem stClassBound_le_of_groupsFreeMono {st st' : MallocngSt}
    (hNd : (st.groups.map (·.metaPtr)).Nodup)
    (hNd' : (st'.groups.map (·.metaPtr)).Nodup)
    (hMono : GroupsFreeMono st.groups st'.groups) (sc : Nat) :
    (stClassBound st' sc).le (stClassBound st sc) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact filter_len_le_of_groupsFreeMono
      (fun g => (g.sc == sc) && isSmallNestedGroup g)
      (fun g' g hSc hCnt hMl => by simp [isSmallNestedGroup, hSc, hCnt, hMl])
      hNd hNd' hMono
  · exact filter_len_le_of_groupsFreeMono
      (fun g => (g.sc == sc) && isSteadyNestedGroup g)
      (fun g' g hSc hCnt hMl => by simp [isSteadyNestedGroup, hSc, hCnt, hMl])
      hNd hNd' hMono
  · exact filter_len_le_of_groupsFreeMono
      (fun g => (g.sc == sc) && isRootGroup g)
      (fun g' g hSc _ hMl => by simp [isRootGroup, hSc, hMl])
      hNd hNd' hMono
  · exact filter_sum_le_of_groupsFreeMono
      (fun g => (g.sc == sc) && isRootGroup g) (fun g => g.maplen * 4096)
      (fun g' g hSc _ hMl => by simp [isRootGroup, hSc, hMl])
      (fun _ _ _ _ hMl _ => by rw [hMl]; exact Nat.le_refl _)
      hNd hNd' hMono

theorem stLiveUserInClass_le_of_groupsFreeMono {st st' : MallocngSt}
    (hNd : (st.groups.map (·.metaPtr)).Nodup)
    (hNd' : (st'.groups.map (·.metaPtr)).Nodup)
    (hMono : GroupsFreeMono st.groups st'.groups) (sc : Nat) :
    stLiveUserInClass st' sc ≤ stLiveUserInClass st sc :=
  filter_sum_le_of_groupsFreeMono (·.sc == sc) (fun g => (g.slots.map slotLiveCount).sum)
    (fun _ _ hSc _ _ => by simp [hSc])
    (fun _ _ _ _ _ hSl => slotUserWeight_le_of_sub
      (fun s hs => by cases s with
        | liveUser p r e => exact False.elim (hs p r e rfl)
        | _ => rfl) hSl)
    hNd hNd' hMono

theorem FineSplitInv.of_groupsFreeMono {inflight inflight' : Nat}
    {base brkStart brk brk' : BitVec 64} {lc pc lc' pc' : Nat}
    {bL bP : FineBudget} {st st' : MallocngSt}
    (h : FineSplitInv bL bP st)
    (hwf : MallocngWFInflight inflight base brkStart brk lc pc st)
    (hwf' : MallocngWFInflight inflight' base brkStart brk' lc' pc' st')
    (hMa : st'.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hMono : GroupsFreeMono st.groups st'.groups) :
    FineSplitInv bL bP st' := by
  have hNd := hwf.groups_nodup.1
  have hNd' := hwf'.groups_nodup.1
  have hUnf : ∀ w : SlotState → Nat,
      (∀ s, (∀ p req eff, s ≠ .liveUser p req eff) → w s = 0) →
      (st'.groups.map fun g => (g.slots.map w).sum).sum ≤
        (st.groups.map fun g => (g.slots.map w).sum).sum := by
    intro w hw0
    refine sum_le_of_nodup_inj hNd hNd' fun g' hg' => ?_
    obtain ⟨g, hg, hM, _, _, _, _, hSl⟩ := hMono g' hg'
    exact ⟨g, hg, hM, slotUserWeight_le_of_sub hw0 hSl⟩
  refine
    { live_inv := h.live_inv
      peak_inv := h.peak_inv
      peaks_le := h.peaks_le
      meta_le := hMa
      groups_geom := ?_
      class_bounds := fun sc hsc =>
        ClassFineBound.le_trans (stClassBound_le_of_groupsFreeMono hNd hNd' hMono sc)
          (h.class_bounds sc hsc)
      liveNom_le := fun k hk => Nat.le_trans
        (hUnf (slotLiveNom k) fun s hs => by cases s with
          | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl)
        (h.liveNom_le k hk)
      reallocCross_le := fun k hk => Nat.le_trans
        (filter_sum_le_of_groupsFreeMono (·.sc < 48)
          (fun g => (g.slots.map (slotReallocCross g.sc k)).sum)
          (fun _ _ hSc _ _ => by simp [hSc])
          (fun g' g hSc _ _ hSl => by
            rw [hSc]
            exact slotUserWeight_le_of_sub (fun s hs => by cases s with
              | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) hSl)
          hNd hNd' hMono)
        (h.reallocCross_le k hk)
      exc_le := fun sc hsc => Nat.le_trans
        (filter_sum_le_of_groupsFreeMono (·.sc == sc)
          (fun g => (g.slots.map slotHasOverAlign).sum)
          (fun _ _ hSc _ _ => by simp [hSc])
          (fun _ _ _ _ _ hSl => slotUserWeight_le_of_sub (fun s hs => by cases s with
            | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) hSl)
          hNd hNd' hMono)
        (h.exc_le sc hsc)
      live63Count_le := Nat.le_trans
        (hUnf slotLive63Count fun s hs => by cases s with
          | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl)
        h.live63Count_le
      live63Bytes_le := Nat.le_trans
        (hUnf slotLive63Bytes fun s hs => by cases s with
          | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl)
        h.live63Bytes_le
      straddle63_le := Nat.le_trans
        (filter_sum_le_of_groupsFreeMono (·.sc == 63)
          (fun g => (g.slots.map slotStraddle63).sum)
          (fun _ _ hSc _ _ => by simp [hSc])
          (fun _ _ _ _ _ hSl => slotUserWeight_le_of_sub (fun s hs => by cases s with
            | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) hSl)
          hNd hNd' hMono)
        h.straddle63_le
      overAlign_le := Nat.le_trans
        (hUnf slotOverAlign fun s hs => by cases s with
          | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl)
        h.overAlign_le }
  intro g' hg' hsc'
  obtain ⟨g, hg, hM, hSc, hCnt, hMl, hPar, hSl⟩ := hMono g' hg'
  have hGeomG := h.groups_geom g hg (hSc ▸ hsc')
  refine ⟨?_, ?_, ?_⟩
  · intro s hs p req eff hsEq
    obtain ⟨idx, hIdx', hGet'⟩ := List.getElem_of_mem hs
    have hIdx : idx < g.slots.length := hSl.1 ▸ hIdx'
    have hSlotG : g.slots[idx]'hIdx = .liveUser p req eff :=
      hSl.2 idx hIdx' hIdx p req eff (hGet'.trans hsEq)
    rw [hSc]
    exact hGeomG.1 _ (List.getElem_mem hIdx) p req eff hSlotG
  · intro hMl0'
    have hMl0 : g.maplen = 0 := hMl ▸ hMl0'
    obtain ⟨hKind, pg, hpg, hParG, hPgSc⟩ := hGeomG.2.1 hMl0
    have hGWf' := hwf'.groups_wf g' hg'
    obtain ⟨_, pg', hpg', _, _, hPar', _⟩ :=
      hGWf'.2.2.2.2.2.2.2.2.2.2.2.2.1 hMl0'
    obtain ⟨pg0, hpg0, hPgM, hPg0Sc, _, _, _, _⟩ := hMono pg' hpg'
    have hSomeEq : some pg'.metaPtr = some pg.metaPtr :=
      hPar'.symm.trans (hPar.trans hParG)
    have hMetaEq : pg0.metaPtr = pg.metaPtr :=
      hPgM.symm.trans (Option.some.inj hSomeEq)
    have hPg0Eq : pg0 = pg := nodup_mem_eq_of_metaPtr hNd hpg0 hpg hMetaEq
    refine ⟨by rw [hSc, hCnt]; exact hKind, pg', hpg', hPar', ?_⟩
    rw [hPg0Sc, hPg0Eq, hPgSc, hCnt, hSc]
  · intro hPos'
    rw [hCnt, hMl, hSc]
    exact hGeomG.2.2 (hMl ▸ hPos')

/-! ## 3. Single-Group Replacement & Slot-Update Sum Helpers -/

private theorem slots_set_sum_eq {ss : List SlotState} {idx : Nat} (hIdx : idx < ss.length)
    (sNew : SlotState) (w : SlotState → Nat) :
    ((ss.set idx sNew).map w).sum + w (ss[idx]'hIdx) = (ss.map w).sum + w sNew := by
  induction ss generalizing idx with
  | nil => cases hIdx
  | cons hd tl ih =>
    cases idx with
    | zero =>
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons, List.getElem_cons_zero]
      omega
    | succ j =>
      have hj : j < tl.length := Nat.lt_of_succ_lt_succ hIdx
      have hRec := ih hj
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ] at hRec ⊢
      omega

private theorem map_id_of_mem {α : Type} {xs : List α} {f : α → α}
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.map_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

private theorem map_ite_sum_eq {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (g' : GroupDesc) (hg : g ∈ gs) (w : GroupDesc → Nat) :
    ((gs.map fun h => if h.metaPtr == g.metaPtr then g' else h).map w).sum + w g =
      (gs.map w).sum + w g' := by
  induction gs with
  | nil => cases hg
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNd
    rcases List.mem_cons.mp hg with hHdEq | hgTl
    · subst hHdEq
      have hTlEq : (tl.map fun h => if h.metaPtr == g.metaPtr then g' else h) = tl := by
        refine map_id_of_mem fun h hh => ?_
        have hNe : (h.metaPtr == g.metaPtr) = false :=
          beq_false_of_ne fun hEq => hNd.1 (hEq ▸ List.mem_map_of_mem hh)
        simp only [hNe, Bool.false_eq_true, ↓reduceIte]
      simp only [List.map_cons, beq_self_eq_true, ↓reduceIte, hTlEq, List.sum_cons]
      omega
    · have hNe : (hd.metaPtr == g.metaPtr) = false :=
        beq_false_of_ne fun hEq => hNd.1 (hEq.symm ▸ List.mem_map_of_mem hgTl)
      have hRec := ih hNd.2 hgTl
      simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte, List.sum_cons] at hRec ⊢
      omega

private theorem filter_map_ite_eq {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g g' : GroupDesc} (hg : g ∈ gs) (p : GroupDesc → Bool) (hp : p g' = p g) :
    ((gs.map fun h => if h.metaPtr == g.metaPtr then g' else h).filter p) =
      (gs.filter p).map fun h => if h.metaPtr == g.metaPtr then g' else h := by
  induction gs with
  | nil => cases hg
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNd
    rcases List.mem_cons.mp hg with hHdEq | hgTl
    · subst hHdEq
      have hTlEq : ∀ xs : List GroupDesc, (∀ x ∈ xs, x ∈ tl) →
          (xs.map fun h => if h.metaPtr == g.metaPtr then g' else h) = xs := by
        intro xs hSub
        refine map_id_of_mem fun h hh => ?_
        have hNe : (h.metaPtr == g.metaPtr) = false :=
          beq_false_of_ne fun hEq => hNd.1 (hEq ▸ List.mem_map_of_mem (hSub h hh))
        simp only [hNe, Bool.false_eq_true, ↓reduceIte]
      simp only [List.map_cons, beq_self_eq_true, ↓reduceIte,
        hTlEq tl (fun _ h => h), List.filter_cons, hp]
      split
      · simp only [List.map_cons, beq_self_eq_true, ↓reduceIte,
          hTlEq (tl.filter p) (fun _ h => (List.mem_filter.mp h).1)]
      · exact (hTlEq (tl.filter p) (fun _ h => (List.mem_filter.mp h).1)).symm
    · have hNe : (hd.metaPtr == g.metaPtr) = false :=
        beq_false_of_ne fun hEq => hNd.1 (hEq.symm ▸ List.mem_map_of_mem hgTl)
      simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte, List.filter_cons]
      split
      · simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte, ih hNd.2 hgTl]
      · exact ih hNd.2 hgTl

private theorem stClassBound_eq_of_map_ite {st st' : MallocngSt}
    (hNd : (st.groups.map (·.metaPtr)).Nodup) {g g' : GroupDesc} (hg : g ∈ st.groups)
    (hSc : g'.sc = g.sc) (hCnt : g'.cnt = g.cnt)
    (hGs : st'.groups = st.groups.map fun h => if h.metaPtr == g.metaPtr then g' else h)
    (sc : Nat) (hMl : g.sc = sc → g'.maplen = g.maplen) :
    stClassBound st' sc = stClassBound st sc := by
  have hLenMap : ∀ p : GroupDesc → Bool, p g' = p g →
      (st'.groups.filter p).length = (st.groups.filter p).length := by
    intro p hp
    rw [hGs, filter_map_ite_eq hNd hg p hp, List.length_map]
  have hpPred : ∀ q : GroupDesc → Bool, (g.sc = sc → q g' = q g) →
      ((g'.sc == sc) && q g') = ((g.sc == sc) && q g) := by
    intro q hq
    by_cases hEqSc : g.sc = sc
    · simp [hSc, hEqSc, hq hEqSc]
    · simp [hSc, beq_false_of_ne hEqSc]
  have hRb : ((st'.groups.filter fun x => (x.sc == sc) && isRootGroup x).map fun x => x.maplen * 4096).sum =
      ((st.groups.filter fun x => (x.sc == sc) && isRootGroup x).map fun x => x.maplen * 4096).sum := by
    have hp := hpPred isRootGroup (fun hEqSc => by simp [isRootGroup, hMl hEqSc])
    rw [hGs, filter_map_ite_eq hNd hg _ hp]
    by_cases hMem : g ∈ st.groups.filter fun x => (x.sc == sc) && isRootGroup x
    · have hEqSc : g.sc = sc := by
        have := (List.mem_filter.mp hMem).2
        rw [Bool.and_eq_true, beq_iff_eq] at this; exact this.1
      have hNdF : ((st.groups.filter fun x => (x.sc == sc) && isRootGroup x).map (·.metaPtr)).Nodup :=
        List.Nodup.sublist ((List.filter_sublist).map _) hNd
      have hSum := map_ite_sum_eq hNdF g' hMem (fun x => x.maplen * 4096)
      rw [hMl hEqSc] at hSum
      omega
    · have hId : ((st.groups.filter fun x => (x.sc == sc) && isRootGroup x).map
          fun h => if h.metaPtr == g.metaPtr then g' else h) =
          st.groups.filter fun x => (x.sc == sc) && isRootGroup x := by
        refine map_id_of_mem fun h hh => ?_
        have hNe : (h.metaPtr == g.metaPtr) = false :=
          beq_false_of_ne fun hEq =>
            hMem ((nodup_mem_eq_of_metaPtr hNd (List.mem_filter.mp hh).1 hg hEq) ▸ hh)
        simp only [hNe, Bool.false_eq_true, ↓reduceIte]
      rw [hId]
  unfold stClassBound
  rw [hLenMap _ (hpPred isSmallNestedGroup fun hEqSc => by simp [isSmallNestedGroup, hSc, hCnt, hMl hEqSc]),
      hLenMap _ (hpPred isSteadyNestedGroup fun hEqSc => by simp [isSteadyNestedGroup, hSc, hCnt, hMl hEqSc]),
      hLenMap _ (hpPred isRootGroup fun hEqSc => by simp [isRootGroup, hMl hEqSc]),
      hRb]

private theorem groupSlotSum_map_ite_eq {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g g' : GroupDesc} (hg : g ∈ gs) {idx : Nat} (hIdx : idx < g.slots.length)
    (sNew : SlotState) (hSl : g'.slots = g.slots.set idx sNew) (w : SlotState → Nat) :
    (((gs.map fun h => if h.metaPtr == g.metaPtr then g' else h).map
        fun h => (h.slots.map w).sum).sum) + w (g.slots[idx]'hIdx) =
      (gs.map fun h => (h.slots.map w).sum).sum + w sNew := by
  have h1 := map_ite_sum_eq hNd g' hg (fun h => (h.slots.map w).sum)
  have h2 := slots_set_sum_eq hIdx sNew w
  rw [hSl] at h1
  omega

private theorem filterGroupSlotSum_map_ite_eq {gs : List GroupDesc}
    (hNd : (gs.map (·.metaPtr)).Nodup) {g g' : GroupDesc} (hg : g ∈ gs)
    (p : GroupDesc → Bool) (hp : p g' = p g) {idx : Nat} (hIdx : idx < g.slots.length)
    (sNew : SlotState) (hSl : g'.slots = g.slots.set idx sNew) (w : GroupDesc → SlotState → Nat)
    (hwEq : ∀ s, w g' s = w g s) :
    ((((gs.map fun h => if h.metaPtr == g.metaPtr then g' else h).filter p).map
        fun h => (h.slots.map (w h)).sum).sum) +
      (if p g then w g (g.slots[idx]'hIdx) else 0) =
    (((gs.filter p).map fun h => (h.slots.map (w h)).sum).sum) +
      (if p g then w g sNew else 0) := by
  rw [filter_map_ite_eq hNd hg p hp]
  have hNdF : ((gs.filter p).map (·.metaPtr)).Nodup :=
    List.Nodup.sublist ((List.filter_sublist).map _) hNd
  by_cases hpG : p g = true
  · have hgF : g ∈ gs.filter p := List.mem_filter.mpr ⟨hg, hpG⟩
    have h1 := map_ite_sum_eq hNdF g' hgF (fun h => (h.slots.map (w h)).sum)
    have hMapW : g'.slots.map (w g') = (g.slots.set idx sNew).map (w g) := by
      rw [hSl]; exact List.map_congr_left fun s _ => hwEq s
    have h2 := slots_set_sum_eq hIdx sNew (w g)
    rw [hMapW] at h1
    simp only [hpG, ↓reduceIte]
    omega
  · have hpG' : p g = false := Bool.eq_false_iff.mpr hpG
    have hNo : ((gs.filter p).map fun h => if h.metaPtr == g.metaPtr then g' else h) = gs.filter p := by
      refine map_id_of_mem fun h hh => ?_
      have hNe : (h.metaPtr == g.metaPtr) = false :=
        beq_false_of_ne fun hEq => by
          have := nodup_mem_eq_of_metaPtr hNd (List.mem_filter.mp hh).1 hg hEq
          subst this
          exact hpG (List.mem_filter.mp hh).2
      simp only [hNe, Bool.false_eq_true, ↓reduceIte]
    rw [hNo]
    simp only [hpG', Bool.false_eq_true, ↓reduceIte]

private theorem groupFineGeom_of_map_ite {st st' : MallocngSt}
    (hNd : (st.groups.map (·.metaPtr)).Nodup)
    (hGeom : ∀ x ∈ st.groups, GroupFineGeom st x)
    {g g' : GroupDesc} (hg : g ∈ st.groups)
    (hMeta : g'.metaPtr = g.metaPtr) (hSc : g'.sc = g.sc)
    (hCnt : g'.cnt = g.cnt) (hMl : g.sc < 48 → g'.maplen = g.maplen)
    (hPar : g'.parentMeta = g.parentMeta)
    (hGs : st'.groups = st.groups.map fun h => if h.metaPtr == g.metaPtr then g' else h)
    (hSlotsG' : g'.sc < 48 → ∀ s ∈ g'.slots, ∀ p req eff, s = .liveUser p req eff →
      req ≤ MmapThresholdReq ∧
      (eff ≤ max req MallocngMinBlockCost → canHoldInPlaceRealloc (nomSc req) g'.sc = true)) :
    ∀ x' ∈ st'.groups, GroupFineGeom st' x' := by
  have liftParent : ∀ pg ∈ st.groups, ∃ pg' ∈ st'.groups,
      pg'.metaPtr = pg.metaPtr ∧ pg'.sc = pg.sc := by
    intro pg hpg
    refine ⟨if pg.metaPtr == g.metaPtr then g' else pg, ?_, ?_, ?_⟩
    · rw [hGs]; exact List.mem_map_of_mem hpg
    · by_cases hEq : pg.metaPtr = g.metaPtr
      · simp [hEq, hMeta]
      · simp [beq_false_of_ne hEq]
    · by_cases hEq : pg.metaPtr = g.metaPtr
      · have hPgG := nodup_mem_eq_of_metaPtr hNd hpg hg hEq
        subst hPgG; simp [hSc]
      · simp [beq_false_of_ne hEq]
  intro x' hx'
  rw [hGs] at hx'
  obtain ⟨x, hx, hMapX⟩ := List.mem_map.mp hx'
  by_cases hEqM : x.metaPtr = g.metaPtr
  · have hxG := (nodup_mem_eq_of_metaPtr hNd hx hg hEqM).symm
    subst hxG
    simp only [beq_self_eq_true, ↓reduceIte] at hMapX
    subst hMapX
    intro hsc'
    have hsc : g.sc < 48 := hSc ▸ hsc'
    have hGx := hGeom g hg hsc
    have hMlEq := hMl hsc
    refine ⟨hSlotsG' hsc', fun hMl0 => ?_, fun hMlPos => ?_⟩
    · obtain ⟨hKind, pg, hpg, hPgPar, hPgSc⟩ := hGx.2.1 (hMlEq ▸ hMl0)
      obtain ⟨pg', hpg', hPgM', hPgSc'⟩ := liftParent pg hpg
      refine ⟨by rwa [hSc, hCnt], pg', hpg', ?_, ?_⟩
      · rw [hPar, hPgPar, hPgM']
      · rw [hPgSc', hPgSc, hCnt, hSc]
    · rw [hCnt, hMlEq, hSc]
      exact hGx.2.2 (hMlEq ▸ hMlPos)
  · simp only [beq_false_of_ne hEqM, Bool.false_eq_true, ↓reduceIte] at hMapX
    subst hMapX
    intro hsc
    have hXx := hGeom x hx hsc
    refine ⟨hXx.1, fun hMl0 => ?_, hXx.2.2⟩
    obtain ⟨hKind, pg, hpg, hPgPar, hPgSc⟩ := hXx.2.1 hMl0
    obtain ⟨pg', hpg', hPgM', hPgSc'⟩ := liftParent pg hpg
    exact ⟨hKind, pg', hpg', hPgPar.trans (congrArg some hPgM'.symm), hPgSc'.trans hPgSc⟩

/-! ## 4. Slot Release (`free`: `.liveUser p req eff ↦ .claimed`) -/

theorem fineGroupsInv_release_slot {bgt : FineBudget} {st st1 : MallocngSt}
    (hFine : FineGroupsInv bgt st) (hNd : (st.groups.map (·.metaPtr)).Nodup)
    {g g' : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {req eff : Nat} (hSlot : g.slots[idx]'hIdx = .liveUser p req eff)
    (hMeta : g'.metaPtr = g.metaPtr) (hSc : g'.sc = g.sc)
    (hCnt : g'.cnt = g.cnt) (hMl : g'.maplen = g.maplen)
    (hPar : g'.parentMeta = g.parentMeta)
    (hSl : g'.slots = g.slots.set idx .claimed)
    (hMa : st1.metaAreas = st.metaAreas)
    (hGs : st1.groups = st.groups.map fun h => if h.metaPtr == g.metaPtr then g' else h) :
    FineGroupsInv (fineStepFree req bgt) st1 := by
  have hBInv' : FineBudgetInv (fineStepFree req bgt) := fineBudgetInv_stepFree req hFine.live_inv
  have hPeakPhysEq : peakPhysOfBudget (fineStepFree req bgt) = peakPhysOfBudget bgt := by
    funext sc; unfold fineStepFree; split <;> rfl
  have hMaxMetaEq : fineMaxMetaAreas (fineStepFree req bgt) = fineMaxMetaAreas bgt := by
    unfold fineMaxMetaAreas fineMaxGroups
    rw [hPeakPhysEq]
    unfold fineStepFree; split <;> rfl
  refine
    { live_inv        := hBInv'
      peak_inv        := hBInv'
      peaks_le        := FinePeaksLe.refl (fineStepFree req bgt)
      meta_le         := by rw [hMa, hMaxMetaEq]; exact hFine.meta_le
      groups_geom     := groupFineGeom_of_map_ite hNd hFine.groups_geom hg
        hMeta hSc hCnt (fun _ => hMl) hPar hGs (fun hsc' s hs p' req' eff' hsEq => by
          rw [hSl] at hs
          rcases List.mem_or_eq_of_mem_set hs with hsOld | hClaimEq
          · rw [hSc]; exact (hFine.groups_geom g hg (hSc ▸ hsc')).1 s hsOld p' req' eff' hsEq
          · cases hClaimEq.symm.trans hsEq)
      class_bounds    := fun sc hsc => by
        rw [stClassBound_eq_of_map_ite hNd hg hSc hCnt hGs sc (fun _ => hMl), hPeakPhysEq]
        exact hFine.class_bounds sc hsc
      liveNom_le      := fun k hk => by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx .claimed hSl (slotLiveNom k)
        rw [hSlot] at hSum
        have hSt1 : stLiveByNom st1 k + slotLiveNom k (.liveUser p req eff) = stLiveByNom st k := by
          unfold stLiveByNom; rw [hGs]; simpa [slotLiveNom] using hSum
        have hLe0 := hFine.liveNom_le k hk
        by_cases hReqLe : req ≤ MmapThresholdReq
        · simp only [fineStepFree, hReqLe, ↓reduceIte, vec48Of_getD, hk]
          by_cases hEqK : k = nomSc req
          · subst hEqK
            simp only [slotLiveNom, hReqLe, decide_true, beq_self_eq_true, Bool.true_and, ↓reduceIte] at hSt1 ⊢
            omega
          · have hNe1 : (k == nomSc req) = false := beq_false_of_ne hEqK
            have hNe2 : (nomSc req == k) = false := beq_false_of_ne (Ne.symm hEqK)
            simp only [slotLiveNom, hReqLe, decide_true, hNe1, hNe2, Bool.true_and,
              Bool.false_eq_true, ↓reduceIte] at hSt1 ⊢
            omega
        · simp only [fineStepFree, hReqLe, ↓reduceIte]; omega
      reallocCross_le := fun k hk => by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (fun x => decide (x.sc < 48))
          (by simp [hSc]) hIdx .claimed hSl (fun x => slotReallocCross x.sc k)
          (fun s => by simp [hSc])
        have hLe : stReallocCrossByNom st1 k ≤ stReallocCrossByNom st k := by
          unfold stReallocCrossByNom; rw [hGs]
          have hC0 : (if decide (g.sc < 48) then slotReallocCross g.sc k .claimed else 0) = 0 := by
            split <;> rfl
          rw [hC0] at hSum; omega
        have hRP : (fineStepFree req bgt).reallocPeakByNom = bgt.reallocPeakByNom := by
          unfold fineStepFree; split <;> rfl
        rw [hRP]
        exact Nat.le_trans hLe (hFine.reallocCross_le k hk)
      exc_le          := fun sc hsc => by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == sc)
          (by simp [hSc]) hIdx .claimed hSl (fun _ => slotHasOverAlign) (fun _ => rfl)
        have hLe : stOverAlignInClass st1 sc ≤ stOverAlignInClass st sc := by
          unfold stOverAlignInClass; rw [hGs]
          have hC0 : (if g.sc == sc then slotHasOverAlign .claimed else 0) = 0 := by
            split <;> rfl
          rw [hC0] at hSum; omega
        have hEP : (fineStepFree req bgt).excByClass = bgt.excByClass := by
          unfold fineStepFree; split <;> rfl
        rw [hEP]
        exact Nat.le_trans hLe (hFine.exc_le sc hsc)
      live63Count_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx .claimed hSl slotLive63Count
        rw [hSlot] at hSum
        have hSt1 : stLive63Count st1 + (if MmapThresholdReq < req then 1 else 0) = stLive63Count st := by
          unfold stLive63Count; rw [hGs]; simpa [slotLive63Count] using hSum
        have hLe0 := hFine.live63Count_le
        by_cases hReqLe : req ≤ MmapThresholdReq
        · simp only [fineStepFree, hReqLe, ↓reduceIte]; omega
        · have hGt : MmapThresholdReq < req := by omega
          simp only [fineStepFree, hReqLe, hGt, ↓reduceIte] at hSt1 ⊢; omega
      live63Bytes_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx .claimed hSl slotLive63Bytes
        rw [hSlot] at hSum
        have hSt1 : stLive63Bytes st1 + (if MmapThresholdReq < req then req else 0) = stLive63Bytes st := by
          unfold stLive63Bytes; rw [hGs]; simpa [slotLive63Bytes] using hSum
        have hLe0 := hFine.live63Bytes_le
        by_cases hReqLe : req ≤ MmapThresholdReq
        · simp only [fineStepFree, hReqLe, ↓reduceIte]; omega
        · have hGt : MmapThresholdReq < req := by omega
          simp only [fineStepFree, hReqLe, hGt, ↓reduceIte] at hSt1 ⊢; omega
      straddle63_le   := by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == 63)
          (by simp [hSc]) hIdx .claimed hSl (fun _ => slotStraddle63) (fun _ => rfl)
        have hLe : stStraddle63 st1 ≤ stStraddle63 st := by
          unfold stStraddle63; rw [hGs]
          have hC0 : (if g.sc == 63 then slotStraddle63 .claimed else 0) = 0 := by
            split <;> rfl
          rw [hC0] at hSum; omega
        have hSP : (fineStepFree req bgt).straddle63Cum = bgt.straddle63Cum := by
          unfold fineStepFree; split <;> rfl
        rw [hSP]
        exact Nat.le_trans hLe hFine.straddle63_le
      overAlign_le    := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx .claimed hSl slotOverAlign
        have hLe : stOverAlign st1 ≤ stOverAlign st := by
          unfold stOverAlign; rw [hGs]
          have : slotOverAlign .claimed = 0 := rfl
          omega
        have hOP : (fineStepFree req bgt).overAlignCum = bgt.overAlignCum := by
          unfold fineStepFree; split <;> rfl
        rw [hOP]
        exact Nat.le_trans hLe hFine.overAlign_le }

/-! ## 5. `AllocSlotOccRoom` & `alloc_group` Root / Nested Bridges -/

private def checkAllowedReqBounds : Bool :=
  (List.range 48).all fun nom =>
    (List.range 48).all fun sc =>
      if allowedPhysClass nom sc then
        decide (allocSlotReqLo sc ≤ minReqOfNom nom ∧ nominalSlotCap nom ≤ nominalSlotCap sc)
      else true

private theorem checkAllowedReqBounds_true : checkAllowedReqBounds = true := by decide

theorem allocSlotReqLo_le_of_allowedPhysClass {req sc : Nat}
    (hReq : req ≤ MmapThresholdReq) (hsc : sc < 48)
    (hAllow : allowedPhysClass (nomSc req) sc = true) :
    allocSlotReqLo sc ≤ req ∧ req ≤ nominalSlotCap sc := by
  obtain ⟨hNom48, hReqHi, hReqLo⟩ := nomSc_spec hReq
  have hRow := (List.all_eq_true.mp checkAllowedReqBounds_true) (nomSc req) (List.mem_range.mpr hNom48)
  have hCell := (List.all_eq_true.mp hRow) sc (List.mem_range.mpr hsc)
  simp only [hAllow, ↓reduceIte, decide_eq_true_eq] at hCell
  have hMinLe : minReqOfNom (nomSc req) ≤ req := by
    unfold minReqOfNom
    rcases hReqLo with h0 | hGt
    · simp [h0]
    · split <;> omega
  exact ⟨Nat.le_trans hCell.1 hMinLe, Nat.le_trans hReqHi hCell.2⟩

private theorem sum_map_le_fb {α : Type} {f g : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h hd List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

private theorem sum_map_strict_le {α : Type} [DecidableEq α] {f g : α → Nat} {xs : List α}
    {x0 : α} (hx0 : x0 ∈ xs) (hLe : ∀ x ∈ xs, f x ≤ g x) (hStrict : f x0 + 1 ≤ g x0) :
    (xs.map f).sum + 1 ≤ (xs.map g).sum := by
  induction xs with
  | nil => cases hx0
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx0 with rfl | hxTl
    · have hTl := sum_map_le_fb (xs := tl) (fun x hx => hLe x (List.mem_cons_of_mem _ hx))
      omega
    · have hHd := hLe hd List.mem_cons_self
      have hRec := ih hxTl (fun x hx => hLe x (List.mem_cons_of_mem _ hx))
      omega

theorem fineLiveUser_room_alloc {bgt : FineBudget} {st : MallocngSt}
    (hFine : FineGroupsInv bgt st) {req sc : Nat}
    (hReq : req ≤ MmapThresholdReq) (hsc : sc < 48)
    (hAllow : allowedPhysClass (nomSc req) sc = true) :
    stLiveUserInClass st sc + 1 ≤ peakPhysOfBudget (fineStepAlloc req bgt) sc := by
  have hParts := stLiveUserInClass_le_parts hsc hFine.groups_geom
  have hPeaks := finePeaksLe_stepAlloc req bgt
  have hRSum :
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then stReallocCrossByNom st kn
        else 0).sum ≤
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
          (fineStepAlloc req bgt).reallocPeakByNom.getD kn 0
        else 0).sum := by
    refine sum_map_le_fb fun kn hkn => ?_
    have hkn48 : kn < 48 := List.mem_range.mp hkn
    split
    · exact Nat.le_trans (hFine.reallocCross_le kn hkn48) (hPeaks.realloc_le kn hkn48)
    · exact Nat.le_refl 0
  have hExc : stOverAlignInClass st sc ≤ (fineStepAlloc req bgt).excByClass.getD sc 0 :=
    Nat.le_trans (hFine.exc_le sc hsc) (hPeaks.exc_le sc hsc)
  unfold allowedPhysClass at hAllow
  rw [decide_eq_true_eq] at hAllow
  rcases hAllow.2 with hEqNom | ⟨hBump, hEqBump⟩
  · subst hEqNom
    have hNom1 : stLiveByNom st (nomSc req) + 1 ≤ (fineStepAlloc req bgt).peakByNom.getD (nomSc req) 0 := by
      have hL := hFine.liveNom_le (nomSc req) hsc
      simp only [fineStepAlloc, hReq, ↓reduceIte, vec48Of_getD, hsc, beq_self_eq_true]
      omega
    have hBumpLe :
        (if 0 < nomSc req && coarseBumpable (nomSc req - 1) then stLiveByNom st (nomSc req - 1) else 0) ≤
        (if 0 < nomSc req && coarseBumpable (nomSc req - 1) then
          (fineStepAlloc req bgt).peakByNom.getD (nomSc req - 1) 0 else 0) := by
      split
      · have hsm1 : nomSc req - 1 < 48 := by omega
        exact Nat.le_trans (hFine.liveNom_le (nomSc req - 1) hsm1)
          (Nat.le_trans (hFine.live_inv.live_le_peak (nomSc req - 1) hsm1) (hPeaks.peak_le (nomSc req - 1) hsm1))
      · exact Nat.le_refl 0
    unfold peakPhysOfBudget
    omega
  · have hScPos : 0 < sc := by omega
    have hsm1Eq : sc - 1 = nomSc req := by omega
    have hNomLt : nomSc req < 48 := nomSc_lt_48 hReq
    have hCond : (decide (0 < sc) && coarseBumpable (sc - 1)) = true := by
      simp [hScPos, hsm1Eq, hBump]
    have hNomLe : stLiveByNom st sc ≤ (fineStepAlloc req bgt).peakByNom.getD sc 0 :=
      Nat.le_trans (hFine.liveNom_le sc hsc)
        (Nat.le_trans (hFine.live_inv.live_le_peak sc hsc) (hPeaks.peak_le sc hsc))
    have hBump1 : stLiveByNom st (sc - 1) + 1 ≤ (fineStepAlloc req bgt).peakByNom.getD (sc - 1) 0 := by
      rw [hsm1Eq]
      have hL := hFine.liveNom_le (nomSc req) hNomLt
      simp only [fineStepAlloc, hReq, ↓reduceIte, vec48Of_getD, hNomLt, beq_self_eq_true]
      omega
    unfold peakPhysOfBudget
    simp only [hCond, ↓reduceIte] at hParts ⊢
    omega

theorem fineLiveUser_room_aligned {bgt : FineBudget} {st : MallocngSt}
    (hFine : FineGroupsInv bgt st) {align len sc : Nat}
    (hAlGt : 16 < align) (hEff : mallocngAlignedEffSize align len ≤ MmapThresholdReq)
    (hsc : sc < 48)
    (hAllow : allowedPhysClass (nomSc (mallocngAlignedEffSize align len)) sc = true) :
    stLiveUserInClass st sc + 1 ≤ peakPhysOfBudget (fineStepAligned align len bgt) sc := by
  have hParts := stLiveUserInClass_le_parts hsc hFine.groups_geom
  have hPeaks := finePeaksLe_step (.aligned align len) bgt
  simp only [fineStep] at hPeaks
  have hNomLe : stLiveByNom st sc ≤ (fineStepAligned align len bgt).peakByNom.getD sc 0 :=
    Nat.le_trans (hFine.liveNom_le sc hsc)
      (Nat.le_trans (hFine.live_inv.live_le_peak sc hsc) (hPeaks.peak_le sc hsc))
  have hBumpLe :
      (if 0 < sc && coarseBumpable (sc - 1) then stLiveByNom st (sc - 1) else 0) ≤
      (if 0 < sc && coarseBumpable (sc - 1) then
        (fineStepAligned align len bgt).peakByNom.getD (sc - 1) 0 else 0) := by
    split
    · have hsm1 : sc - 1 < 48 := by omega
      exact Nat.le_trans (hFine.liveNom_le (sc - 1) hsm1)
        (Nat.le_trans (hFine.live_inv.live_le_peak (sc - 1) hsm1) (hPeaks.peak_le (sc - 1) hsm1))
    · exact Nat.le_refl 0
  have hRSum :
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then stReallocCrossByNom st kn
        else 0).sum ≤
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
          (fineStepAligned align len bgt).reallocPeakByNom.getD kn 0
        else 0).sum := by
    refine sum_map_le_fb fun kn hkn => ?_
    have hkn48 : kn < 48 := List.mem_range.mp hkn
    split
    · exact Nat.le_trans (hFine.reallocCross_le kn hkn48) (hPeaks.realloc_le kn hkn48)
    · exact Nat.le_refl 0
  have hNotLe16 : ¬ align ≤ 16 := by omega
  have hExc1 : stOverAlignInClass st sc + 1 ≤ (fineStepAligned align len bgt).excByClass.getD sc 0 := by
    have hE0 := hFine.exc_le sc hsc
    unfold fineStepAligned
    simp only [hNotLe16, hEff, ↓reduceIte, vec48Of_getD, hsc, hAllow]
    have hB1Exc : (fineStepAlloc len bgt).excByClass = bgt.excByClass := by
      unfold fineStepAlloc; split <;> rfl
    rw [hB1Exc]
    omega
  unfold peakPhysOfBudget
  omega

/-- Occupancy room in slab class `sc` guaranteeing `nonFreeSlots st sc + 1 ≤ fineRawOcc (peakPhysOfBudget bP) sc`
    at `alloc_group` entry (`totalClaimedSlots st = 0`): either user slots have room below
    `peakPhysOfBudget bP sc` (outer call), or some child class `csc < sc` has room for one more
    nested group feeding `sc` (recursive nested call). -/
def AllocSlotOccRoom (bP : FineBudget) (st : MallocngSt) (sc : Nat) : Prop :=
  stLiveUserInClass st sc + 1 ≤ peakPhysOfBudget bP sc ∨
  ∃ csc < sc,
    ((canSmallNestIn csc sc = true ∧
      (stClassBound st csc).gsn + 1 ≤ (fineClassEntry (peakPhysOfBudget bP) csc).gsn) ∨
     ((steadyParent csc == sc && isSteadyNestedClass csc) = true ∧
      (stClassBound st csc).gst + 1 ≤ (fineClassEntry (peakPhysOfBudget bP) csc).gst))

theorem AllocSlotOccRoom.of_groups_eq {bP : FineBudget} {st st' : MallocngSt} {sc : Nat}
    (h : AllocSlotOccRoom bP st sc) (hGs : st'.groups = st.groups) :
    AllocSlotOccRoom bP st' sc := by
  rcases h with hL | ⟨csc, hcsc, hC⟩
  · left; unfold stLiveUserInClass at hL ⊢; rwa [hGs]
  · right; refine ⟨csc, hcsc, ?_⟩
    unfold stClassBound at hC ⊢; rwa [hGs]

theorem AllocSlotOccRoom.of_groupsFreeMono {bP : FineBudget} {st st' : MallocngSt} {sc : Nat}
    (h : AllocSlotOccRoom bP st sc)
    (hNd : (st.groups.map (·.metaPtr)).Nodup)
    (hNd' : (st'.groups.map (·.metaPtr)).Nodup)
    (hMono : GroupsFreeMono st.groups st'.groups) :
    AllocSlotOccRoom bP st' sc := by
  rcases h with hL | ⟨csc, hcsc, hC⟩
  · left
    have hLe := stLiveUserInClass_le_of_groupsFreeMono hNd hNd' hMono sc
    omega
  · right
    have hBLe := stClassBound_le_of_groupsFreeMono hNd hNd' hMono csc
    refine ⟨csc, hcsc, ?_⟩
    rcases hC with ⟨hCan, hGsn⟩ | ⟨hSp, hGst⟩
    · left; exact ⟨hCan, Nat.le_trans (Nat.add_le_add_right hBLe.1 1) hGsn⟩
    · right; exact ⟨hSp, Nat.le_trans (Nat.add_le_add_right hBLe.2.1 1) hGst⟩

theorem nonFreeSlots_succ_le_fineRawOcc {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {bL bP : FineBudget}
    (hFine : FineSplitInv bL bP st)
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hClaim0 : totalClaimedSlots st = 0)
    {sc : Nat} (hsc : sc < 48) (hRoom : AllocSlotOccRoom bP st sc) :
    nonFreeSlots st sc + 1 ≤ fineRawOcc (peakPhysOfBudget bP) sc := by
  rw [nonFreeSlots_eq_user_add_children hClaim0 sc]
  unfold fineRawOcc
  rcases hRoom with hUser | ⟨csc0, hcsc0, hChild⟩
  · have hCh := childMetas_sum_le_childNested hwf hFine.groups_geom hsc
      (fun csc hcsc => hFine.class_bounds csc (by omega))
    omega
  · have hULe := hFine.liveUserInClass_le_peakPhys hsc
    have hCh0 := childMetas_sum_le_of_bounds hwf hFine.groups_geom hsc
      (B := stClassBound st) (fun _ _ => ClassFineBound.le_refl _)
    have hChStrict :
        ((List.range sc).map fun csc =>
          (if canSmallNestIn csc sc then (stClassBound st csc).gsn else 0) +
          (if steadyParent csc == sc && isSteadyNestedClass csc then (stClassBound st csc).gst else 0)).sum + 1 ≤
        fineChildNested (peakPhysOfBudget bP) sc := by
      unfold fineChildNested childNestedFrom
      refine sum_map_strict_le (List.mem_range.mpr hcsc0) (fun csc hcscR => ?_) ?_
      · dsimp only
        have hcsc : csc < sc := List.mem_range.mp hcscR
        have hBc := hFine.class_bounds csc (by omega)
        have hEqE : (fineClassBounds (peakPhysOfBudget bP)).getD csc ClassFineBound.zero =
            fineClassEntry (peakPhysOfBudget bP) csc := rfl
        rw [hEqE]
        have h1 : (if canSmallNestIn csc sc then (stClassBound st csc).gsn else 0) ≤
            (if canSmallNestIn csc sc then (fineClassEntry (peakPhysOfBudget bP) csc).gsn else 0) := by
          split
          · exact hBc.1
          · exact Nat.le_refl 0
        have h2 : (if steadyParent csc == sc && isSteadyNestedClass csc then (stClassBound st csc).gst else 0) ≤
            (if steadyParent csc == sc && isSteadyNestedClass csc then (fineClassEntry (peakPhysOfBudget bP) csc).gst else 0) := by
          split
          · exact hBc.2.1
          · exact Nat.le_refl 0
        omega
      · dsimp only
        have hBc := hFine.class_bounds csc0 (by omega)
        have hEqE : (fineClassBounds (peakPhysOfBudget bP)).getD csc0 ClassFineBound.zero =
            fineClassEntry (peakPhysOfBudget bP) csc0 := rfl
        rw [hEqE]
        rcases hChild with ⟨hCan, hGsn⟩ | ⟨hSp, hGst⟩
        · have h2 : (if steadyParent csc0 == sc && isSteadyNestedClass csc0 then (stClassBound st csc0).gst else 0) ≤
              (if steadyParent csc0 == sc && isSteadyNestedClass csc0 then (fineClassEntry (peakPhysOfBudget bP) csc0).gst else 0) := by
            split
            · exact hBc.2.1
            · exact Nat.le_refl 0
          simp only [hCan, ↓reduceIte]; omega
        · have h1 : (if canSmallNestIn csc0 sc then (stClassBound st csc0).gsn else 0) ≤
              (if canSmallNestIn csc0 sc then (fineClassEntry (peakPhysOfBudget bP) csc0).gsn else 0) := by
            split
            · exact hBc.1
            · exact Nat.le_refl 0
          simp only [hSp, ↓reduceIte]; omega
    omega

private theorem slots_sum_zero_of_no_liveUser {ss : List SlotState}
    (hNo : ∀ s ∈ ss, ∀ p req eff, s ≠ .liveUser p req eff)
    (w : SlotState → Nat)
    (hFreeA : w .freeAvail = 0) (hFreeI : w .freeInactive = 0)
    (hNest : ∀ m, w (.liveNested m) = 0) (hCl : w .claimed = 0) :
    (ss.map w).sum = 0 := by
  induction ss with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hTl := ih (fun s hs => hNo s (List.mem_cons_of_mem _ hs))
    have hHd : w hd = 0 := by
      cases hd with
      | freeAvail => exact hFreeA
      | freeInactive => exact hFreeI
      | liveNested m => exact hNest m
      | claimed => exact hCl
      | liveUser p req eff => exact absurd rfl (hNo _ List.mem_cons_self p req eff)
    omega

theorem newGroupSlots_no_liveUser {lastIdx activeIdx : Nat} :
    ∀ s ∈ newGroupSlots lastIdx activeIdx, ∀ p req eff, s ≠ .liveUser p req eff := by
  intro s hs p req eff hEq
  subst hEq
  unfold newGroupSlots at hs
  rcases List.mem_cons.mp hs with hCl | hApp
  · cases hCl
  · rcases List.mem_append.mp hApp with hRep1 | hRep2
    · cases List.eq_of_mem_replicate hRep1
    · cases List.eq_of_mem_replicate hRep2

private theorem filter_and_sum_le {α : Type} (p q : α → Bool) (f : α → Nat) (xs : List α) :
    ((xs.filter fun x => p x && q x).map f).sum ≤ ((xs.filter p).map f).sum := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons]
    cases hp : p hd <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    · exact ih
    · cases hq : q hd <;> simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons] <;> omega

private theorem length_mul_le_sum {α : Type} {c : Nat} {f : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, c ≤ f x) : xs.length * c ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
    have hHd := h hd List.mem_cons_self
    have hTl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

private theorem sum_le_const_mul_sum {α : Type} {c : Nat} {f g : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, f x ≤ c * g x) : (xs.map f).sum ≤ c * (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    have hHd := h hd List.mem_cons_self
    have hTl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem fineGroups_add_root {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st1 st' : MallocngSt} {bL bP : FineBudget}
    (hFine1 : FineSplitInv bL bP st1)
    (hwf1 : MallocngWFInflight inflight base brkStart brk liveCost peakCost st1)
    (hClaim0 : totalClaimedSlots st1 = 0)
    {sc : Nat} (hsc : sc < 48)
    (hscU : sc < st1.ctx.usageByClass.length)
    (hAct0 : ∀ h : sc < st1.ctx.active.length, st1.ctx.active[sc]'h = 0#64)
    (hRoom : AllocSlotOccRoom bP st1 sc)
    {cg : GroupDesc}
    (hCgSc : cg.sc = sc) (hCgMapPos : 0 < cg.maplen)
    (hCgPair : (cg.cnt, cg.maplen * 4096) ∈ reachableRootPairs sc)
    (hCgNoUser : ∀ s ∈ cg.slots, ∀ p req eff, s ≠ .liveUser p req eff)
    (hMa' : st'.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hGs' : st'.groups = cg :: st1.groups) :
    FineSplitInv bL bP st' ∧ ∀ k < sc, (stClassBound st' k).le (stClassBound st1 k) := by
  have hOccGe1 := nonFreeSlots_succ_le_fineRawOcc hFine1 hwf1 hClaim0 hsc hRoom
  have hUseEq : ((st1.groups.filter (·.sc == sc)).map GroupDesc.cnt).sum = nonFreeSlots st1 sc := by
    rw [← hwf1.usage_wf sc hscU, usage_eq_nonFreeSlots_of_active_zero hwf1 hscU hAct0]
  have hCgBounds := reachableRootPairs_bounds hsc hCgPair
  have hHasRoot : hasRootPair sc = true := hCgBounds.1
  have hCmPos : 1 ≤ cntMinRoot sc := cntMinRoot_pos hsc hHasRoot
  have hEntryEq := fineClassEntry_eq (peakPhys := peakPhysOfBudget bP) hsc
  dsimp only at hEntryEq
  generalize hOcc : fineRawOcc (peakPhysOfBudget bP) sc = occ at hOccGe1 hEntryEq
  have hOccPos : 1 ≤ occ := by omega
  have hOccNe0 : (occ == 0) = false := beq_false_of_ne (by omega)
  have hOtherEq : ∀ k : Nat, k ≠ sc → stClassBound st' k = stClassBound st1 k := by
    intro k hkNe
    have hNeB : (cg.sc == k) = false := beq_false_of_ne (hCgSc ▸ hkNe.symm)
    unfold stClassBound
    simp [hGs', hNeB]
  have hScBound : (stClassBound st' sc).le (fineClassEntry (peakPhysOfBudget bP) sc) := by
    let roots1 := st1.groups.filter fun g => (g.sc == sc) && isRootGroup g
    have hRootsCntLe : (roots1.map GroupDesc.cnt).sum ≤ occ := by
      have hSub := filter_and_sum_le (·.sc == sc) isRootGroup GroupDesc.cnt st1.groups
      dsimp [roots1]; omega
    have hRootEach : ∀ g ∈ roots1,
        cntMinRoot sc ≤ g.cnt ∧ g.maplen * 4096 ≤ ceilRootPerSlot sc * g.cnt := by
      intro g hgR
      obtain ⟨hg1, hgCond⟩ := List.mem_filter.mp hgR
      simp only [isRootGroup, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hgCond
      have hGPair := (hFine1.groups_geom g hg1 (hgCond.1 ▸ hsc)).2.2 hgCond.2
      rw [hgCond.1] at hGPair
      have hB := reachableRootPairs_bounds hsc hGPair
      exact ⟨hB.2.2.2.1, hB.2.2.2.2.2.2.1⟩
    have hGrLe : roots1.length ≤ occ / cntMinRoot sc := by
      rw [Nat.le_div_iff_mul_le hCmPos]
      exact Nat.le_trans (length_mul_le_sum fun g hg => (hRootEach g hg).1) hRootsCntLe
    have hRb1Le : (roots1.map fun g => g.maplen * 4096).sum ≤ ceilRootPerSlot sc * occ :=
      Nat.le_trans (sum_le_const_mul_sum fun g hg => (hRootEach g hg).2)
        (Nat.mul_le_mul_left _ hRootsCntLe)
    have hCgRbLe : cg.maplen * 4096 ≤ maxRootBytes sc := hCgBounds.2.2.2.2.2.1
    have hB1 := hFine1.class_bounds sc hsc
    have hSmF : isSmallNestedGroup cg = false := by
      unfold isSmallNestedGroup; simp [Nat.ne_of_gt hCgMapPos]
    have hStF : isSteadyNestedGroup cg = false := by
      unfold isSteadyNestedGroup; simp [Nat.ne_of_gt hCgMapPos]
    have hRtT : isRootGroup cg = true := by
      unfold isRootGroup; simp [hCgMapPos]
    simp only [hOccNe0, Bool.false_eq_true, ↓reduceIte] at hEntryEq
    unfold ClassFineBound.le
    rw [hEntryEq]
    dsimp only
    simp only [hHasRoot, ↓reduceIte]
    have hSt'Eq :
        (stClassBound st' sc).gsn = (stClassBound st1 sc).gsn ∧
        (stClassBound st' sc).gst = (stClassBound st1 sc).gst ∧
        (stClassBound st' sc).gr = roots1.length + 1 ∧
        (stClassBound st' sc).rb = cg.maplen * 4096 + (roots1.map fun g => g.maplen * 4096).sum := by
      unfold stClassBound
      simp [hGs', hCgSc, hSmF, hStF, hRtT, roots1, Nat.add_comm]
    rw [hSt'Eq.1, hSt'Eq.2.1, hSt'Eq.2.2.1, hSt'Eq.2.2.2]
    have hGsn1 : (stClassBound st1 sc).gsn ≤ maxSmallNestedGroups sc := by
      have := hB1.1; rw [hEntryEq] at this; exact this
    have hGst1 : (stClassBound st1 sc).gst ≤ if isSteadyNestedClass sc then 1 + occ / steadyCnt sc else 0 := by
      have := hB1.2.1; rw [hEntryEq] at this; exact this
    exact ⟨hGsn1, hGst1, by simpa [Nat.add_comm] using Nat.add_le_add_right hGrLe 1,
      Nat.add_le_add hCgRbLe hRb1Le⟩
  refine ⟨?_, fun k hk => by rw [hOtherEq k (by omega)]; exact ClassFineBound.le_refl _⟩
  refine
    { live_inv        := hFine1.live_inv
      peak_inv        := hFine1.peak_inv
      peaks_le        := hFine1.peaks_le
      meta_le         := hMa'
      groups_geom     := fun g' hg' => by
        rw [hGs'] at hg'
        rcases List.mem_cons.mp hg' with rfl | hg1
        · intro _
          refine ⟨fun s hs p req eff hsEq => absurd hsEq (hCgNoUser s hs p req eff),
            fun hMl0 => absurd hMl0 (Nat.ne_of_gt hCgMapPos),
            fun _ => hCgSc ▸ hCgPair⟩
        · intro hscG
          have hG1 := hFine1.groups_geom g' hg1 hscG
          refine ⟨hG1.1, fun hMl0 => ?_, hG1.2.2⟩
          obtain ⟨hK, pg, hpg, hPar, hPsc⟩ := hG1.2.1 hMl0
          exact ⟨hK, pg, hGs' ▸ List.mem_cons_of_mem _ hpg, hPar, hPsc⟩
      class_bounds    := fun k hk => by
        by_cases hEq : k = sc
        · subst hEq; exact hScBound
        · rw [hOtherEq k hEq]; exact hFine1.class_bounds k hk
      liveNom_le      := fun k hk => by
        unfold stLiveByNom
        rw [hGs', List.map_cons, List.sum_cons,
          slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
        exact hFine1.liveNom_le k hk
      reallocCross_le := fun k hk => by
        unfold stReallocCrossByNom
        rw [hGs', List.filter_cons]
        split
        · rw [List.map_cons, List.sum_cons,
            slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
          exact hFine1.reallocCross_le k hk
        · exact hFine1.reallocCross_le k hk
      exc_le          := fun k hk => by
        unfold stOverAlignInClass
        rw [hGs', List.filter_cons]
        split
        · rw [List.map_cons, List.sum_cons,
            slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
          exact hFine1.exc_le k hk
        · exact hFine1.exc_le k hk
      live63Count_le  := by
        unfold stLive63Count
        rw [hGs', List.map_cons, List.sum_cons,
          slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
        exact hFine1.live63Count_le
      live63Bytes_le  := by
        unfold stLive63Bytes
        rw [hGs', List.map_cons, List.sum_cons,
          slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
        exact hFine1.live63Bytes_le
      straddle63_le   := by
        unfold stStraddle63
        rw [hGs', List.filter_cons]
        split
        · rw [List.map_cons, List.sum_cons,
            slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
          exact hFine1.straddle63_le
        · exact hFine1.straddle63_le
      overAlign_le    := by
        unfold stOverAlign
        rw [hGs', List.map_cons, List.sum_cons,
          slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
        exact hFine1.overAlign_le }

/-- Witness packaged at `alloc_group` nested-path pre-call (`st1`) and consumed after recursive
    `alloc_slot(pSc, needed)` (`st2 ↦ st'`). -/
def NestedFinePrep (bP : FineBudget) (st1 : MallocngSt) (sc cnt' : Nat) : Prop :=
  (isSteadyNestedClass sc = true ∧ cnt' = steadyCnt sc ∧
    (stClassBound st1 sc).gst + 1 ≤ (fineClassEntry (peakPhysOfBudget bP) sc).gst) ∨
  (¬ (isSteadyNestedClass sc = true ∧ cnt' = steadyCnt sc) ∧
    cnt' ≤ 32 ∧ isSmallNestedCnt sc cnt' = true ∧
    (stClassBound st1 sc).gsn + 1 ≤ (fineClassEntry (peakPhysOfBudget bP) sc).gsn)

theorem fineGroups_nested_parent_prep {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st1 : MallocngSt} {bL bP : FineBudget}
    (hFine1 : FineSplitInv bL bP st1)
    (hwf1 : MallocngWFInflight inflight base brkStart brk liveCost peakCost st1)
    (hClaim0 : totalClaimedSlots st1 = 0)
    {sc cnt' : Nat} (hsc : sc < 48)
    (hscU : sc < st1.ctx.usageByClass.length)
    (hAct0 : ∀ h : sc < st1.ctx.active.length, st1.ctx.active[sc]'h = 0#64)
    (hRoom : AllocSlotOccRoom bP st1 sc)
    (hCntSel : cnt' = cntSel sc (st1.ctx.usageByClass[sc]'hscU).toNat)
    (hNest : cnt' * slotStride sc + 16 ≤ 2048) :
    let pSc := sizeToClassUnits (cnt' * sizeClass sc)
    AllocSlotOccRoom bP st1 pSc ∧ NestedFinePrep bP st1 sc cnt' := by
  intro pSc
  have hOccGe1 := nonFreeSlots_succ_le_fineRawOcc hFine1 hwf1 hClaim0 hsc hRoom
  have hUseVal : (st1.ctx.usageByClass[sc]'hscU).toNat = nonFreeSlots st1 sc :=
    usage_eq_nonFreeSlots_of_active_zero hwf1 hscU hAct0
  have hSumCnt : ((st1.groups.filter (·.sc == sc)).map GroupDesc.cnt).sum = nonFreeSlots st1 sc :=
    (hwf1.usage_wf sc hscU).symm.trans hUseVal
  have hEntryEq := fineClassEntry_eq (peakPhys := peakPhysOfBudget bP) hsc
  dsimp only at hEntryEq
  generalize hOcc : fineRawOcc (peakPhysOfBudget bP) sc = occ at hOccGe1 hEntryEq
  have hOccNe0 : (occ == 0) = false := beq_false_of_ne (by omega)
  simp only [hOccNe0, Bool.false_eq_true, ↓reduceIte] at hEntryEq
  by_cases hSt : isSteadyNestedClass sc = true ∧ cnt' = steadyCnt sc
  · obtain ⟨hIsSt, hCntSt⟩ := hSt
    have hStProps := steadyParent_props hsc hIsSt
    have hStPos : 1 ≤ steadyCnt sc := by omega
    have hPscEq : pSc = steadyParent sc := by
      dsimp [pSc, steadyParent]; rw [hCntSt]
    let stGrps := st1.groups.filter fun g => (g.sc == sc) && isSteadyNestedGroup g
    have hStCntLe : (stGrps.map GroupDesc.cnt).sum ≤ occ := by
      have hSub := filter_and_sum_le (·.sc == sc) isSteadyNestedGroup GroupDesc.cnt st1.groups
      dsimp [stGrps]; omega
    have hEachSt : ∀ g ∈ stGrps, steadyCnt sc ≤ g.cnt := by
      intro g hgG
      have hCond := (List.mem_filter.mp hgG).2
      simp only [isSteadyNestedGroup, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hCond
      rw [hCond.2.2, hCond.1]
      exact Nat.le_refl _
    have hGstLe : stGrps.length ≤ occ / steadyCnt sc := by
      rw [Nat.le_div_iff_mul_le hStPos]
      exact Nat.le_trans (length_mul_le_sum hEachSt) hStCntLe
    have hGstSucc : (stClassBound st1 sc).gst + 1 ≤ (fineClassEntry (peakPhysOfBudget bP) sc).gst := by
      rw [hEntryEq]
      dsimp only [stClassBound]
      simp only [hIsSt, ↓reduceIte]
      dsimp [stGrps] at hGstLe
      omega
    refine ⟨Or.inr ⟨sc, hPscEq ▸ hStProps.2.1, Or.inr ⟨?_, hGstSucc⟩⟩,
      Or.inl ⟨hIsSt, hCntSt, hGstSucc⟩⟩
    simp [hPscEq, hIsSt]
  · have hSm := smallNested_of_cntSel hsc hCntSel hNest hSt
    obtain ⟨hULt128, hCnt32, hSmCnt⟩ := hSm
    have hSmProps := smallNestedCnt_props hsc hCnt32 hSmCnt
    obtain ⟨hHasSm, _, _, hScLtPsc, _, hCanNest⟩ := hSmProps
    have hCmGe2 : 2 ≤ cntMinSmallNested sc := cntMinSmallNested_ge_two hsc hHasSm
    let smGrps := st1.groups.filter fun g => (g.sc == sc) && isSmallNestedGroup g
    have hSmCntLe127 : (smGrps.map GroupDesc.cnt).sum ≤ 127 := by
      have hSub := filter_and_sum_le (·.sc == sc) isSmallNestedGroup GroupDesc.cnt st1.groups
      dsimp [smGrps]
      omega
    have hEachSm : ∀ g ∈ smGrps, cntMinSmallNested sc ≤ g.cnt := by
      intro g hgG
      obtain ⟨hg1, hCond⟩ := List.mem_filter.mp hgG
      simp only [isSmallNestedGroup, Bool.and_eq_true, Bool.not_eq_true',
        beq_iff_eq, decide_eq_true_eq] at hCond
      obtain ⟨hGSc, hGMl0, hGNotStB⟩ := hCond
      have hGeomG := (hFine1.groups_geom g hg1 (hGSc ▸ hsc)).2.1 hGMl0
      rcases hGeomG.1 with ⟨hGIsSt, hGCntSt⟩ | ⟨hGCnt32, hGSm⟩
      · simp [hGIsSt, hGCntSt] at hGNotStB
      · rw [hGSc] at hGSm
        exact (smallNestedCnt_props hsc hGCnt32 hGSm).2.2.1
    have hGsnLe : smGrps.length ≤ 127 / cntMinSmallNested sc := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      exact Nat.le_trans (length_mul_le_sum hEachSm) hSmCntLe127
    have hGsnSucc : (stClassBound st1 sc).gsn + 1 ≤ (fineClassEntry (peakPhysOfBudget bP) sc).gsn := by
      rw [hEntryEq]
      dsimp only [stClassBound, maxSmallNestedGroups]
      simp only [hHasSm, ↓reduceIte]
      dsimp [smGrps] at hGsnLe
      omega
    exact ⟨Or.inr ⟨sc, hScLtPsc, Or.inl ⟨hCanNest, hGsnSucc⟩⟩,
      Or.inr ⟨hSt, hCnt32, hSmCnt, hGsnSucc⟩⟩

theorem fineGroups_add_nested {st1 st2 st' : MallocngSt} {bL bP : FineBudget}
    (hFine2 : FineSplitInv bL bP st2)
    (hNd2 : (st2.groups.map (·.metaPtr)).Nodup)
    {sc cnt' : Nat} (hsc : sc < 48)
    (hPrep : NestedFinePrep bP st1 sc cnt')
    (hLow2 : ∀ k ≤ sc, (stClassBound st2 k).le (stClassBound st1 k))
    {pg pg' cg : GroupDesc} (hpg : pg ∈ st2.groups)
    {pIdx : Nat} (hpIdx : pIdx < pg.slots.length)
    (hPgSc : pg.sc = sizeToClassUnits (cnt' * sizeClass sc))
    (hScLtPg : sc < pg.sc)
    (hPgMeta : pg'.metaPtr = pg.metaPtr) (hPgSc' : pg'.sc = pg.sc)
    (hPgCnt' : pg'.cnt = pg.cnt) (hPgMl' : pg'.maplen = pg.maplen)
    (hPgPar' : pg'.parentMeta = pg.parentMeta)
    {m : BitVec 64} (hPgSl' : pg'.slots = pg.slots.set pIdx (.liveNested m))
    (hCgSc : cg.sc = sc) (hCgCnt : cg.cnt = cnt') (hCgMl0 : cg.maplen = 0)
    (hCgPar : cg.parentMeta = some pg.metaPtr)
    (hCgNoUser : ∀ s ∈ cg.slots, ∀ p req eff, s ≠ .liveUser p req eff)
    (hMa' : st'.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hGs' : st'.groups = cg :: st2.groups.map fun g => if g.metaPtr == pg.metaPtr then pg' else g) :
    FineSplitInv bL bP st' ∧ ∀ k < sc, (stClassBound st' k).le (stClassBound st1 k) := by
  let stMid : MallocngSt :=
    { st2 with groups := st2.groups.map fun g => if g.metaPtr == pg.metaPtr then pg' else g }
  have hMidGs : stMid.groups = st2.groups.map fun g => if g.metaPtr == pg.metaPtr then pg' else g := rfl
  have hMidCB : ∀ k, stClassBound stMid k = stClassBound st2 k := fun k =>
    stClassBound_eq_of_map_ite hNd2 hpg hPgSc' hPgCnt' hMidGs k (fun _ => hPgMl')
  have hMidGeom : ∀ x' ∈ stMid.groups, GroupFineGeom stMid x' :=
    groupFineGeom_of_map_ite hNd2 hFine2.groups_geom hpg
      hPgMeta hPgSc' hPgCnt' (fun _ => hPgMl') hPgPar' hMidGs
      (fun hsc' s hs p' req' eff' hsEq => by
        rw [hPgSl'] at hs
        rcases List.mem_or_eq_of_mem_set hs with hsOld | hNestEq
        · rw [hPgSc']; exact (hFine2.groups_geom pg hpg (hPgSc' ▸ hsc')).1 s hsOld p' req' eff' hsEq
        · cases hNestEq.symm.trans hsEq)
  have hOtherEq : ∀ k : Nat, k ≠ sc → stClassBound st' k = stClassBound st2 k := by
    intro k hkNe
    have hNeB : (cg.sc == k) = false := beq_false_of_ne (hCgSc ▸ hkNe.symm)
    have : stClassBound st' k = stClassBound stMid k := by
      unfold stClassBound; simp [hGs', hMidGs, hNeB]
    exact this.trans (hMidCB k)
  have hScBound : (stClassBound st' sc).le (fineClassEntry (peakPhysOfBudget bP) sc) := by
    have hB2 := hFine2.class_bounds sc hsc
    have hLe21 := hLow2 sc (Nat.le_refl sc)
    have hRtF : isRootGroup cg = false := by unfold isRootGroup; simp [hCgMl0]
    rcases hPrep with ⟨hIsSt, hCntSt, hGst1⟩ | ⟨hNotSt, hCnt32, hSmCnt, hGsn1⟩
    · have hStT : isSteadyNestedGroup cg = true := by
        unfold isSteadyNestedGroup; simp [hCgMl0, hCgSc, hIsSt, hCgCnt, hCntSt]
      have hSmF : isSmallNestedGroup cg = false := by
        unfold isSmallNestedGroup; simp [hCgMl0, hCgSc, hIsSt, hCgCnt, hCntSt]
      have hEq :
          (stClassBound st' sc).gsn = (stClassBound st2 sc).gsn ∧
          (stClassBound st' sc).gst = (stClassBound st2 sc).gst + 1 ∧
          (stClassBound st' sc).gr = (stClassBound st2 sc).gr ∧
          (stClassBound st' sc).rb = (stClassBound st2 sc).rb := by
        have hMid := hMidCB sc
        unfold stClassBound at hMid ⊢
        rw [hGs', ← hMidGs]
        simp [hCgSc, hSmF, hStT, hRtF]
        exact ⟨congrArg ClassFineBound.gsn hMid,
          by have := congrArg ClassFineBound.gst hMid; omega,
          congrArg ClassFineBound.gr hMid,
          congrArg ClassFineBound.rb hMid⟩
      unfold ClassFineBound.le
      rw [hEq.1, hEq.2.1, hEq.2.2.1, hEq.2.2.2]
      exact ⟨hB2.1, Nat.le_trans (Nat.add_le_add_right hLe21.2.1 1) hGst1, hB2.2.2.1, hB2.2.2.2⟩
    · have hStF : isSteadyNestedGroup cg = false := by
        unfold isSteadyNestedGroup
        simp only [hCgMl0, decide_true, hCgSc, hCgCnt, Bool.true_and]
        cases hB : isSteadyNestedClass sc && decide (cnt' = steadyCnt sc)
        · rfl
        · rw [Bool.and_eq_true, decide_eq_true_eq] at hB; exact absurd hB hNotSt
      have hSmT : isSmallNestedGroup cg = true := by
        unfold isSmallNestedGroup
        simp only [hCgMl0, decide_true, hCgSc, hCgCnt, Bool.true_and]
        cases hB : isSteadyNestedClass sc && decide (cnt' = steadyCnt sc)
        · rfl
        · rw [Bool.and_eq_true, decide_eq_true_eq] at hB; exact absurd hB hNotSt
      have hEq :
          (stClassBound st' sc).gsn = (stClassBound st2 sc).gsn + 1 ∧
          (stClassBound st' sc).gst = (stClassBound st2 sc).gst ∧
          (stClassBound st' sc).gr = (stClassBound st2 sc).gr ∧
          (stClassBound st' sc).rb = (stClassBound st2 sc).rb := by
        have hMid := hMidCB sc
        unfold stClassBound at hMid ⊢
        rw [hGs', ← hMidGs]
        simp [hCgSc, hSmT, hStF, hRtF]
        exact ⟨by have := congrArg ClassFineBound.gsn hMid; omega,
          congrArg ClassFineBound.gst hMid,
          congrArg ClassFineBound.gr hMid,
          congrArg ClassFineBound.rb hMid⟩
      unfold ClassFineBound.le
      rw [hEq.1, hEq.2.1, hEq.2.2.1, hEq.2.2.2]
      exact ⟨Nat.le_trans (Nat.add_le_add_right hLe21.1 1) hGsn1, hB2.2.1, hB2.2.2.1, hB2.2.2.2⟩
  refine ⟨?_, fun k hk => ?_⟩
  · refine
      { live_inv        := hFine2.live_inv
        peak_inv        := hFine2.peak_inv
        peaks_le        := hFine2.peaks_le
        meta_le         := hMa'
        groups_geom     := fun g' hg' => by
          rw [hGs', ← hMidGs] at hg'
          rcases List.mem_cons.mp hg' with rfl | hgMid
          · intro _
            refine ⟨fun s hs p req eff hsEq => absurd hsEq (hCgNoUser s hs p req eff),
              fun _ => ?_,
              fun hPos => absurd hCgMl0 (Nat.ne_of_gt hPos)⟩
            have hPg'Mem : pg' ∈ st'.groups := by
              rw [hGs']
              refine List.mem_cons_of_mem _ ?_
              have := List.mem_map_of_mem (f := fun g => if g.metaPtr == pg.metaPtr then pg' else g) hpg
              simpa using this
            refine ⟨?_, pg', hPg'Mem, hCgPar.trans (congrArg some hPgMeta.symm),
              hPgSc'.trans (hPgSc.trans (by rw [hCgCnt, hCgSc]))⟩
            rcases hPrep with ⟨hIsSt, hCntSt, _⟩ | ⟨_, hCnt32, hSmCnt, _⟩
            · left; exact ⟨hCgSc ▸ hIsSt, hCgCnt.trans (hCntSt.trans (by rw [hCgSc]))⟩
            · right; exact ⟨hCgCnt ▸ hCnt32, by rwa [hCgSc, hCgCnt]⟩
          · intro hscG
            have hGM := hMidGeom g' hgMid hscG
            refine ⟨hGM.1, fun hMl0 => ?_, hGM.2.2⟩
            obtain ⟨hK, qg, hqg, hPar, hQsc⟩ := hGM.2.1 hMl0
            exact ⟨hK, qg, hGs' ▸ List.mem_cons_of_mem _ hqg, hPar, hQsc⟩
        class_bounds    := fun k hk => by
          by_cases hEq : k = sc
          · subst hEq; exact hScBound
          · rw [hOtherEq k hEq]; exact hFine2.class_bounds k hk
        liveNom_le      := fun k hk => by
          have hSum := groupSlotSum_map_ite_eq hNd2 hpg hpIdx (.liveNested m) hPgSl' (slotLiveNom k)
          unfold stLiveByNom
          rw [hGs', List.map_cons, List.sum_cons,
            slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
          have hLe : ((stMid.groups.map fun g => (g.slots.map (slotLiveNom k)).sum).sum) ≤ stLiveByNom st2 k := by
            unfold stLiveByNom; dsimp [stMid]
            have : slotLiveNom k (.liveNested m) = 0 := rfl
            omega
          exact Nat.le_trans hLe (hFine2.liveNom_le k hk)
        reallocCross_le := fun k hk => by
          have hSum := filterGroupSlotSum_map_ite_eq hNd2 hpg (fun x => decide (x.sc < 48))
            (by simp [hPgSc']) hpIdx (.liveNested m) hPgSl' (fun x => slotReallocCross x.sc k)
            (fun _ => by simp [hPgSc'])
          unfold stReallocCrossByNom
          rw [hGs', List.filter_cons]
          have hLe : ((stMid.groups.filter (·.sc < 48)).map fun g =>
              (g.slots.map (slotReallocCross g.sc k)).sum).sum ≤ stReallocCrossByNom st2 k := by
            unfold stReallocCrossByNom; dsimp [stMid]
            have hN0 : (if decide (pg.sc < 48) then slotReallocCross pg.sc k (.liveNested m) else 0) = 0 := by
              split <;> rfl
            rw [hN0] at hSum; omega
          split
          · rw [List.map_cons, List.sum_cons,
              slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
            exact Nat.le_trans hLe (hFine2.reallocCross_le k hk)
          · exact Nat.le_trans hLe (hFine2.reallocCross_le k hk)
        exc_le          := fun k hk => by
          have hSum := filterGroupSlotSum_map_ite_eq hNd2 hpg (·.sc == k)
            (by simp [hPgSc']) hpIdx (.liveNested m) hPgSl' (fun _ => slotHasOverAlign) (fun _ => rfl)
          unfold stOverAlignInClass
          rw [hGs', List.filter_cons]
          have hLe : ((stMid.groups.filter (·.sc == k)).map fun g =>
              (g.slots.map slotHasOverAlign).sum).sum ≤ stOverAlignInClass st2 k := by
            unfold stOverAlignInClass; dsimp [stMid]
            have hN0 : (if pg.sc == k then slotHasOverAlign (.liveNested m) else 0) = 0 := by
              split <;> rfl
            rw [hN0] at hSum; omega
          split
          · rw [List.map_cons, List.sum_cons,
              slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
            exact Nat.le_trans hLe (hFine2.exc_le k hk)
          · exact Nat.le_trans hLe (hFine2.exc_le k hk)
        live63Count_le  := by
          have hSum := groupSlotSum_map_ite_eq hNd2 hpg hpIdx (.liveNested m) hPgSl' slotLive63Count
          unfold stLive63Count
          rw [hGs', List.map_cons, List.sum_cons,
            slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
          have hLe : (stMid.groups.map fun g => (g.slots.map slotLive63Count).sum).sum ≤ stLive63Count st2 := by
            unfold stLive63Count; dsimp [stMid]
            have : slotLive63Count (.liveNested m) = 0 := rfl
            omega
          exact Nat.le_trans hLe hFine2.live63Count_le
        live63Bytes_le  := by
          have hSum := groupSlotSum_map_ite_eq hNd2 hpg hpIdx (.liveNested m) hPgSl' slotLive63Bytes
          unfold stLive63Bytes
          rw [hGs', List.map_cons, List.sum_cons,
            slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
          have hLe : (stMid.groups.map fun g => (g.slots.map slotLive63Bytes).sum).sum ≤ stLive63Bytes st2 := by
            unfold stLive63Bytes; dsimp [stMid]
            have : slotLive63Bytes (.liveNested m) = 0 := rfl
            omega
          exact Nat.le_trans hLe hFine2.live63Bytes_le
        straddle63_le   := by
          have hSum := filterGroupSlotSum_map_ite_eq hNd2 hpg (·.sc == 63)
            (by simp [hPgSc']) hpIdx (.liveNested m) hPgSl' (fun _ => slotStraddle63) (fun _ => rfl)
          unfold stStraddle63
          rw [hGs', List.filter_cons]
          have hLe : ((stMid.groups.filter (·.sc == 63)).map fun g =>
              (g.slots.map slotStraddle63).sum).sum ≤ stStraddle63 st2 := by
            unfold stStraddle63; dsimp [stMid]
            have hN0 : (if pg.sc == 63 then slotStraddle63 (.liveNested m) else 0) = 0 := by
              split <;> rfl
            rw [hN0] at hSum; omega
          split
          · rw [List.map_cons, List.sum_cons,
              slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
            exact Nat.le_trans hLe hFine2.straddle63_le
          · exact Nat.le_trans hLe hFine2.straddle63_le
        overAlign_le    := by
          have hSum := groupSlotSum_map_ite_eq hNd2 hpg hpIdx (.liveNested m) hPgSl' slotOverAlign
          unfold stOverAlign
          rw [hGs', List.map_cons, List.sum_cons,
            slots_sum_zero_of_no_liveUser hCgNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
          have hLe : (stMid.groups.map fun g => (g.slots.map slotOverAlign).sum).sum ≤ stOverAlign st2 := by
            unfold stOverAlign; dsimp [stMid]
            have : slotOverAlign (.liveNested m) = 0 := rfl
            omega
          exact Nat.le_trans hLe hFine2.overAlign_le }
  · rw [hOtherEq k (by omega)]
    exact hLow2 k (by omega)

/-! ## 6. Post-Allocation Enframe, Large `mmap`, `aligned_alloc` Reframe & `realloc` -/

theorem fineSplitInv_insert_large63 {bL bP : FineBudget} {st1 st2 : MallocngSt}
    (hSplit : FineSplitInv bL bP st1)
    {gNew : GroupDesc} (hSc63 : gNew.sc = 63)
    (hNoUser : ∀ s ∈ gNew.slots, ∀ p req eff, s ≠ .liveUser p req eff)
    (hMa : st2.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hGs : st2.groups = gNew :: st1.groups) :
    FineSplitInv bL bP st2 where
  live_inv        := hSplit.live_inv
  peak_inv        := hSplit.peak_inv
  peaks_le        := hSplit.peaks_le
  meta_le         := hMa
  groups_geom     := fun g' hg' => by
    rw [hGs] at hg'
    rcases List.mem_cons.mp hg' with rfl | hg1
    · intro h48; omega
    · intro h48
      have hG1 := hSplit.groups_geom g' hg1 h48
      refine ⟨hG1.1, fun hMl0 => ?_, hG1.2.2⟩
      obtain ⟨hK, pg, hpg, hPar, hPsc⟩ := hG1.2.1 hMl0
      exact ⟨hK, pg, hGs ▸ List.mem_cons_of_mem _ hpg, hPar, hPsc⟩
  class_bounds    := fun sc hsc => by
    have hNe : (gNew.sc == sc) = false := beq_false_of_ne (by omega)
    have hEq : stClassBound st2 sc = stClassBound st1 sc := by
      unfold stClassBound; simp [hGs, hNe]
    rw [hEq]; exact hSplit.class_bounds sc hsc
  liveNom_le      := fun k hk => by
    unfold stLiveByNom
    rw [hGs, List.map_cons, List.sum_cons,
      slots_sum_zero_of_no_liveUser hNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
    exact hSplit.liveNom_le k hk
  reallocCross_le := fun k hk => by
    unfold stReallocCrossByNom
    rw [hGs, List.filter_cons]
    have hF : decide (gNew.sc < 48) = false := decide_eq_false (by omega)
    simp only [hF, Bool.false_eq_true, ↓reduceIte]
    exact hSplit.reallocCross_le k hk
  exc_le          := fun sc hsc => by
    unfold stOverAlignInClass
    rw [hGs, List.filter_cons]
    have hF : (gNew.sc == sc) = false := beq_false_of_ne (by omega)
    simp only [hF, Bool.false_eq_true, ↓reduceIte]
    exact hSplit.exc_le sc hsc
  live63Count_le  := by
    unfold stLive63Count
    rw [hGs, List.map_cons, List.sum_cons,
      slots_sum_zero_of_no_liveUser hNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
    exact hSplit.live63Count_le
  live63Bytes_le  := by
    unfold stLive63Bytes
    rw [hGs, List.map_cons, List.sum_cons,
      slots_sum_zero_of_no_liveUser hNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
    exact hSplit.live63Bytes_le
  straddle63_le   := by
    unfold stStraddle63
    rw [hGs, List.filter_cons]
    split
    · rw [List.map_cons, List.sum_cons,
        slots_sum_zero_of_no_liveUser hNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
      exact hSplit.straddle63_le
    · exact hSplit.straddle63_le
  overAlign_le    := by
    unfold stOverAlign
    rw [hGs, List.map_cons, List.sum_cons,
      slots_sum_zero_of_no_liveUser hNoUser _ rfl rfl (fun _ => rfl) rfl, Nat.zero_add]
    exact hSplit.overAlign_le

theorem fineGroupsInv_enframe_alloc {bgt0 : FineBudget} {req : Nat} {st1 st2 : MallocngSt}
    (hSplit : FineSplitInv bgt0 (fineStepAlloc req bgt0) st1)
    (hNd : (st1.groups.map (·.metaPtr)).Nodup)
    {g g' : GroupDesc} (hg : g ∈ st1.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hSmall : req ≤ MmapThresholdReq → g.sc < 48 ∧ allowedPhysClass (nomSc req) g.sc = true)
    (hLarge : MmapThresholdReq < req → g.sc = 63)
    {p : BitVec 64}
    (hMeta : g'.metaPtr = g.metaPtr) (hSc : g'.sc = g.sc)
    (hCnt : g'.cnt = g.cnt) (hMl : g'.maplen = g.maplen)
    (hPar : g'.parentMeta = g.parentMeta)
    (hSl : g'.slots = g.slots.set idx (.liveUser p req (max req MallocngMinBlockCost)))
    (hMa : st2.metaAreas = st1.metaAreas)
    (hGs : st2.groups = st1.groups.map fun h => if h.metaPtr == g.metaPtr then g' else h) :
    FineGroupsInv (fineStepAlloc req bgt0) st2 := by
  let sNew := SlotState.liveUser p req (max req MallocngMinBlockCost)
  refine
    { live_inv        := hSplit.peak_inv
      peak_inv        := hSplit.peak_inv
      peaks_le        := FinePeaksLe.refl (fineStepAlloc req bgt0)
      meta_le         := by rw [hMa]; exact hSplit.meta_le
      groups_geom     := groupFineGeom_of_map_ite hNd hSplit.groups_geom hg
        hMeta hSc hCnt (fun _ => hMl) hPar hGs (fun hsc' s hs p' req' eff' hsEq => by
          rw [hSl] at hs
          rcases List.mem_or_eq_of_mem_set hs with hsOld | hNewEq
          · rw [hSc]; exact (hSplit.groups_geom g hg (hSc ▸ hsc')).1 s hsOld p' req' eff' hsEq
          · cases hNewEq.symm.trans hsEq
            have hReqLe : req ≤ MmapThresholdReq := Classical.byContradiction fun hGt => by
              have h63 := hLarge (by omega)
              omega
            refine ⟨hReqLe, fun _ => ?_⟩
            rw [hSc]
            exact allowedPhysClass_imp_canHold (hSmall hReqLe).2)
      class_bounds    := fun sc hsc => by
        rw [stClassBound_eq_of_map_ite hNd hg hSc hCnt hGs sc (fun _ => hMl)]
        exact hSplit.class_bounds sc hsc
      liveNom_le      := fun k hk => by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl (slotLiveNom k)
        rw [hClaimed] at hSum
        have hSt2 : stLiveByNom st2 k = stLiveByNom st1 k + slotLiveNom k sNew := by
          unfold stLiveByNom; rw [hGs]; simpa [slotLiveNom] using hSum
        have hLe1 := hSplit.liveNom_le k hk
        rw [hSt2]
        by_cases hReqLe : req ≤ MmapThresholdReq
        · simp only [fineStepAlloc, hReqLe, ↓reduceIte, vec48Of_getD, hk]
          by_cases hEqK : k = nomSc req
          · subst hEqK
            simp only [sNew, slotLiveNom, hReqLe, decide_true, beq_self_eq_true, Bool.true_and, ↓reduceIte]
            omega
          · have hNe1 : (k == nomSc req) = false := beq_false_of_ne hEqK
            have hNe2 : (nomSc req == k) = false := beq_false_of_ne (Ne.symm hEqK)
            simp only [sNew, slotLiveNom, hReqLe, decide_true, hNe1, hNe2, Bool.true_and,
              Bool.false_eq_true, ↓reduceIte]
            omega
        · simp only [fineStepAlloc, sNew, slotLiveNom, hReqLe, decide_false, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte]
          omega
      reallocCross_le := fun k hk => by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (fun x => decide (x.sc < 48))
          (by simp [hSc]) hIdx sNew hSl (fun x => slotReallocCross x.sc k)
          (fun _ => by simp [hSc])
        rw [hClaimed] at hSum
        have hZeroNew : (if decide (g.sc < 48) then slotReallocCross g.sc k sNew else 0) = 0 := by
          by_cases hsc48 : g.sc < 48
          · have hReqLe : req ≤ MmapThresholdReq := Classical.byContradiction fun hGt => by
              have := hLarge (by omega); omega
            have hAl := (hSmall hReqLe).2
            simp only [hsc48, decide_true, ↓reduceIte, sNew, slotReallocCross]
            by_cases hEqK : nomSc req = k
            · subst hEqK; simp [hAl]
            · simp [beq_false_of_ne hEqK]
          · simp [hsc48]
        have hEq : stReallocCrossByNom st2 k = stReallocCrossByNom st1 k := by
          unfold stReallocCrossByNom; rw [hGs]
          have : (if decide (g.sc < 48) then slotReallocCross g.sc k .claimed else 0) = 0 := by
            split <;> rfl
          rw [this, hZeroNew] at hSum; omega
        rw [hEq]
        exact Nat.le_trans (hSplit.reallocCross_le k hk) (hSplit.peaks_le.realloc_le k hk)
      exc_le          := fun sc hsc => by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == sc)
          (by simp [hSc]) hIdx sNew hSl (fun _ => slotHasOverAlign) (fun _ => rfl)
        rw [hClaimed] at hSum
        have hEq : stOverAlignInClass st2 sc = stOverAlignInClass st1 sc := by
          unfold stOverAlignInClass; rw [hGs]
          have h1 : (if g.sc == sc then slotHasOverAlign .claimed else 0) = 0 := by split <;> rfl
          have h2 : (if g.sc == sc then slotHasOverAlign sNew else 0) = 0 := by
            simp [sNew, slotHasOverAlign]
          rw [h1, h2] at hSum; omega
        rw [hEq]
        exact Nat.le_trans (hSplit.exc_le sc hsc) (hSplit.peaks_le.exc_le sc hsc)
      live63Count_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl slotLive63Count
        rw [hClaimed] at hSum
        have hSt2 : stLive63Count st2 = stLive63Count st1 + (if MmapThresholdReq < req then 1 else 0) := by
          unfold stLive63Count; rw [hGs]; simpa [sNew, slotLive63Count] using hSum
        have hLe1 := hSplit.live63Count_le
        rw [hSt2]
        by_cases hReqLe : req ≤ MmapThresholdReq
        · have hNotGt : ¬ MmapThresholdReq < req := by omega
          simp only [fineStepAlloc, hReqLe, hNotGt, ↓reduceIte]; omega
        · have hGt : MmapThresholdReq < req := by omega
          simp only [fineStepAlloc, hReqLe, hGt, ↓reduceIte]; omega
      live63Bytes_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl slotLive63Bytes
        rw [hClaimed] at hSum
        have hSt2 : stLive63Bytes st2 = stLive63Bytes st1 + (if MmapThresholdReq < req then req else 0) := by
          unfold stLive63Bytes; rw [hGs]; simpa [sNew, slotLive63Bytes] using hSum
        have hLe1 := hSplit.live63Bytes_le
        rw [hSt2]
        by_cases hReqLe : req ≤ MmapThresholdReq
        · have hNotGt : ¬ MmapThresholdReq < req := by omega
          simp only [fineStepAlloc, hReqLe, hNotGt, ↓reduceIte]; omega
        · have hGt : MmapThresholdReq < req := by omega
          simp only [fineStepAlloc, hReqLe, hGt, ↓reduceIte]; omega
      straddle63_le   := by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == 63)
          (by simp [hSc]) hIdx sNew hSl (fun _ => slotStraddle63) (fun _ => rfl)
        rw [hClaimed] at hSum
        have hEq : stStraddle63 st2 = stStraddle63 st1 := by
          unfold stStraddle63; rw [hGs]
          have h1 : (if g.sc == 63 then slotStraddle63 .claimed else 0) = 0 := by split <;> rfl
          have h2 : (if g.sc == 63 then slotStraddle63 sNew else 0) = 0 := by
            by_cases h63 : g.sc = 63
            · have hNotLe : ¬ req ≤ MmapThresholdReq := fun hLe => by have := (hSmall hLe).1; omega
              simp [h63, sNew, slotStraddle63, hNotLe]
            · simp [beq_false_of_ne h63]
          rw [h1, h2] at hSum; omega
        rw [hEq]
        exact Nat.le_trans hSplit.straddle63_le hSplit.peaks_le.straddle_le
      overAlign_le    := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl slotOverAlign
        rw [hClaimed] at hSum
        have hEq : stOverAlign st2 = stOverAlign st1 := by
          unfold stOverAlign; rw [hGs]
          have : slotOverAlign .claimed = 0 := rfl
          have : slotOverAlign sNew = 0 := by simp [sNew, slotOverAlign]
          omega
        rw [hEq]
        exact Nat.le_trans hSplit.overAlign_le hSplit.peaks_le.overAlign_le }

theorem map_ite_double_eq (gs : List GroupDesc) {m : BitVec 64} {g1 g2 : GroupDesc}
    (hMeta1 : g1.metaPtr = m) :
    ((gs.map fun h => if h.metaPtr == m then g1 else h).map
      fun h => if h.metaPtr == g1.metaPtr then g2 else h) =
      gs.map fun h => if h.metaPtr == m then g2 else h := by
  rw [List.map_map]
  refine List.map_congr_left fun h _ => ?_
  dsimp only [Function.comp]
  by_cases hEq : h.metaPtr = m
  · simp [hEq, hMeta1]
  · simp [beq_false_of_ne hEq, hMeta1]

theorem fineGroupsInv_enframe_aligned {bgt0 : FineBudget} {align len : Nat} {st1 stFinal : MallocngSt}
    (hSplit : FineSplitInv bgt0 (fineStepAligned align len bgt0) st1)
    (hNd : (st1.groups.map (·.metaPtr)).Nodup)
    (hAlGt : 16 < align)
    {g g' : GroupDesc} (hg : g ∈ st1.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hSmallEff : mallocngAlignedEffSize align len ≤ MmapThresholdReq →
      g.sc < 48 ∧ allowedPhysClass (nomSc (mallocngAlignedEffSize align len)) g.sc = true)
    (hLargeEff : MmapThresholdReq < mallocngAlignedEffSize align len → g.sc = 63)
    {newP : BitVec 64}
    (hMeta : g'.metaPtr = g.metaPtr) (hSc : g'.sc = g.sc)
    (hCnt : g'.cnt = g.cnt) (hMl : g'.maplen = g.maplen)
    (hPar : g'.parentMeta = g.parentMeta)
    (hSl : g'.slots = g.slots.set idx
      (.liveUser newP len (max len MallocngMinBlockCost + (max align 16 - 16))))
    (hMa : stFinal.metaAreas = st1.metaAreas)
    (hGs : stFinal.groups = st1.groups.map fun h => if h.metaPtr == g.metaPtr then g' else h) :
    FineGroupsInv (fineStepAligned align len bgt0) stFinal := by
  have hNotLe16 : ¬ align ≤ 16 := by omega
  have hMaxAlEq : max align 16 - 16 = align - 16 := by omega
  have hEffDef : mallocngAlignedEffSize align len = len + align - 16 := by
    simp [mallocngAlignedEffSize, hNotLe16]
  let effCost' := max len MallocngMinBlockCost + (max align 16 - 16)
  have hOvPos : max len MallocngMinBlockCost < effCost' := by
    dsimp [effCost']; omega
  let sNew := SlotState.liveUser newP len effCost'
  have hLiveEqB1 : (fineStepAligned align len bgt0).liveByNom = (fineStepAlloc len bgt0).liveByNom ∧
      (fineStepAligned align len bgt0).live63Count = (fineStepAlloc len bgt0).live63Count ∧
      (fineStepAligned align len bgt0).live63Bytes = (fineStepAlloc len bgt0).live63Bytes := by
    unfold fineStepAligned
    simp only [hNotLe16, ↓reduceIte]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl⟩
  refine
    { live_inv        := hSplit.peak_inv
      peak_inv        := hSplit.peak_inv
      peaks_le        := FinePeaksLe.refl (fineStepAligned align len bgt0)
      meta_le         := by rw [hMa]; exact hSplit.meta_le
      groups_geom     := groupFineGeom_of_map_ite hNd hSplit.groups_geom hg
        hMeta hSc hCnt (fun _ => hMl) hPar hGs (fun hsc' s hs p' req' eff' hsEq => by
          rw [hSl] at hs
          rcases List.mem_or_eq_of_mem_set hs with hsOld | hNewEq
          · rw [hSc]; exact (hSplit.groups_geom g hg (hSc ▸ hsc')).1 s hsOld p' req' eff' hsEq
          · cases hNewEq.symm.trans hsEq
            have hEffLe : mallocngAlignedEffSize align len ≤ MmapThresholdReq :=
              Classical.byContradiction fun hGt => by have := hLargeEff (by omega); omega
            refine ⟨by omega, fun hLeMax => absurd hLeMax (by omega)⟩)
      class_bounds    := fun sc hsc => by
        rw [stClassBound_eq_of_map_ite hNd hg hSc hCnt hGs sc (fun _ => hMl)]
        exact hSplit.class_bounds sc hsc
      liveNom_le      := fun k hk => by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl (slotLiveNom k)
        rw [hClaimed] at hSum
        have hStF : stLiveByNom stFinal k = stLiveByNom st1 k + slotLiveNom k sNew := by
          unfold stLiveByNom; rw [hGs]; simpa [slotLiveNom] using hSum
        have hLe1 := hSplit.liveNom_le k hk
        rw [hStF, hLiveEqB1.1]
        by_cases hLenLe : len ≤ MmapThresholdReq
        · simp only [fineStepAlloc, hLenLe, ↓reduceIte, vec48Of_getD, hk]
          by_cases hEqK : k = nomSc len
          · subst hEqK
            simp only [sNew, slotLiveNom, hLenLe, decide_true, beq_self_eq_true, Bool.true_and, ↓reduceIte]
            omega
          · have hNe1 : (k == nomSc len) = false := beq_false_of_ne hEqK
            have hNe2 : (nomSc len == k) = false := beq_false_of_ne (Ne.symm hEqK)
            simp only [sNew, slotLiveNom, hLenLe, decide_true, hNe1, hNe2, Bool.true_and,
              Bool.false_eq_true, ↓reduceIte]
            omega
        · simp only [fineStepAlloc, sNew, slotLiveNom, hLenLe, decide_false, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte]
          omega
      reallocCross_le := fun k hk => by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (fun x => decide (x.sc < 48))
          (by simp [hSc]) hIdx sNew hSl (fun x => slotReallocCross x.sc k)
          (fun _ => by simp [hSc])
        rw [hClaimed] at hSum
        have hZeroNew : (if decide (g.sc < 48) then slotReallocCross g.sc k sNew else 0) = 0 := by
          have hNotLeMax : ¬ effCost' ≤ max len MallocngMinBlockCost := by omega
          by_cases hsc48 : g.sc < 48 <;> simp [hsc48, sNew, slotReallocCross, hNotLeMax]
        have hEq : stReallocCrossByNom stFinal k = stReallocCrossByNom st1 k := by
          unfold stReallocCrossByNom; rw [hGs]
          have : (if decide (g.sc < 48) then slotReallocCross g.sc k .claimed else 0) = 0 := by
            split <;> rfl
          rw [this, hZeroNew] at hSum; omega
        rw [hEq]
        exact Nat.le_trans (hSplit.reallocCross_le k hk) (hSplit.peaks_le.realloc_le k hk)
      exc_le          := fun sc hsc => by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == sc)
          (by simp [hSc]) hIdx sNew hSl (fun _ => slotHasOverAlign) (fun _ => rfl)
        rw [hClaimed] at hSum
        have hHas1 : slotHasOverAlign sNew = 1 := by simp [sNew, slotHasOverAlign, hOvPos]
        by_cases hEqSc : g.sc = sc
        · subst hEqSc
          have hEffLe : mallocngAlignedEffSize align len ≤ MmapThresholdReq :=
            Classical.byContradiction fun hGt => by have := hLargeEff (by omega); omega
          have hAl := (hSmallEff hEffLe).2
          have hStF : stOverAlignInClass stFinal g.sc = stOverAlignInClass st1 g.sc + 1 := by
            unfold stOverAlignInClass; rw [hGs]
            simp only [beq_self_eq_true, ↓reduceIte, hHas1] at hSum
            have : slotHasOverAlign .claimed = 0 := rfl
            omega
          have hE0 := hSplit.exc_le g.sc hsc
          have hB1Exc : (fineStepAlloc len bgt0).excByClass = bgt0.excByClass := by
            unfold fineStepAlloc; split <;> rfl
          rw [hStF]
          unfold fineStepAligned
          simp only [hNotLe16, hEffLe, ↓reduceIte, vec48Of_getD, hsc, hAl, hB1Exc]
          omega
        · have hNe : (g.sc == sc) = false := beq_false_of_ne hEqSc
          have hEq : stOverAlignInClass stFinal sc = stOverAlignInClass st1 sc := by
            unfold stOverAlignInClass; rw [hGs]
            simp only [hNe, Bool.false_eq_true, ↓reduceIte] at hSum
            omega
          rw [hEq]
          exact Nat.le_trans (hSplit.exc_le sc hsc) (hSplit.peaks_le.exc_le sc hsc)
      live63Count_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl slotLive63Count
        rw [hClaimed] at hSum
        have hStF : stLive63Count stFinal = stLive63Count st1 + (if MmapThresholdReq < len then 1 else 0) := by
          unfold stLive63Count; rw [hGs]; simpa [sNew, slotLive63Count] using hSum
        have hLe1 := hSplit.live63Count_le
        rw [hStF, hLiveEqB1.2.1]
        by_cases hLenLe : len ≤ MmapThresholdReq
        · have hNotGt : ¬ MmapThresholdReq < len := by omega
          simp only [fineStepAlloc, hLenLe, hNotGt, ↓reduceIte]; omega
        · have hGt : MmapThresholdReq < len := by omega
          simp only [fineStepAlloc, hLenLe, hGt, ↓reduceIte]; omega
      live63Bytes_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl slotLive63Bytes
        rw [hClaimed] at hSum
        have hStF : stLive63Bytes stFinal = stLive63Bytes st1 + (if MmapThresholdReq < len then len else 0) := by
          unfold stLive63Bytes; rw [hGs]; simpa [sNew, slotLive63Bytes] using hSum
        have hLe1 := hSplit.live63Bytes_le
        rw [hStF, hLiveEqB1.2.2]
        by_cases hLenLe : len ≤ MmapThresholdReq
        · have hNotGt : ¬ MmapThresholdReq < len := by omega
          simp only [fineStepAlloc, hLenLe, hNotGt, ↓reduceIte]; omega
        · have hGt : MmapThresholdReq < len := by omega
          simp only [fineStepAlloc, hLenLe, hGt, ↓reduceIte]; omega
      straddle63_le   := by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == 63)
          (by simp [hSc]) hIdx sNew hSl (fun _ => slotStraddle63) (fun _ => rfl)
        rw [hClaimed] at hSum
        have hC0 : (if g.sc == 63 then slotStraddle63 .claimed else 0) = 0 := by split <;> rfl
        rw [hC0] at hSum
        by_cases hStr : g.sc = 63 ∧ len ≤ MmapThresholdReq
        · obtain ⟨h63, hLenLe⟩ := hStr
          have hNotEffLe : ¬ mallocngAlignedEffSize align len ≤ MmapThresholdReq := fun hLe => by
            have := (hSmallEff hLe).1; omega
          have hStF : stStraddle63 stFinal = stStraddle63 st1 + 1 := by
            unfold stStraddle63; rw [hGs]
            simpa [h63, sNew, slotStraddle63, hLenLe] using hSum
          have hB1Str : (fineStepAlloc len bgt0).straddle63Cum = bgt0.straddle63Cum := by
            unfold fineStepAlloc; split <;> rfl
          have hS0 := hSplit.straddle63_le
          rw [hStF]
          unfold fineStepAligned
          simp only [hNotLe16, hNotEffLe, hLenLe, ↓reduceIte, hB1Str]
          omega
        · have hZeroNew : (if g.sc == 63 then slotStraddle63 sNew else 0) = 0 := by
            by_cases h63 : g.sc = 63
            · have hNotLenLe : ¬ len ≤ MmapThresholdReq := fun hL => hStr ⟨h63, hL⟩
              simp [h63, sNew, slotStraddle63, hNotLenLe]
            · simp [beq_false_of_ne h63]
          have hEq : stStraddle63 stFinal = stStraddle63 st1 := by
            unfold stStraddle63; rw [hGs]; rw [hZeroNew] at hSum; omega
          rw [hEq]
          exact Nat.le_trans hSplit.straddle63_le hSplit.peaks_le.straddle_le
      overAlign_le    := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl slotOverAlign
        rw [hClaimed] at hSum
        have hOvNew : slotOverAlign sNew = align - 16 := by
          simp [sNew, slotOverAlign, effCost', hMaxAlEq]
        have hStF : stOverAlign stFinal = stOverAlign st1 + (align - 16) := by
          unfold stOverAlign; rw [hGs]
          have : slotOverAlign .claimed = 0 := rfl
          rw [hOvNew] at hSum; omega
        have hB1Ov : (fineStepAlloc len bgt0).overAlignCum = bgt0.overAlignCum := by
          unfold fineStepAlloc; split <;> rfl
        have hO0 := hSplit.overAlign_le
        rw [hStF]
        unfold fineStepAligned
        simp only [hNotLe16, ↓reduceIte]
        split
        · dsimp only; rw [hB1Ov]; omega
        · split <;> (dsimp only; rw [hB1Ov]; omega) }

private theorem fineStepRealloc_live_eq (al oldSz newSz : Nat) (bgt : FineBudget) :
    (fineStepRealloc al oldSz newSz bgt).liveByNom =
      (fineStepFree oldSz (fineStepAlloc newSz bgt)).liveByNom ∧
    (fineStepRealloc al oldSz newSz bgt).live63Count =
      (fineStepFree oldSz (fineStepAlloc newSz bgt)).live63Count ∧
    (fineStepRealloc al oldSz newSz bgt).live63Bytes =
      (fineStepFree oldSz (fineStepAlloc newSz bgt)).live63Bytes := by
  unfold fineStepRealloc
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem fineGroupsInv_realloc_inplace {bgt0 : FineBudget} {al oldSz oldEff newSz : Nat}
    {st st' : MallocngSt}
    (hFine : FineGroupsInv bgt0 st)
    (hNd : (st.groups.map (·.metaPtr)).Nodup)
    {g g' : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64}
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hSc48 : g.sc < 48)
    (hNewMax : newSz ≤ MmapThresholdReq)
    (hScLe : g.sc ≤ nomSc newSz + 1)
    (hStrideFit : newSz + 4 ≤ g.stride)
    (hMeta : g'.metaPtr = g.metaPtr) (hSc : g'.sc = g.sc)
    (hCnt : g'.cnt = g.cnt) (hMl : g'.maplen = g.maplen)
    (hPar : g'.parentMeta = g.parentMeta)
    (hSl : g'.slots = g.slots.set idx
      (.liveUser p newSz ((oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost)))
    (hMa : st'.metaAreas = st.metaAreas)
    (hGs : st'.groups = st.groups.map fun h => if h.metaPtr == g.metaPtr then g' else h) :
    FineGroupsInv (fineStepRealloc al oldSz newSz bgt0) st' := by
  let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
  let sOld := SlotState.liveUser p oldSz oldEff
  let sNew := SlotState.liveUser p newSz newEff
  have hBInv' : FineBudgetInv (fineStepRealloc al oldSz newSz bgt0) :=
    fineBudgetInv_step (.realloc al oldSz newSz) hFine.live_inv
  have hPeaks : FinePeaksLe bgt0 (fineStepRealloc al oldSz newSz bgt0) :=
    finePeaksLe_step (.realloc al oldSz newSz) bgt0
  have hGeomG := hFine.groups_geom g hg hSc48
  have hOldMax : oldSz ≤ MmapThresholdReq :=
    (hGeomG.1 _ (List.getElem_mem hIdx) p oldSz oldEff hSlot).1
  have hMaxStr : g.stride ≤ maxPossibleStride g.sc :=
    groupStride_le_maxPossibleStride hSc48 hGeomG.2.2
  have hCanHoldNew : canHoldInPlaceRealloc (nomSc newSz) g.sc = true :=
    canHoldInPlaceRealloc_of_fit hSc48 hNewMax hScLe (Nat.le_trans hStrideFit hMaxStr)
  have hLiveEq := fineStepRealloc_live_eq al oldSz newSz bgt0
  have hLiveNomBound : ∀ k < 48,
      stLiveByNom st' k ≤ (fineStepRealloc al oldSz newSz bgt0).liveByNom.getD k 0 := by
    intro k hk
    have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl (slotLiveNom k)
    rw [hSlot] at hSum
    have hSt' : stLiveByNom st' k + slotLiveNom k sOld = stLiveByNom st k + slotLiveNom k sNew := by
      unfold stLiveByNom; rw [hGs]; exact hSum
    have hLe0 := hFine.liveNom_le k hk
    rw [hLiveEq.1]
    simp only [fineStepFree, fineStepAlloc, hOldMax, hNewMax, ↓reduceIte, vec48Of_getD, hk]
    by_cases hEqOld : k = nomSc oldSz
    · subst hEqOld
      by_cases hEqNew : nomSc oldSz = nomSc newSz
      · simp only [sOld, sNew, slotLiveNom, hOldMax, hNewMax, decide_true,
          ← hEqNew, beq_self_eq_true, Bool.true_and, ↓reduceIte] at hSt' ⊢
        omega
      · have hNe1 : (nomSc oldSz == nomSc newSz) = false := beq_false_of_ne hEqNew
        have hNe2 : (nomSc newSz == nomSc oldSz) = false := beq_false_of_ne (Ne.symm hEqNew)
        simp only [sOld, sNew, slotLiveNom, hOldMax, hNewMax, decide_true,
          beq_self_eq_true, hNe1, hNe2, Bool.true_and, Bool.false_eq_true, ↓reduceIte] at hSt' ⊢
        omega
    · have hNeO1 : (k == nomSc oldSz) = false := beq_false_of_ne hEqOld
      have hNeO2 : (nomSc oldSz == k) = false := beq_false_of_ne (Ne.symm hEqOld)
      by_cases hEqNew : k = nomSc newSz
      · subst hEqNew
        simp only [sOld, sNew, slotLiveNom, hOldMax, hNewMax, decide_true,
          beq_self_eq_true, hNeO1, hNeO2, Bool.true_and, Bool.false_eq_true, ↓reduceIte] at hSt' ⊢
        omega
      · have hNeN1 : (k == nomSc newSz) = false := beq_false_of_ne hEqNew
        have hNeN2 : (nomSc newSz == k) = false := beq_false_of_ne (Ne.symm hEqNew)
        simp only [sOld, sNew, slotLiveNom, hOldMax, hNewMax, decide_true,
          hNeO1, hNeO2, hNeN1, hNeN2, Bool.true_and, Bool.false_eq_true, ↓reduceIte] at hSt' ⊢
        omega
  refine
    { live_inv        := hBInv'
      peak_inv        := hBInv'
      peaks_le        := FinePeaksLe.refl _
      meta_le         := by rw [hMa]; exact Nat.le_trans hFine.meta_le (fineMaxMetaAreas_mono hPeaks)
      groups_geom     := groupFineGeom_of_map_ite hNd hFine.groups_geom hg
        hMeta hSc hCnt (fun _ => hMl) hPar hGs (fun hsc' s hs p' req' eff' hsEq => by
          rw [hSl] at hs
          rcases List.mem_or_eq_of_mem_set hs with hsOld | hNewEq
          · rw [hSc]; exact (hFine.groups_geom g hg (hSc ▸ hsc')).1 s hsOld p' req' eff' hsEq
          · cases hNewEq.symm.trans hsEq
            exact ⟨hNewMax, fun _ => hSc ▸ hCanHoldNew⟩)
      class_bounds    := fun sc hsc => by
        rw [stClassBound_eq_of_map_ite hNd hg hSc hCnt hGs sc (fun _ => hMl)]
        exact ClassFineBound.le_trans (hFine.class_bounds sc hsc)
          (fineClassEntry_mono (fun _ hj => peakPhysOfBudget_mono hPeaks hj) hsc)
      liveNom_le      := hLiveNomBound
      reallocCross_le := fun k hk => by
        by_cases hNomNe : nomSc oldSz ≠ nomSc newSz ∧ k = nomSc newSz
        · obtain ⟨hNeNom, rfl⟩ := hNomNe
          have hCrossLeLive := stReallocCrossByNom_le_stLiveByNom st' (nomSc newSz)
          have hLiveLe := hLiveNomBound (nomSc newSz) hk
          rw [hLiveEq.1] at hLiveLe
          unfold fineStepRealloc
          dsimp only
          have hIf : (oldSz ≤ MmapThresholdReq ∧ newSz ≤ MmapThresholdReq ∧ nomSc oldSz ≠ nomSc newSz) = True :=
            propext ⟨fun _ => trivial, fun _ => ⟨hOldMax, hNewMax, hNeNom⟩⟩
          simp only [hIf, ↓reduceIte, vec48Of_getD, hk, beq_self_eq_true]
          exact Nat.le_trans hCrossLeLive (Nat.le_trans hLiveLe (Nat.le_max_right _ _))
        · have hSum := filterGroupSlotSum_map_ite_eq hNd hg (fun x => decide (x.sc < 48))
            (by simp [hSc]) hIdx sNew hSl (fun x => slotReallocCross x.sc k)
            (fun _ => by simp [hSc])
          rw [hSlot] at hSum
          have hSlotLe : slotReallocCross g.sc k sNew ≤ slotReallocCross g.sc k sOld := by
            by_cases hEqK : nomSc newSz = k
            · have hEqNom : nomSc oldSz = nomSc newSz :=
                Classical.byContradiction fun hNe => hNomNe ⟨hNe, hEqK.symm⟩
              have hOvIff : decide (newEff ≤ max newSz MallocngMinBlockCost) =
                  decide (oldEff ≤ max oldSz MallocngMinBlockCost) := by
                dsimp [newEff]; apply decide_eq_decide.mpr; omega
              simp only [sNew, sOld, slotReallocCross, hOvIff, hNewMax, hOldMax, hEqNom]
              exact Nat.le_refl _
            · simp [sNew, slotReallocCross, beq_false_of_ne hEqK]
          have hLeSt : stReallocCrossByNom st' k ≤ stReallocCrossByNom st k := by
            unfold stReallocCrossByNom; rw [hGs]
            simp only [hSc48, decide_true, ↓reduceIte] at hSum
            dsimp only [sOld] at hSlotLe
            omega
          exact Nat.le_trans hLeSt (Nat.le_trans (hFine.reallocCross_le k hk) (hPeaks.realloc_le k hk))
      exc_le          := fun sc hsc => by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == sc)
          (by simp [hSc]) hIdx sNew hSl (fun _ => slotHasOverAlign) (fun _ => rfl)
        rw [hSlot] at hSum
        have hOvEq : slotHasOverAlign sNew = slotHasOverAlign sOld := by
          simp only [sNew, sOld, slotHasOverAlign]
          by_cases h1 : max oldSz MallocngMinBlockCost < oldEff
          · have h2 : max newSz MallocngMinBlockCost < newEff := by dsimp [newEff]; omega
            simp [h1, h2]
          · have h2 : ¬ max newSz MallocngMinBlockCost < newEff := by dsimp [newEff]; omega
            simp [h1, h2]
        have hEq : stOverAlignInClass st' sc = stOverAlignInClass st sc := by
          unfold stOverAlignInClass; rw [hGs]; dsimp only [sOld] at hOvEq; rw [hOvEq] at hSum; omega
        rw [hEq]
        exact Nat.le_trans (hFine.exc_le sc hsc) (hPeaks.exc_le sc hsc)
      live63Count_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl slotLive63Count
        rw [hSlot] at hSum
        have hNotO : ¬ MmapThresholdReq < oldSz := by omega
        have hNotN : ¬ MmapThresholdReq < newSz := by omega
        have hEq : stLive63Count st' = stLive63Count st := by
          unfold stLive63Count; rw [hGs]
          simp only [sNew, slotLive63Count, hNotO, hNotN, ↓reduceIte] at hSum; omega
        rw [hEq, hLiveEq.2.1]
        simp only [fineStepFree, fineStepAlloc, hOldMax, hNewMax, ↓reduceIte]
        exact hFine.live63Count_le
      live63Bytes_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl slotLive63Bytes
        rw [hSlot] at hSum
        have hNotO : ¬ MmapThresholdReq < oldSz := by omega
        have hNotN : ¬ MmapThresholdReq < newSz := by omega
        have hEq : stLive63Bytes st' = stLive63Bytes st := by
          unfold stLive63Bytes; rw [hGs]
          simp only [sNew, slotLive63Bytes, hNotO, hNotN, ↓reduceIte] at hSum; omega
        rw [hEq, hLiveEq.2.2]
        simp only [fineStepFree, fineStepAlloc, hOldMax, hNewMax, ↓reduceIte]
        exact hFine.live63Bytes_le
      straddle63_le   := by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == 63)
          (by simp [hSc]) hIdx sNew hSl (fun _ => slotStraddle63) (fun _ => rfl)
        rw [hSlot] at hSum
        have hNe63 : (g.sc == 63) = false := beq_false_of_ne (by omega)
        have hEq : stStraddle63 st' = stStraddle63 st := by
          unfold stStraddle63; rw [hGs]; simp only [hNe63, Bool.false_eq_true, ↓reduceIte] at hSum; omega
        rw [hEq]
        exact Nat.le_trans hFine.straddle63_le hPeaks.straddle_le
      overAlign_le    := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx sNew hSl slotOverAlign
        rw [hSlot] at hSum
        have hOvEq : slotOverAlign sNew = slotOverAlign sOld := by
          simp only [sNew, sOld, slotOverAlign, newEff]; omega
        have hEq : stOverAlign st' = stOverAlign st := by
          unfold stOverAlign; rw [hGs]; dsimp only [sOld] at hOvEq; rw [hOvEq] at hSum; omega
        rw [hEq]
        exact Nat.le_trans hFine.overAlign_le hPeaks.overAlign_le }

theorem fineGroupsInv_realloc_mremap63 {bgt0 : FineBudget} {al oldSz oldEff newSz : Nat}
    {st st' : MallocngSt}
    (hFine : FineGroupsInv bgt0 st)
    (hNd : (st.groups.map (·.metaPtr)).Nodup)
    {g g' : GroupDesc} (hg : g ∈ st.groups) (hSlotsLen1 : g.slots.length = 1)
    {p newP : BitVec 64}
    (hSlot0 : g.slots[0]'(by omega) = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    (hNewLo : MmapThresholdReq < newSz)
    (hMeta : g'.metaPtr = g.metaPtr) (hSc : g'.sc = g.sc)
    (hCnt : g'.cnt = g.cnt) (hPar : g'.parentMeta = g.parentMeta)
    (hSl : g'.slots = [.liveUser newP newSz
      ((oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost)])
    (hMa : st'.metaAreas = st.metaAreas)
    (hGs : st'.groups = st.groups.map fun h => if h.metaPtr == g.metaPtr then g' else h) :
    FineGroupsInv (fineStepRealloc al oldSz newSz bgt0) st' := by
  let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
  let sOld := SlotState.liveUser p oldSz oldEff
  let sNew := SlotState.liveUser newP newSz newEff
  have hIdx0 : 0 < g.slots.length := by omega
  have hSlSet : g'.slots = g.slots.set 0 sNew := by
    rw [hSl]
    cases hs : g.slots with
    | nil => simp [hs] at hSlotsLen1
    | cons hd tl =>
      simp [hs] at hSlotsLen1
      rw [hSlotsLen1]; rfl
  have hBInv' : FineBudgetInv (fineStepRealloc al oldSz newSz bgt0) :=
    fineBudgetInv_step (.realloc al oldSz newSz) hFine.live_inv
  have hPeaks : FinePeaksLe bgt0 (fineStepRealloc al oldSz newSz bgt0) :=
    finePeaksLe_step (.realloc al oldSz newSz) bgt0
  have hLiveEq := fineStepRealloc_live_eq al oldSz newSz bgt0
  have hNotNewLe : ¬ newSz ≤ MmapThresholdReq := by omega
  refine
    { live_inv        := hBInv'
      peak_inv        := hBInv'
      peaks_le        := FinePeaksLe.refl _
      meta_le         := by rw [hMa]; exact Nat.le_trans hFine.meta_le (fineMaxMetaAreas_mono hPeaks)
      groups_geom     := groupFineGeom_of_map_ite hNd hFine.groups_geom hg
        hMeta hSc hCnt (fun h48 => by omega) hPar hGs (fun hsc' => by omega)
      class_bounds    := fun sc hsc => by
        rw [stClassBound_eq_of_map_ite hNd hg hSc hCnt hGs sc (fun hEq => by omega)]
        exact ClassFineBound.le_trans (hFine.class_bounds sc hsc)
          (fineClassEntry_mono (fun _ hj => peakPhysOfBudget_mono hPeaks hj) hsc)
      liveNom_le      := fun k hk => by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx0 sNew hSlSet (slotLiveNom k)
        rw [hSlot0] at hSum
        have hZeroNew : slotLiveNom k sNew = 0 := by
          simp [sNew, slotLiveNom, hNotNewLe]
        have hSt' : stLiveByNom st' k + slotLiveNom k sOld = stLiveByNom st k := by
          unfold stLiveByNom; rw [hGs]; rw [hZeroNew] at hSum; omega
        have hLe0 := hFine.liveNom_le k hk
        rw [hLiveEq.1]
        simp only [fineStepAlloc, hNotNewLe, ↓reduceIte]
        by_cases hOldLe : oldSz ≤ MmapThresholdReq
        · simp only [fineStepFree, hOldLe, ↓reduceIte, vec48Of_getD, hk]
          by_cases hEqO : k = nomSc oldSz
          · subst hEqO
            simp only [sOld, slotLiveNom, hOldLe, decide_true, beq_self_eq_true, Bool.true_and, ↓reduceIte] at hSt' ⊢
            omega
          · have hNe1 : (k == nomSc oldSz) = false := beq_false_of_ne hEqO
            have hNe2 : (nomSc oldSz == k) = false := beq_false_of_ne (Ne.symm hEqO)
            simp only [sOld, slotLiveNom, hOldLe, decide_true, hNe1, hNe2, Bool.true_and,
              Bool.false_eq_true, ↓reduceIte] at hSt' ⊢
            omega
        · simp only [fineStepFree, hOldLe, ↓reduceIte]; omega
      reallocCross_le := fun k hk => by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (fun x => decide (x.sc < 48))
          (by simp [hSc]) hIdx0 sNew hSlSet (fun x => slotReallocCross x.sc k)
          (fun _ => by simp [hSc])
        have hNot48 : ¬ g.sc < 48 := by omega
        have hEq : stReallocCrossByNom st' k = stReallocCrossByNom st k := by
          unfold stReallocCrossByNom; rw [hGs]; simp only [hNot48, decide_false, Bool.false_eq_true, ↓reduceIte] at hSum; omega
        rw [hEq]
        exact Nat.le_trans (hFine.reallocCross_le k hk) (hPeaks.realloc_le k hk)
      exc_le          := fun sc hsc => by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == sc)
          (by simp [hSc]) hIdx0 sNew hSlSet (fun _ => slotHasOverAlign) (fun _ => rfl)
        have hNe : (g.sc == sc) = false := beq_false_of_ne (by omega)
        have hEq : stOverAlignInClass st' sc = stOverAlignInClass st sc := by
          unfold stOverAlignInClass; rw [hGs]; simp only [hNe, Bool.false_eq_true, ↓reduceIte] at hSum; omega
        rw [hEq]
        exact Nat.le_trans (hFine.exc_le sc hsc) (hPeaks.exc_le sc hsc)
      live63Count_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx0 sNew hSlSet slotLive63Count
        rw [hSlot0] at hSum
        have hOneNew : slotLive63Count sNew = 1 := by simp [sNew, slotLive63Count, hNewLo]
        have hSt' : stLive63Count st' + slotLive63Count sOld = stLive63Count st + 1 := by
          unfold stLive63Count; rw [hGs]; rw [hOneNew] at hSum; exact hSum
        have hLe0 := hFine.live63Count_le
        rw [hLiveEq.2.1]
        simp only [fineStepAlloc, hNotNewLe, ↓reduceIte]
        by_cases hOldLe : oldSz ≤ MmapThresholdReq
        · have hNotO : ¬ MmapThresholdReq < oldSz := by omega
          simp only [fineStepFree, sOld, slotLive63Count, hOldLe, hNotO, ↓reduceIte] at hSt' ⊢; omega
        · have hGtO : MmapThresholdReq < oldSz := by omega
          simp only [fineStepFree, sOld, slotLive63Count, hOldLe, hGtO, ↓reduceIte] at hSt' ⊢; omega
      live63Bytes_le  := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx0 sNew hSlSet slotLive63Bytes
        rw [hSlot0] at hSum
        have hNewB : slotLive63Bytes sNew = newSz := by simp [sNew, slotLive63Bytes, hNewLo]
        have hSt' : stLive63Bytes st' + slotLive63Bytes sOld = stLive63Bytes st + newSz := by
          unfold stLive63Bytes; rw [hGs]; rw [hNewB] at hSum; exact hSum
        have hLe0 := hFine.live63Bytes_le
        rw [hLiveEq.2.2]
        simp only [fineStepAlloc, hNotNewLe, ↓reduceIte]
        by_cases hOldLe : oldSz ≤ MmapThresholdReq
        · have hNotO : ¬ MmapThresholdReq < oldSz := by omega
          simp only [fineStepFree, sOld, slotLive63Bytes, hOldLe, hNotO, ↓reduceIte] at hSt' ⊢; omega
        · have hGtO : MmapThresholdReq < oldSz := by omega
          simp only [fineStepFree, sOld, slotLive63Bytes, hOldLe, hGtO, ↓reduceIte] at hSt' ⊢; omega
      straddle63_le   := by
        have hSum := filterGroupSlotSum_map_ite_eq hNd hg (·.sc == 63)
          (by simp [hSc]) hIdx0 sNew hSlSet (fun _ => slotStraddle63) (fun _ => rfl)
        rw [hSlot0] at hSum
        have hZeroNew : slotStraddle63 sNew = 0 := by simp [sNew, slotStraddle63, hNotNewLe]
        have hLe : stStraddle63 st' ≤ stStraddle63 st := by
          unfold stStraddle63; rw [hGs]; simp only [hSc63, beq_self_eq_true, ↓reduceIte, hZeroNew] at hSum; omega
        exact Nat.le_trans hLe (Nat.le_trans hFine.straddle63_le hPeaks.straddle_le)
      overAlign_le    := by
        have hSum := groupSlotSum_map_ite_eq hNd hg hIdx0 sNew hSlSet slotOverAlign
        rw [hSlot0] at hSum
        have hOvEq : slotOverAlign sNew = slotOverAlign sOld := by
          simp only [sNew, sOld, slotOverAlign, newEff]; omega
        have hEq : stOverAlign st' = stOverAlign st := by
          unfold stOverAlign; rw [hGs]; dsimp only [sOld] at hOvEq; rw [hOvEq] at hSum; omega
        rw [hEq]
        exact Nat.le_trans hFine.overAlign_le hPeaks.overAlign_le }

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine

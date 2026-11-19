/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.RootLen

/-!
# Per-Size-Class Fine Geometry Tables (`VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Tables`)

- **Layer & Role**: `Role::Proof` (untrusted). Pure, kernel-derived per-size-class constants and
  bottom-up group/byte bound recurrences for `mallocng`'s `alloc_group` / `alloc_slot` hierarchy.
- **Zero hand-typed magic tables**: every per-class bound (`steadyCnt`, `steadyParent`,
  `maxSmallNestedGroups`, `canSmallNestIn`, `reachableRootPairs`, `cntMinRoot`, `maxRootBytes`,
  `ceilRootPerSlot`) is computed directly from `SizeClasses` (`sizeClass`, `slotStride`,
  `nominalSlotCap`, `sizeToClassUnits`) and `Cost.GroupTable` (`cntSel`, `reduceCnt`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
  VerifiedLibraries.Mallocng.Proofs.Cost

/-! ## 1. Nominal Size-Class & Coarse-Bump / In-Place `realloc` Predicates -/

/-- Largest user request (`131051` B) routed through `size_to_class` (`sc < 48`) rather than
    individual `sc = 63` `mmap`. -/
def MmapThresholdReq : Nat := 131051

/-- Nominal size class (`0 .. 47` for `req ≤ 131051`) computed by `size_to_class`. -/
def nomSc (req : Nat) : Nat :=
  sizeToClassUnits ((req + 3) / 16)

theorem nomSc_spec {req : Nat} (h : req ≤ MmapThresholdReq) :
    nomSc req < 48 ∧
    req ≤ nominalSlotCap (nomSc req) ∧
    (nomSc req = 0 ∨ nominalSlotCap (nomSc req - 1) < req) :=
  sizeToClass_spec h

theorem nomSc_lt_48 {req : Nat} (h : req ≤ MmapThresholdReq) : nomSc req < 48 :=
  (nomSc_spec h).1

/-- Even classes `4 ≤ sc ≤ 30`, `sc ≠ 6` eligible for `__libc_malloc_impl`'s `sc | 1` coarse bump. -/
def coarseBumpable (sc : Nat) : Bool :=
  decide (4 ≤ sc ∧ sc ≤ 31 ∧ sc ≠ 6 ∧ sc % 2 = 0)

/-- Physical slab classes (`sc < 48`) into which `__libc_malloc_impl` can place an allocation of
    nominal class `nom`: either `nom` itself or `nom + 1` when `coarseBumpable nom`. -/
def allowedPhysClass (nom sc : Nat) : Bool :=
  decide (sc < 48 ∧ (sc = nom ∨ (coarseBumpable nom = true ∧ sc = nom + 1)))

/-- Minimum request size passed to `alloc_slot(sc, req)` at any outer or recursive call site. -/
def allocSlotReqLo (sc : Nat) : Nat :=
  if sc = 0 then 0
  else if coarseBumpable (sc - 1) then nominalSlotCap (sc - 2) + 1
  else nominalSlotCap (sc - 1) + 1

/-- Largest `g.stride` achievable by any group of slab class `sc < 48` (`cnt = 1` root groups in
    `sc ≥ 24` may stretch `g.stride` to `len - 16 ≤ pageAlignUp (slotStride sc + 16) - 16`). -/
def maxPossibleStride (sc : Nat) : Nat :=
  if sc < 24 then slotStride sc else pageAlignUp (slotStride sc + 16) - 16

/-- Minimum user request size with `nomSc req = nomNew` (`0` for `nomNew = 0`, else
    `nominalSlotCap (nomNew - 1) + 1`). -/
def minReqOfNom (nomNew : Nat) : Nat :=
  if nomNew = 0 then 0 else nominalSlotCap (nomNew - 1) + 1

/-- Physical slab classes `sc < 48` that can absorb an in-place Stage-2 `realloc` to nominal class
    `nomNew` (`g.sc ≤ nomNew + 1` and `newSz + 4 ≤ g.stride ≤ maxPossibleStride sc`). -/
def canHoldInPlaceRealloc (nomNew sc : Nat) : Bool :=
  decide (sc < 48 ∧ sc ≤ nomNew + 1 ∧ minReqOfNom nomNew + 4 ≤ maxPossibleStride sc)

theorem canHoldInPlaceRealloc_of_fit {sc newSz : Nat}
    (hsc : sc < 48) (hNew : newSz ≤ MmapThresholdReq)
    (hLe : sc ≤ nomSc newSz + 1) (hFit : newSz + 4 ≤ maxPossibleStride sc) :
    canHoldInPlaceRealloc (nomSc newSz) sc = true := by
  unfold canHoldInPlaceRealloc minReqOfNom
  have hSpec := (nomSc_spec hNew).2.2
  simp only [decide_eq_true_eq]
  refine ⟨hsc, hLe, ?_⟩
  rcases hSpec with h0 | hgt
  · simp [h0]; omega
  · split <;> omega

/-! ## 2. Steady vs Small Nested Group Counts & Parent Relations -/

/-- Saturated count `cntSel sc 128` reached for all usage `u ≥ 128`. -/
def steadyCnt (sc : Nat) : Nat :=
  cntSel sc 128

theorem cntSel_eq_steadyCnt_of_ge {sc u : Nat} (hu : 128 ≤ u) :
    cntSel sc u = steadyCnt sc := by
  rw [cntSel_min, Nat.min_eq_right hu]; rfl

/-- Classes `sc < 48` whose saturated count `steadyCnt sc` still takes the nested path
    (`steadyCnt sc * slotStride sc + 16 ≤ 2048`). -/
def isSteadyNestedClass (sc : Nat) : Bool :=
  decide (sc < 48 ∧ steadyCnt sc * slotStride sc + 16 ≤ 2048)

/-- Exact parent class `sizeToClassUnits (steadyCnt sc * sizeClass sc)` of a steady-nested group. -/
def steadyParent (sc : Nat) : Nat :=
  sizeToClassUnits (steadyCnt sc * sizeClass sc)

/-- Non-steady nested counts reachable at low usage `u < 128`. -/
def isSmallNestedCnt (sc cnt : Nat) : Bool :=
  decide (sc < 48 ∧ ¬ (isSteadyNestedClass sc = true ∧ cnt = steadyCnt sc)) &&
    ((List.range 128).any fun u =>
      decide (cntSel sc u = cnt ∧ cnt * slotStride sc + 16 ≤ 2048))

def hasSmallNested (sc : Nat) : Bool :=
  (List.range 33).any (isSmallNestedCnt sc)

def cntMinSmallNested (sc : Nat) : Nat :=
  ((List.range 33).filter (isSmallNestedCnt sc)).foldr min 32

/-- Maximum small-nested groups of class `sc` (`u ≤ 127` at creation, each existing small-nested
    group contributes `≥ cntMinSmallNested sc` slots to `u`). -/
def maxSmallNestedGroups (sc : Nat) : Nat :=
  if hasSmallNested sc then 1 + 127 / cntMinSmallNested sc else 0

/-- Whether a small-nested group of class `csc` can nest inside a parent slot of class `psc`. -/
def canSmallNestIn (csc psc : Nat) : Bool :=
  decide (csc < psc ∧ psc ≤ 24) &&
    ((List.range 33).any fun cnt =>
      isSmallNestedCnt csc cnt && decide (sizeToClassUnits (cnt * sizeClass csc) = psc))

private def checkNestedProps : Bool :=
  (List.range 48).all fun sc =>
    (1 ≤ steadyCnt sc) &&
    (if isSteadyNestedClass sc then
      (2 ≤ steadyCnt sc) && (sc < steadyParent sc) && (steadyParent sc < 48)
     else true) &&
    (if hasSmallNested sc then 2 ≤ cntMinSmallNested sc else true) &&
    ((List.range 33).all fun cnt =>
      if isSmallNestedCnt sc cnt then
        let psc := sizeToClassUnits (cnt * sizeClass sc)
        (2 ≤ cnt) && (cntMinSmallNested sc ≤ cnt) && (sc < psc) && (psc ≤ 24)
      else true) &&
    ((List.range 48).all fun psc =>
      if canSmallNestIn sc psc then sc < psc else true)

private theorem checkNestedProps_true : checkNestedProps = true := by
  decide +kernel

theorem steadyCnt_pos {sc : Nat} (hsc : sc < 48) : 1 ≤ steadyCnt sc := by
  have h := List.all_eq_true.mp checkNestedProps_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem steadyParent_props {sc : Nat} (hsc : sc < 48) (hst : isSteadyNestedClass sc = true) :
    2 ≤ steadyCnt sc ∧ sc < steadyParent sc ∧ steadyParent sc < 48 := by
  have h := List.all_eq_true.mp checkNestedProps_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true] at h
  have h2 := h.1.1.1.2
  simp only [hst, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h2
  exact ⟨h2.1.1, h2.1.2, h2.2⟩

theorem cntMinSmallNested_ge_two {sc : Nat} (hsc : sc < 48) (hsm : hasSmallNested sc = true) :
    2 ≤ cntMinSmallNested sc := by
  have h := List.all_eq_true.mp checkNestedProps_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true] at h
  have h3 := h.1.1.2
  simpa only [hsm, ↓reduceIte, decide_eq_true_eq] using h3

theorem smallNestedCnt_props {sc cnt : Nat} (hsc : sc < 48) (hcnt : cnt ≤ 32)
    (hsm : isSmallNestedCnt sc cnt = true) :
    hasSmallNested sc = true ∧
    2 ≤ cnt ∧
    cntMinSmallNested sc ≤ cnt ∧
    sc < sizeToClassUnits (cnt * sizeClass sc) ∧
    sizeToClassUnits (cnt * sizeClass sc) < 48 ∧
    canSmallNestIn sc (sizeToClassUnits (cnt * sizeClass sc)) = true := by
  have hHas : hasSmallNested sc = true :=
    List.any_eq_true.mpr ⟨cnt, List.mem_range.mpr (by omega), hsm⟩
  have h := List.all_eq_true.mp checkNestedProps_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true] at h
  have h4 := List.all_eq_true.mp h.1.2 cnt (List.mem_range.mpr (by omega))
  simp only [hsm, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h4
  have hCan : canSmallNestIn sc (sizeToClassUnits (cnt * sizeClass sc)) = true := by
    unfold canSmallNestIn
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true ⟨h4.1.2, h4.2⟩,
      List.any_eq_true.mpr ⟨cnt, List.mem_range.mpr (by omega), by simp [hsm]⟩⟩
  exact ⟨hHas, h4.1.1.1, h4.1.1.2, h4.1.2, by omega, hCan⟩

theorem smallNested_of_cntSel {sc u cnt : Nat} (hsc : sc < 48)
    (hcnt : cnt = cntSel sc u) (hnest : cnt * slotStride sc + 16 ≤ 2048)
    (hnotSt : ¬ (isSteadyNestedClass sc = true ∧ cnt = steadyCnt sc)) :
    u < 128 ∧ cnt ≤ 32 ∧ isSmallNestedCnt sc cnt = true := by
  have huLt : u < 128 := by
    apply Classical.byContradiction
    intro hge
    have hEq := cntSel_eq_steadyCnt_of_ge (sc := sc) (u := u) (by omega)
    have hCntSt : cnt = steadyCnt sc := hcnt.trans hEq
    have hIsSt : isSteadyNestedClass sc = true := by
      unfold isSteadyNestedClass
      rw [decide_eq_true_eq]
      exact ⟨hsc, hCntSt ▸ hnest⟩
    exact hnotSt ⟨hIsSt, hCntSt⟩
  have hCntLe32 : cnt ≤ 32 := by
    have hAll : ((List.range 48).all fun s => (List.range 128).all fun v =>
        decide (cntSel s v ≤ 32)) = true := by decide +kernel
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp hAll sc (List.mem_range.mpr hsc))
      u (List.mem_range.mpr huLt)
    rw [decide_eq_true_eq] at h1
    omega
  refine ⟨huLt, hCntLe32, ?_⟩
  unfold isSmallNestedCnt
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true ⟨hsc, hnotSt⟩, List.any_eq_true.mpr ⟨u, List.mem_range.mpr huLt, ?_⟩⟩
  exact decide_eq_true ⟨hcnt.symm, hnest⟩

/-! ## 3. Reachable Root `(cnt, bytes)` Pairs of `alloc_group` -/

/-- Candidate `(cnt, bytes)` pairs reachable on the root `mmap` path of `alloc_group` for `sc < 48`
    under `allocSlotReqLo sc ≤ req ≤ nominalSlotCap sc`. -/
def reachableRootPairs (sc : Nat) : List (Nat × Nat) :=
  if sc < 48 then
    let multiPairs : List (Nat × Nat) :=
      (List.range 129).flatMap fun u =>
        let c' := cntSel sc u
        if 2048 < c' * slotStride sc + 16 then
          let r := reduceCnt sc c'
          [(c', pageAlignUp (c' * slotStride sc + 16)),
           (r, pageAlignUp (r * slotStride sc + 16))]
        else []
    let hasLowCnt : Bool :=
      (List.range 129).any fun u =>
        let c' := cntSel sc u
        decide (2048 < c' * slotStride sc + 16) &&
          (decide (c' ≤ 7) || decide (reduceCnt sc c' ≤ 7))
    let cnt1Pairs : List (Nat × Nat) :=
      if hasLowCnt then
        (if pageAlignUp (allocSlotReqLo sc + 20) < slotStride sc + 16 then
          let minP := pageAlignUp (allocSlotReqLo sc + 20) / 4096
          let maxP := pageAlignUp (slotStride sc + 16) / 4096
          ((List.range (maxP + 1)).filter (fun k => decide (1 ≤ k ∧ minP ≤ k))).map
            fun k => (1, 4096 * k)
         else []) ++
        (if 16384 ≤ pageAlignUp (nominalSlotCap sc + 20) then
          [(1, pageAlignUp (slotStride sc + 16))]
         else [])
      else []
    multiPairs ++ cnt1Pairs
  else []

def hasRootPair (sc : Nat) : Bool :=
  !(reachableRootPairs sc).isEmpty

def cntMinRoot (sc : Nat) : Nat :=
  ((reachableRootPairs sc).map Prod.fst).foldr min 32

def maxRootBytes (sc : Nat) : Nat :=
  ((reachableRootPairs sc).map Prod.snd).foldr max 0

def ceilRootPerSlot (sc : Nat) : Nat :=
  ((reachableRootPairs sc).map fun p => (p.2 + p.1 - 1) / p.1).foldr max 0

private def checkRootPairsProps : Bool :=
  (List.range 48).all fun sc =>
    (if hasRootPair sc then 1 ≤ cntMinRoot sc else true) &&
    ((reachableRootPairs sc).all fun p =>
      (1 ≤ p.1) &&
      (p.1 ≤ 32) &&
      (cntMinRoot sc ≤ p.1) &&
      (4096 ≤ p.2) &&
      (p.2 ≤ maxRootBytes sc) &&
      (p.2 ≤ ceilRootPerSlot sc * p.1) &&
      (p.2 ≤ 1048576))

private theorem checkRootPairsProps_true : checkRootPairsProps = true := by
  decide +kernel

theorem cntMinRoot_pos {sc : Nat} (hsc : sc < 48) (hr : hasRootPair sc = true) :
    1 ≤ cntMinRoot sc := by
  have h := List.all_eq_true.mp checkRootPairsProps_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true] at h
  simpa only [hr, ↓reduceIte, decide_eq_true_eq] using h.1

theorem reachableRootPairs_bounds {sc cnt bytes : Nat} (hsc : sc < 48)
    (hmem : (cnt, bytes) ∈ reachableRootPairs sc) :
    hasRootPair sc = true ∧
    1 ≤ cnt ∧ cnt ≤ 32 ∧ cntMinRoot sc ≤ cnt ∧
    4096 ≤ bytes ∧ bytes ≤ maxRootBytes sc ∧
    bytes ≤ ceilRootPerSlot sc * cnt ∧ bytes ≤ 1048576 := by
  have hHas : hasRootPair sc = true := by
    unfold hasRootPair
    cases hL : reachableRootPairs sc with
    | nil => rw [hL] at hmem; cases hmem
    | cons _ _ => rfl
  have h := List.all_eq_true.mp checkRootPairsProps_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true] at h
  have hp := List.all_eq_true.mp h.2 (cnt, bytes) hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨hHas, hp.1.1.1.1.1.1, hp.1.1.1.1.1.2, hp.1.1.1.1.2, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩

private theorem pageAlignUp_mono_fine {a b : Nat} (h : a ≤ b) : pageAlignUp a ≤ pageAlignUp b := by
  unfold pageAlignUp PAGE_SIZE
  exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))

/-- Completeness of `reachableRootPairs`: every `(cnt_f, len)` selected on the root `mmap` path of
    `alloc_group` (under `allocSlotReqLo sc ≤ req ≤ nominalSlotCap sc`) belongs to
    `reachableRootPairs sc`. -/
theorem mem_reachableRootPairs_of_rootSelect {sc u c' c cnt_f req len : Nat}
    (hsc : sc < 48)
    (hc' : c' = cntSel sc u)
    (hroot : 2048 < c' * slotStride sc + 16)
    (hc : c = c' ∨ c = reduceCnt sc c')
    (hReqLo : allocSlotReqLo sc ≤ req)
    (hReqHi : req ≤ nominalSlotCap sc)
    (hsel :
      (cnt_f = c ∧ len = pageAlignUp (c * slotStride sc + 16)) ∨
      (cnt_f = 1 ∧ c ≤ 7 ∧ len = pageAlignUp (req + 20) ∧
        (len < slotStride sc + 16 ∨ 16384 ≤ len))) :
    (cnt_f, len) ∈ reachableRootPairs sc := by
  let u0 := min u 128
  have hu0Mem : u0 ∈ List.range 129 := List.mem_range.mpr (by omega)
  have hc'0 : c' = cntSel sc u0 := hc'.trans (cntSel_min sc u)
  unfold reachableRootPairs
  simp only [hsc, ↓reduceIte]
  rcases hsel with ⟨rfl, rfl⟩ | ⟨rfl, hc7, rfl, hbr⟩
  · apply List.mem_append_left
    refine List.mem_flatMap.mpr ⟨u0, hu0Mem, ?_⟩
    simp only [← hc'0, hroot, ↓reduceIte]
    rcases hc with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  · apply List.mem_append_right
    have hHasLow :
        ((List.range 129).any fun v =>
          let cv := cntSel sc v
          decide (2048 < cv * slotStride sc + 16) &&
            (decide (cv ≤ 7) || decide (reduceCnt sc cv ≤ 7))) = true := by
      refine List.any_eq_true.mpr ⟨u0, hu0Mem, ?_⟩
      simp only [← hc'0, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      refine ⟨hroot, ?_⟩
      rcases hc with rfl | rfl
      · exact Or.inl hc7
      · exact Or.inr hc7
    simp only [hHasLow, ↓reduceIte]
    have hCapPlus20 : nominalSlotCap sc + 20 = slotStride sc + 16 := by
      have hB := (sizeClass_bounds hsc).1
      unfold nominalSlotCap slotStride; omega
    have hLenLo : pageAlignUp (allocSlotReqLo sc + 20) ≤ pageAlignUp (req + 20) :=
      pageAlignUp_mono_fine (by omega)
    have hLenHi : pageAlignUp (req + 20) ≤ pageAlignUp (slotStride sc + 16) :=
      pageAlignUp_mono_fine (by omega)
    by_cases hLtStr : pageAlignUp (req + 20) < slotStride sc + 16
    · apply List.mem_append_left
      have hCond1 : pageAlignUp (allocSlotReqLo sc + 20) < slotStride sc + 16 := by omega
      simp only [hCond1, ↓reduceIte]
      let k := (req + 20 + 4095) / 4096
      have hkEq : pageAlignUp (req + 20) = 4096 * k := by
        unfold pageAlignUp PAGE_SIZE; omega
      have hk1 : 1 ≤ k := by omega
      have hMinP : pageAlignUp (allocSlotReqLo sc + 20) / 4096 ≤ k := by
        unfold pageAlignUp PAGE_SIZE; omega
      have hMaxP : k ≤ pageAlignUp (slotStride sc + 16) / 4096 := by
        unfold pageAlignUp PAGE_SIZE; omega
      refine List.mem_map.mpr ⟨k, ?_, by rw [← hkEq]⟩
      exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), decide_eq_true ⟨hk1, hMinP⟩⟩
    · have hGe16k : 16384 ≤ pageAlignUp (req + 20) := by
        rcases hbr with h | h
        · exact absurd h hLtStr
        · exact h
      apply List.mem_append_right
      have hCond2 : 16384 ≤ pageAlignUp (nominalSlotCap sc + 20) := by
        rw [hCapPlus20]; omega
      simp only [hCond2, ↓reduceIte]
      have hEqTop : pageAlignUp (req + 20) = pageAlignUp (slotStride sc + 16) := by
        unfold pageAlignUp PAGE_SIZE at hLtStr hLenHi ⊢
        omega
      simp [hEqTop]

/-! ## 4. Bottom-Up Per-Class Group & Byte Bound Recurrence -/

/-- Per-class `(smallNestedGroups, steadyNestedGroups, rootGroups, rootBytes)` bound tuple. -/
structure ClassFineBound where
  gsn : Nat
  gst : Nat
  gr  : Nat
  rb  : Nat
  deriving DecidableEq, Repr, Inhabited

def ClassFineBound.zero : ClassFineBound := ⟨0, 0, 0, 0⟩

def ClassFineBound.le (a b : ClassFineBound) : Prop :=
  a.gsn ≤ b.gsn ∧ a.gst ≤ b.gst ∧ a.gr ≤ b.gr ∧ a.rb ≤ b.rb

theorem ClassFineBound.le_refl (a : ClassFineBound) : a.le a :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem ClassFineBound.le_trans {a b c : ClassFineBound} (h1 : a.le b) (h2 : b.le c) : a.le c :=
  ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2.1 h2.2.1,
   Nat.le_trans h1.2.2.1 h2.2.2.1, Nat.le_trans h1.2.2.2 h2.2.2.2⟩

/-- Child nested groups from classes `csc < sc` that occupy parent slots in class `sc`. -/
def childNestedFrom (acc : List ClassFineBound) (sc : Nat) : Nat :=
  ((List.range sc).map fun csc =>
    let e := acc.getD csc ClassFineBound.zero
    (if canSmallNestIn csc sc then e.gsn else 0) +
    (if steadyParent csc == sc && isSteadyNestedClass csc then e.gst else 0)).sum

def fineClassStepOfOcc (sc occ : Nat) : ClassFineBound :=
  if occ == 0 then ClassFineBound.zero
  else
    { gsn := maxSmallNestedGroups sc
      gst := if isSteadyNestedClass sc then 1 + occ / steadyCnt sc else 0
      gr  := if hasRootPair sc then 1 + occ / cntMinRoot sc else 0
      rb  := if hasRootPair sc then maxRootBytes sc + ceilRootPerSlot sc * occ else 0 }

/-- Single step of the bottom-up class bound recurrence at class `sc`. -/
def fineClassStep (peakPhys : Nat → Nat) (acc : List ClassFineBound) (sc : Nat) : ClassFineBound :=
  fineClassStepOfOcc sc (peakPhys sc + childNestedFrom acc sc)

/-- Single-pass linear traversal that computes `childNestedFrom` while appending the new class entry
    (avoids `2^n` term duplication in call-by-name WHNF). -/
def appendClassStep (peakPhys : Nat → Nat) (sc : Nat) :
    Nat → Nat → List ClassFineBound → List ClassFineBound
  | _, childAcc, [] => [fineClassStepOfOcc sc (peakPhys sc + childAcc)]
  | csc, childAcc, e :: tl =>
    let add :=
      (if canSmallNestIn csc sc then e.gsn else 0) +
      (if steadyParent csc == sc && isSteadyNestedClass csc then e.gst else 0)
    e :: appendClassStep peakPhys sc (csc + 1) (childAcc + add) tl

/-- Prefix `0 .. n - 1` of the bottom-up per-class bounds. -/
def fineBoundsUpTo (peakPhys : Nat → Nat) : Nat → List ClassFineBound
  | 0 => []
  | n + 1 => appendClassStep peakPhys n 0 0 (fineBoundsUpTo peakPhys n)

private def childNestedSlice (sc : Nat) : Nat → List ClassFineBound → Nat
  | _, [] => 0
  | csc, e :: tl =>
    ((if canSmallNestIn csc sc then e.gsn else 0) +
      (if steadyParent csc == sc && isSteadyNestedClass csc then e.gst else 0)) +
    childNestedSlice sc (csc + 1) tl

private theorem appendClassStep_eq_slice (peakPhys : Nat → Nat) (sc : Nat) :
    ∀ (xs : List ClassFineBound) (csc childAcc : Nat),
      appendClassStep peakPhys sc csc childAcc xs =
        xs ++ [fineClassStepOfOcc sc (peakPhys sc + (childAcc + childNestedSlice sc csc xs))]
  | [], _, childAcc => by simp [appendClassStep, childNestedSlice]
  | e :: tl, csc, childAcc => by
    simp only [appendClassStep, childNestedSlice, List.cons_append]
    rw [appendClassStep_eq_slice peakPhys sc tl (csc + 1), Nat.add_assoc childAcc]

private theorem appendClassStep_length (peakPhys : Nat → Nat) (sc : Nat) :
    ∀ (xs : List ClassFineBound) (csc childAcc : Nat),
      (appendClassStep peakPhys sc csc childAcc xs).length = xs.length + 1
  | [], _, _ => rfl
  | _ :: tl, csc, childAcc => by
    simp [appendClassStep, appendClassStep_length peakPhys sc tl (csc + 1)]

private theorem childNestedSlice_eq_range (sc : Nat) :
    ∀ (xs : List ClassFineBound) (csc : Nat),
      childNestedSlice sc csc xs =
        ((List.range xs.length).map fun i =>
          let e := xs.getD i ClassFineBound.zero
          (if canSmallNestIn (csc + i) sc then e.gsn else 0) +
          (if steadyParent (csc + i) == sc && isSteadyNestedClass (csc + i) then e.gst else 0)).sum
  | [], _ => rfl
  | e :: tl, csc => by
    rw [childNestedSlice, childNestedSlice_eq_range sc tl (csc + 1),
        List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [Nat.add_zero, List.getD, List.getElem?_cons_zero, Option.getD_some]
    rw [Nat.add_left_cancel_iff]
    refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
    simp only [Function.comp_apply, List.getElem?_cons_succ]
    have hIdxEq : csc + 1 + i = csc + (i + 1) := by omega
    simp only [hIdxEq]

theorem fineBoundsUpTo_length (peakPhys : Nat → Nat) (n : Nat) :
    (fineBoundsUpTo peakPhys n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fineBoundsUpTo, appendClassStep_length, ih]

theorem fineBoundsUpTo_succ (peakPhys : Nat → Nat) (n : Nat) :
    fineBoundsUpTo peakPhys (n + 1) =
      fineBoundsUpTo peakPhys n ++ [fineClassStep peakPhys (fineBoundsUpTo peakPhys n) n] := by
  rw [fineBoundsUpTo, appendClassStep_eq_slice, Nat.zero_add,
      childNestedSlice_eq_range, fineBoundsUpTo_length]
  simp [fineClassStep, childNestedFrom]

/-- Full 48-class bound table under physical user-slot cap `peakPhys`. -/
def fineClassBounds (peakPhys : Nat → Nat) : List ClassFineBound :=
  fineBoundsUpTo peakPhys 48

def fineClassEntry (peakPhys : Nat → Nat) (sc : Nat) : ClassFineBound :=
  (fineClassBounds peakPhys).getD sc ClassFineBound.zero

def fineChildNested (peakPhys : Nat → Nat) (sc : Nat) : Nat :=
  childNestedFrom (fineClassBounds peakPhys) sc

def fineRawOcc (peakPhys : Nat → Nat) (sc : Nat) : Nat :=
  peakPhys sc + fineChildNested peakPhys sc

theorem fineClassBounds_length (peakPhys : Nat → Nat) :
    (fineClassBounds peakPhys).length = 48 :=
  fineBoundsUpTo_length peakPhys 48

theorem fineBoundsUpTo_getD_of_lt (peakPhys : Nat → Nat) {k m n : Nat}
    (hkm : k < m) (hmn : m ≤ n) :
    (fineBoundsUpTo peakPhys n).getD k ClassFineBound.zero =
      (fineBoundsUpTo peakPhys m).getD k ClassFineBound.zero := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · rfl
    · have hkn : k < n := by omega
      have hlen : (fineBoundsUpTo peakPhys n).length = n := fineBoundsUpTo_length peakPhys n
      simp only [fineBoundsUpTo_succ, List.getD, List.getElem?_append_left (by omega : k < (fineBoundsUpTo peakPhys n).length)]
      exact ih (Nat.le_of_lt_succ hlt)

theorem fineBoundsUpTo_getD_self (peakPhys : Nat → Nat) (sc : Nat) :
    (fineBoundsUpTo peakPhys (sc + 1)).getD sc ClassFineBound.zero =
      fineClassStep peakPhys (fineBoundsUpTo peakPhys sc) sc := by
  have hlen := fineBoundsUpTo_length peakPhys sc
  simp [fineBoundsUpTo_succ, List.getD, hlen]

theorem childNestedFrom_congr {acc1 acc2 : List ClassFineBound} {sc : Nat}
    (h : ∀ csc < sc, acc1.getD csc ClassFineBound.zero = acc2.getD csc ClassFineBound.zero) :
    childNestedFrom acc1 sc = childNestedFrom acc2 sc := by
  unfold childNestedFrom
  congr 1
  refine List.map_congr_left fun csc hcsc => ?_
  rw [h csc (List.mem_range.mp hcsc)]

/-- Exact unfolding equation for `fineClassEntry peakPhys sc` (`sc < 48`) in terms of
    `fineRawOcc peakPhys sc = peakPhys sc + fineChildNested peakPhys sc`. -/
theorem fineClassEntry_eq {peakPhys : Nat → Nat} {sc : Nat} (hsc : sc < 48) :
    fineClassEntry peakPhys sc =
      (let occ := fineRawOcc peakPhys sc
       if occ == 0 then ClassFineBound.zero
       else
         { gsn := maxSmallNestedGroups sc
           gst := if isSteadyNestedClass sc then 1 + occ / steadyCnt sc else 0
           gr  := if hasRootPair sc then 1 + occ / cntMinRoot sc else 0
           rb  := if hasRootPair sc then maxRootBytes sc + ceilRootPerSlot sc * occ else 0 }) := by
  unfold fineClassEntry fineClassBounds
  rw [fineBoundsUpTo_getD_of_lt peakPhys (Nat.lt_succ_self sc) hsc,
      fineBoundsUpTo_getD_self]
  unfold fineClassStep fineRawOcc fineChildNested fineClassBounds
  have hCongr : childNestedFrom (fineBoundsUpTo peakPhys sc) sc =
      childNestedFrom (fineBoundsUpTo peakPhys 48) sc :=
    childNestedFrom_congr fun csc hcsc =>
      (fineBoundsUpTo_getD_of_lt peakPhys hcsc (by omega)).symm
  rw [hCongr]
  rfl

private theorem sum_map_le_fine {α : Type} {f g : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem x hy))

theorem childNestedFrom_mono {acc1 acc2 : List ClassFineBound} {sc : Nat}
    (h : ∀ csc < sc, (acc1.getD csc ClassFineBound.zero).le (acc2.getD csc ClassFineBound.zero)) :
    childNestedFrom acc1 sc ≤ childNestedFrom acc2 sc := by
  unfold childNestedFrom
  refine sum_map_le_fine fun csc hcsc => ?_
  have hc := h csc (List.mem_range.mp hcsc)
  refine Nat.add_le_add ?_ ?_
  · split
    · exact hc.1
    · exact Nat.le_refl 0
  · split
    · exact hc.2.1
    · exact Nat.le_refl 0

theorem fineClassStep_mono {p1 p2 : Nat → Nat} {acc1 acc2 : List ClassFineBound} {sc : Nat}
    (hp : p1 sc ≤ p2 sc)
    (hacc : ∀ csc < sc, (acc1.getD csc ClassFineBound.zero).le (acc2.getD csc ClassFineBound.zero)) :
    (fineClassStep p1 acc1 sc).le (fineClassStep p2 acc2 sc) := by
  have hch := childNestedFrom_mono hacc
  unfold fineClassStep fineClassStepOfOcc
  have hocc : p1 sc + childNestedFrom acc1 sc ≤ p2 sc + childNestedFrom acc2 sc :=
    Nat.add_le_add hp hch
  by_cases h0 : (p1 sc + childNestedFrom acc1 sc == 0) = true
  · simp only [h0, ↓reduceIte, ClassFineBound.le, ClassFineBound.zero]
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  · have hPos1 : 0 < p1 sc + childNestedFrom acc1 sc := by
      rw [beq_iff_eq] at h0; omega
    have h02 : (p2 sc + childNestedFrom acc2 sc == 0) = false :=
      beq_false_of_ne (by omega)
    simp only [Bool.eq_false_iff.mpr h0, h02, Bool.false_eq_true, ↓reduceIte, ClassFineBound.le]
    refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
    · split
      · exact Nat.add_le_add_left (Nat.div_le_div_right hocc) 1
      · exact Nat.le_refl 0
    · split
      · exact Nat.add_le_add_left (Nat.div_le_div_right hocc) 1
      · exact Nat.le_refl 0
    · split
      · exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hocc) _
      · exact Nat.le_refl 0

theorem fineBoundsUpTo_mono {p1 p2 : Nat → Nat} (n : Nat)
    (hp : ∀ sc < n, p1 sc ≤ p2 sc) :
    ∀ sc < n, ((fineBoundsUpTo p1 n).getD sc ClassFineBound.zero).le
      ((fineBoundsUpTo p2 n).getD sc ClassFineBound.zero) := by
  induction n with
  | zero => intro _ h; omega
  | succ n ih =>
    have hprev := ih (fun sc hsc => hp sc (Nat.lt_succ_of_lt hsc))
    intro sc hsc
    rcases Nat.lt_succ_iff_lt_or_eq.mp hsc with hlt | rfl
    · rw [fineBoundsUpTo_getD_of_lt p1 hlt (Nat.le_succ n),
          fineBoundsUpTo_getD_of_lt p2 hlt (Nat.le_succ n)]
      exact hprev sc hlt
    · rw [fineBoundsUpTo_getD_self, fineBoundsUpTo_getD_self]
      exact fineClassStep_mono (hp sc (Nat.lt_succ_self sc)) hprev

theorem fineClassEntry_mono {p1 p2 : Nat → Nat}
    (hp : ∀ sc < 48, p1 sc ≤ p2 sc) {sc : Nat} (hsc : sc < 48) :
    (fineClassEntry p1 sc).le (fineClassEntry p2 sc) :=
  fineBoundsUpTo_mono 48 hp sc hsc

/-! ## 5. Aggregate Slab Group / Byte Totals & Per-Call Step Reserve -/

/-- Total slab groups (`sc < 48`, both nested and root) bounded by `fineClassBounds`. -/
def fineSlabGroups (peakPhys : Nat → Nat) : Nat :=
  ((fineClassBounds peakPhys).map fun e => e.gsn + e.gst + e.gr).sum

/-- Total mapped slab root groups (`sc < 48`, `0 < maplen`) bounded by `fineClassBounds`. -/
def fineSlabRootGroups (peakPhys : Nat → Nat) : Nat :=
  ((fineClassBounds peakPhys).map fun e => e.gr).sum

/-- Total mapped bytes of slab root groups (`sc < 48`, `0 < maplen`) bounded by `fineClassBounds`. -/
def fineSlabRootBytes (peakPhys : Nat → Nat) : Nat :=
  ((fineClassBounds peakPhys).map fun e => e.rb).sum

private theorem list_map_eq_range_getD {α β : Type} (xs : List α) (d : α) (f : α → β) :
    xs.map f = (List.range xs.length).map (fun i => f (xs.getD i d)) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map]
    exact congrArg (List.cons (f x)) ih

theorem fineSlabGroups_eq_range (peakPhys : Nat → Nat) :
    fineSlabGroups peakPhys =
      ((List.range 48).map fun sc =>
        let e := fineClassEntry peakPhys sc
        e.gsn + e.gst + e.gr).sum := by
  unfold fineSlabGroups fineClassEntry
  rw [list_map_eq_range_getD (fineClassBounds peakPhys) ClassFineBound.zero,
      fineClassBounds_length]

theorem fineSlabRootGroups_eq_range (peakPhys : Nat → Nat) :
    fineSlabRootGroups peakPhys =
      ((List.range 48).map fun sc => (fineClassEntry peakPhys sc).gr).sum := by
  unfold fineSlabRootGroups fineClassEntry
  rw [list_map_eq_range_getD (fineClassBounds peakPhys) ClassFineBound.zero,
      fineClassBounds_length]

theorem fineSlabRootBytes_eq_range (peakPhys : Nat → Nat) :
    fineSlabRootBytes peakPhys =
      ((List.range 48).map fun sc => (fineClassEntry peakPhys sc).rb).sum := by
  unfold fineSlabRootBytes fineClassEntry
  rw [list_map_eq_range_getD (fineClassBounds peakPhys) ClassFineBound.zero,
      fineClassBounds_length]

theorem fineSlabGroups_mono {p1 p2 : Nat → Nat} (hp : ∀ sc < 48, p1 sc ≤ p2 sc) :
    fineSlabGroups p1 ≤ fineSlabGroups p2 := by
  rw [fineSlabGroups_eq_range, fineSlabGroups_eq_range]
  refine sum_map_le_fine fun sc hsc => ?_
  have h := fineClassEntry_mono hp (List.mem_range.mp hsc)
  exact Nat.add_le_add (Nat.add_le_add h.1 h.2.1) h.2.2.1

theorem fineSlabRootGroups_mono {p1 p2 : Nat → Nat} (hp : ∀ sc < 48, p1 sc ≤ p2 sc) :
    fineSlabRootGroups p1 ≤ fineSlabRootGroups p2 := by
  rw [fineSlabRootGroups_eq_range, fineSlabRootGroups_eq_range]
  exact sum_map_le_fine fun sc hsc => (fineClassEntry_mono hp (List.mem_range.mp hsc)).2.2.1

theorem fineSlabRootBytes_mono {p1 p2 : Nat → Nat} (hp : ∀ sc < 48, p1 sc ≤ p2 sc) :
    fineSlabRootBytes p1 ≤ fineSlabRootBytes p2 := by
  rw [fineSlabRootBytes_eq_range, fineSlabRootBytes_eq_range]
  exact sum_map_le_fine fun sc hsc => (fineClassEntry_mono hp (List.mem_range.mp hsc)).2.2.2

/-- Newly mapped + refused `mprotect` page bound for one `__malloc_alloc_meta()` call when
    `st.metaAreas.length ≤ maxMeta` (`4096 * 2^(m+1) + 4096 ≤ 4096 * (maxMeta + 43)`). -/
def FineMetaStep (maxMeta : Nat) : Nat :=
  4096 * (maxMeta + 43)

/-- Per-call step reserve covering both small/medium `alloc_slot` (`≤ 4` meta steps + `1 MiB` root
    group) and large `mmap` / `mremap` (`1` meta step + `reqBytes + 8195`). -/
def FineStepBound (maxMeta reqBytes : Nat) : Nat :=
  max (4 * FineMetaStep maxMeta + 1048576) (FineMetaStep maxMeta + reqBytes + 8195)

theorem FineMetaStep_mono {m1 m2 : Nat} (h : m1 ≤ m2) : FineMetaStep m1 ≤ FineMetaStep m2 := by
  unfold FineMetaStep; omega

theorem FineStepBound_mono {m1 m2 r1 r2 : Nat} (hm : m1 ≤ m2) (hr : r1 ≤ r2) :
    FineStepBound m1 r1 ≤ FineStepBound m2 r2 := by
  unfold FineStepBound FineMetaStep; omega

theorem req_le_FineStepBound (maxMeta reqBytes : Nat) :
    reqBytes ≤ FineStepBound maxMeta reqBytes := by
  unfold FineStepBound; omega

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine

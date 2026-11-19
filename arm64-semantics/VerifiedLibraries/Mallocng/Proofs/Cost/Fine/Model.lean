/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Tables
public import VerifiedLibraries.Mallocng.Proofs.Cost.ModelOom

/-!
# Per-Size-Class Fine Cost Model (`VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Model`)

- **Layer & Role**: `Role::Proof` (untrusted). Defines `FineBudget`, `mallocngFineCostModel`,
  `fineLawful : LawfulCostModel mallocngFineCostModel`, `fine_alloc0_le_stepReserve`, and
  closed-form client bounds (both per-class caps and aggregate stride-sum caps).
- **Design**:
  - Tracks live and peak user block counts per nominal class `nomSc req ∈ 0..47` (`liveByNom`,
    `peakByNom`), cumulative exceptional slab placements (`excByClass`, nonzero only on
    `aligned_alloc` with `align > 16` or cross-class in-place `realloc`), individual-`mmap`
    `sc = 63` live/peak counts & bytes (`live63Count`, `peak63Count`, `live63Bytes`, `peak63Bytes`),
    and cumulative `align > 16` straddlers/slack (`straddle63Cum`, `overAlignCum`).
  - `free` reuse credit: `fineStepFree` decrements `liveByNom[nomSc req]` (independent of `align`),
    so churn loops (`malloc` + `free` repeated millions of times) keep `peakByNom` bounded by
    **simultaneously live** blocks per class.
  - Tight `maxDynIvs`: `3 * fineMaxMetaAreas + 2 + fineMaxRootGroups` (`≪ 500k` even at `2.8M`
    live small blocks, fitting comfortably inside 48-bit `VaRoom`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
  VerifiedLibraries.Mallocng.Proofs.Cost

/-! ## 1. 48-Class Vector Helper & `FineBudget` State -/

/-- Build a length-48 `List Nat` from an index function `0 .. 47`. -/
def vec48Of (f : Nat → Nat) : List Nat :=
  (List.range 48).map f

@[simp] theorem vec48Of_length (f : Nat → Nat) : (vec48Of f).length = 48 := by
  simp [vec48Of]

theorem vec48Of_getD (f : Nat → Nat) (sc : Nat) :
    (vec48Of f).getD sc 0 = if sc < 48 then f sc else 0 := by
  by_cases hsc : sc < 48 <;> simp [vec48Of, List.getD, hsc]

/-- Abstract state of `mallocngFineCostModel`. -/
structure FineBudget where
  liveByNom        : List Nat
  peakByNom        : List Nat
  reallocPeakByNom : List Nat
  excByClass       : List Nat
  live63Bytes      : Nat
  peak63Bytes      : Nat
  live63Count      : Nat
  peak63Count      : Nat
  straddle63Cum    : Nat
  overAlignCum     : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Initial empty-heap budget. -/
def fineInit : FineBudget where
  liveByNom        := vec48Of fun _ => 0
  peakByNom        := vec48Of fun _ => 0
  reallocPeakByNom := vec48Of fun _ => 0
  excByClass       := vec48Of fun _ => 0
  live63Bytes      := 0
  peak63Bytes      := 0
  live63Count      := 0
  peak63Count      := 0
  straddle63Cum    := 0
  overAlignCum     := 0

/-- Physical user-slot cap for slab class `sc < 48` induced by `bgt` (`D1.A`):
    nominal `sc` blocks, coarse `sc | 1` bumps from `sc - 1`, live/peak-indexed cross-class
    in-place `realloc` slots (`reallocPeakByNom[kn] ≤ peakByNom[kn]`), and `align > 16`
    over-aligned slab slots (`excByClass[sc]`). -/
def peakPhysOfBudget (bgt : FineBudget) (sc : Nat) : Nat :=
  bgt.peakByNom.getD sc 0 +
  (if 0 < sc && coarseBumpable (sc - 1) then bgt.peakByNom.getD (sc - 1) 0 else 0) +
  ((List.range 48).map fun kn =>
    if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then
      bgt.reallocPeakByNom.getD kn 0
    else 0).sum +
  bgt.excByClass.getD sc 0

/-- Maximum active groups (`sc < 48` nested + root, plus `sc = 63` individual `mmap` groups). -/
def fineMaxGroups (bgt : FineBudget) : Nat :=
  fineSlabGroups (peakPhysOfBudget bgt) + bgt.peak63Count + bgt.straddle63Cum

/-- Maximum mapped root groups (`0 < maplen`, both `sc < 48` and `sc = 63`). -/
def fineMaxRootGroups (bgt : FineBudget) : Nat :=
  fineSlabRootGroups (peakPhysOfBudget bgt) + bgt.peak63Count + bgt.straddle63Cum

/-- Maximum `4096`-byte `meta_area` pages (`101` `struct meta` slots per page, `≤ 7` free/bump/in-flight
    slack at quiescent or mid-recursion points: `101 * m ≤ G + 108 ⇒ m ≤ 1 + (7 + G) / 101`). -/
def fineMaxMetaAreas (bgt : FineBudget) : Nat :=
  1 + (7 + fineMaxGroups bgt) / 101

/-- Maximum dynamic intervals from `metaAreas`, `guardPages`, and `availMetaPages` combined
    (`m + (m + 1) + (2^k - 2) ≤ 3 * m + 2`). -/
def fineMetaIvs (bgt : FineBudget) : Nat :=
  3 * fineMaxMetaAreas bgt + 2

/-- Current dynamic mapped-byte bound for `bgt` (`sc = 63` term shrinks on `free`). -/
def fineFootprint (bgt : FineBudget) : Nat :=
  4096 * fineMetaIvs bgt +
  fineSlabRootBytes (peakPhysOfBudget bgt) +
  bgt.live63Bytes + 8195 * bgt.live63Count +
  139246 * bgt.straddle63Cum + bgt.overAlignCum

/-- Monotone peak dynamic mapped-byte bound for `bgt`. -/
def finePeakFootprint (bgt : FineBudget) : Nat :=
  4096 * fineMetaIvs bgt +
  fineSlabRootBytes (peakPhysOfBudget bgt) +
  bgt.peak63Bytes + 8195 * bgt.peak63Count +
  139246 * bgt.straddle63Cum + bgt.overAlignCum

/-- Maximum dynamic intervals `ivs.length` (`meta` + `guard` + `avail` + root groups). -/
def fineMaxDynIvs (bgt : FineBudget) : Nat :=
  fineMetaIvs bgt + fineMaxRootGroups bgt

/-- Per-call step reserve covering newly mapped pages plus any refused `mmap` / `mprotect` request. -/
def fineStepReserve (ev : AllocEvent) (bgt : FineBudget) : Nat :=
  FineStepBound (fineMaxMetaAreas bgt) (evReqBytes ev)

/-! ## 2. Event Transitions & `mallocngFineCostModel` -/

/-- Budget transition for `malloc(req)` / `calloc` (`align ≤ 16`). -/
def fineStepAlloc (req : Nat) (bgt : FineBudget) : FineBudget :=
  if req ≤ MmapThresholdReq then
    let k := nomSc req
    { bgt with
      liveByNom := vec48Of fun sc => bgt.liveByNom.getD sc 0 + (if sc == k then 1 else 0)
      peakByNom := vec48Of fun sc =>
        max (bgt.peakByNom.getD sc 0) (bgt.liveByNom.getD sc 0 + (if sc == k then 1 else 0)) }
  else
    { bgt with
      live63Bytes := bgt.live63Bytes + req
      peak63Bytes := max bgt.peak63Bytes (bgt.live63Bytes + req)
      live63Count := bgt.live63Count + 1
      peak63Count := max bgt.peak63Count (bgt.live63Count + 1) }

/-- Budget transition for `free(_, req)` (independent of `align` so `realloc` `outAlign` matches). -/
def fineStepFree (req : Nat) (bgt : FineBudget) : FineBudget :=
  if req ≤ MmapThresholdReq then
    let k := nomSc req
    { bgt with
      liveByNom := vec48Of fun sc => bgt.liveByNom.getD sc 0 - (if sc == k then 1 else 0) }
  else
    { bgt with
      live63Bytes := bgt.live63Bytes - req
      live63Count := bgt.live63Count - 1 }

/-- Budget transition for `aligned_alloc(align, req)` / `posix_memalign(_, align, req)`.
    When `align ≤ 16`, identical to `fineStepAlloc req bgt` (zero exceptional overhead). -/
def fineStepAligned (align req : Nat) (bgt : FineBudget) : FineBudget :=
  if align ≤ 16 then
    fineStepAlloc req bgt
  else
    let eff := mallocngAlignedEffSize align req
    let b1 := fineStepAlloc req bgt
    if eff ≤ MmapThresholdReq then
      let ke := nomSc eff
      { b1 with
        excByClass   := vec48Of fun sc =>
          b1.excByClass.getD sc 0 + (if allowedPhysClass ke sc then 1 else 0)
        overAlignCum := b1.overAlignCum + (align - 16) }
    else if req ≤ MmapThresholdReq then
      { b1 with
        straddle63Cum := b1.straddle63Cum + 1
        overAlignCum  := b1.overAlignCum + (align - 16) }
    else
      { b1 with
        overAlignCum := b1.overAlignCum + (align - 16) }

/-- Budget transition for `realloc(p, newSz)` on a live block of `oldSz` bytes (`D1.A`:
    allocates `newSz` before freeing `oldSz` so peaks cover Stage-4 coexistence, and records
    `reallocPeakByNom[kn] = max reallocPeakByNom[kn] liveByNom'[kn]` on cross-class small
    transitions without touching `excByClass`). -/
def fineStepRealloc (_align oldSz newSz : Nat) (bgt : FineBudget) : FineBudget :=
  let b1 := fineStepFree oldSz (fineStepAlloc newSz bgt)
  if oldSz ≤ MmapThresholdReq ∧ newSz ≤ MmapThresholdReq ∧ nomSc oldSz ≠ nomSc newSz then
    let kn := nomSc newSz
    { b1 with
      reallocPeakByNom := vec48Of fun k =>
        if k == kn then max (b1.reallocPeakByNom.getD k 0) (b1.liveByNom.getD k 0)
        else b1.reallocPeakByNom.getD k 0 }
  else
    b1

/-- Dispatch `AllocEvent` on `FineBudget`. -/
def fineStep : AllocEvent → FineBudget → FineBudget
  | .alloc req             => fineStepAlloc req
  | .aligned align req     => fineStepAligned align req
  | .free _align req       => fineStepFree req
  | .realloc align old new => fineStepRealloc align old new

/-- The fine per-size-class `AllocCostModel` for `mallocng`. -/
def mallocngFineCostModel : AllocCostModel where
  σ           := FineBudget
  init        := fineInit
  step        := fineStep
  footprint   := fineFootprint
  maxDynIvs   := fineMaxDynIvs
  stepReserve := fineStepReserve

@[simp, cost_simp] theorem mallocngFineCostModel_init :
    mallocngFineCostModel.init = fineInit := rfl

@[simp, cost_simp] theorem mallocngFineCostModel_step (ev : AllocEvent) (bgt : FineBudget) :
    mallocngFineCostModel.step ev bgt = fineStep ev bgt := rfl

@[simp, cost_simp] theorem mallocngFineCostModel_footprint (bgt : FineBudget) :
    mallocngFineCostModel.footprint bgt = fineFootprint bgt := rfl

@[simp, cost_simp] theorem mallocngFineCostModel_maxDynIvs (bgt : FineBudget) :
    mallocngFineCostModel.maxDynIvs bgt = fineMaxDynIvs bgt := rfl

@[simp, cost_simp] theorem mallocngFineCostModel_stepReserve (ev : AllocEvent) (bgt : FineBudget) :
    mallocngFineCostModel.stepReserve ev bgt = fineStepReserve ev bgt := rfl

/-! ## 3. Budget Invariant, Monotonicity & `LawfulCostModel` Instance -/

/-- Well-formedness of `FineBudget` along any `evalLog`. -/
structure FineBudgetInv (bgt : FineBudget) : Prop where
  live_len         : bgt.liveByNom.length = 48
  peak_len         : bgt.peakByNom.length = 48
  realloc_len      : bgt.reallocPeakByNom.length = 48
  exc_len          : bgt.excByClass.length = 48
  live_le_peak     : ∀ sc < 48, bgt.liveByNom.getD sc 0 ≤ bgt.peakByNom.getD sc 0
  realloc_le_peak  : ∀ sc < 48, bgt.reallocPeakByNom.getD sc 0 ≤ bgt.peakByNom.getD sc 0
  live63Bytes_le   : bgt.live63Bytes ≤ bgt.peak63Bytes
  live63Count_le   : bgt.live63Count ≤ bgt.peak63Count

/-- Coordinatewise peak monotonicity across transitions. -/
structure FinePeaksLe (b1 b2 : FineBudget) : Prop where
  peak_le        : ∀ sc < 48, b1.peakByNom.getD sc 0 ≤ b2.peakByNom.getD sc 0
  realloc_le     : ∀ sc < 48, b1.reallocPeakByNom.getD sc 0 ≤ b2.reallocPeakByNom.getD sc 0
  exc_le         : ∀ sc < 48, b1.excByClass.getD sc 0 ≤ b2.excByClass.getD sc 0
  peak63Bytes_le : b1.peak63Bytes ≤ b2.peak63Bytes
  peak63Count_le : b1.peak63Count ≤ b2.peak63Count
  straddle_le    : b1.straddle63Cum ≤ b2.straddle63Cum
  overAlign_le   : b1.overAlignCum ≤ b2.overAlignCum

theorem FinePeaksLe.refl (b : FineBudget) : FinePeaksLe b b :=
  ⟨fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _,
   Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem FinePeaksLe.trans {b1 b2 b3 : FineBudget}
    (h12 : FinePeaksLe b1 b2) (h23 : FinePeaksLe b2 b3) : FinePeaksLe b1 b3 :=
  ⟨fun sc hsc => Nat.le_trans (h12.peak_le sc hsc) (h23.peak_le sc hsc),
   fun sc hsc => Nat.le_trans (h12.realloc_le sc hsc) (h23.realloc_le sc hsc),
   fun sc hsc => Nat.le_trans (h12.exc_le sc hsc) (h23.exc_le sc hsc),
   Nat.le_trans h12.peak63Bytes_le h23.peak63Bytes_le,
   Nat.le_trans h12.peak63Count_le h23.peak63Count_le,
   Nat.le_trans h12.straddle_le h23.straddle_le,
   Nat.le_trans h12.overAlign_le h23.overAlign_le⟩

theorem fineBudgetInv_init : FineBudgetInv fineInit where
  live_len := vec48Of_length _
  peak_len := vec48Of_length _
  realloc_len := vec48Of_length _
  exc_len := vec48Of_length _
  live_le_peak sc hsc := by simp [fineInit, hsc]
  realloc_le_peak sc hsc := by simp [fineInit, hsc]
  live63Bytes_le := Nat.le_refl 0
  live63Count_le := Nat.le_refl 0

theorem fineBudgetInv_stepAlloc (req : Nat) {bgt : FineBudget} (h : FineBudgetInv bgt) :
    FineBudgetInv (fineStepAlloc req bgt) := by
  unfold fineStepAlloc
  split
  · refine ⟨vec48Of_length _, vec48Of_length _, h.realloc_len, h.exc_len,
      ?_, ?_, h.live63Bytes_le, h.live63Count_le⟩
    · intro sc hsc; simp only [vec48Of_getD, hsc, ↓reduceIte]; exact Nat.le_max_right _ _
    · intro sc hsc; simp only [vec48Of_getD, hsc, ↓reduceIte]
      exact Nat.le_trans (h.realloc_le_peak sc hsc) (Nat.le_max_left _ _)
  · exact ⟨h.live_len, h.peak_len, h.realloc_len, h.exc_len,
      h.live_le_peak, h.realloc_le_peak, Nat.le_max_right _ _, Nat.le_max_right _ _⟩

theorem fineBudgetInv_stepFree (req : Nat) {bgt : FineBudget} (h : FineBudgetInv bgt) :
    FineBudgetInv (fineStepFree req bgt) := by
  unfold fineStepFree
  split
  · refine ⟨vec48Of_length _, h.peak_len, h.realloc_len, h.exc_len,
      ?_, h.realloc_le_peak, h.live63Bytes_le, h.live63Count_le⟩
    intro sc hsc
    have hle := h.live_le_peak sc hsc
    simp only [vec48Of_getD, hsc, ↓reduceIte]; omega
  · refine ⟨h.live_len, h.peak_len, h.realloc_len, h.exc_len,
      h.live_le_peak, h.realloc_le_peak, ?_, ?_⟩
    · dsimp only; have := h.live63Bytes_le; omega
    · dsimp only; have := h.live63Count_le; omega

theorem fineBudgetInv_step (ev : AllocEvent) {bgt : FineBudget} (h : FineBudgetInv bgt) :
    FineBudgetInv (fineStep ev bgt) := by
  cases ev with
  | alloc req => exact fineBudgetInv_stepAlloc req h
  | free _ req => exact fineBudgetInv_stepFree req h
  | aligned align req =>
    show FineBudgetInv (fineStepAligned align req bgt)
    unfold fineStepAligned
    split
    · exact fineBudgetInv_stepAlloc req h
    · have h1 := fineBudgetInv_stepAlloc req h
      dsimp only
      split
      · exact ⟨h1.live_len, h1.peak_len, h1.realloc_len, vec48Of_length _,
          h1.live_le_peak, h1.realloc_le_peak, h1.live63Bytes_le, h1.live63Count_le⟩
      · split <;> exact ⟨h1.live_len, h1.peak_len, h1.realloc_len, h1.exc_len,
          h1.live_le_peak, h1.realloc_le_peak, h1.live63Bytes_le, h1.live63Count_le⟩
  | realloc align oldSz newSz =>
    show FineBudgetInv (fineStepRealloc align oldSz newSz bgt)
    unfold fineStepRealloc
    have h1 := fineBudgetInv_stepFree oldSz (fineBudgetInv_stepAlloc newSz h)
    dsimp only
    split
    · refine ⟨h1.live_len, h1.peak_len, vec48Of_length _, h1.exc_len,
        h1.live_le_peak, ?_, h1.live63Bytes_le, h1.live63Count_le⟩
      intro sc hsc
      simp only [vec48Of_getD, hsc, ↓reduceIte]
      have hr := h1.realloc_le_peak sc hsc
      have hl := h1.live_le_peak sc hsc
      split <;> omega
    · exact h1

private theorem sum_map_le_model {α : Type} {f g : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem x hy))

theorem finePeaksLe_stepAlloc (req : Nat) (bgt : FineBudget) :
    FinePeaksLe bgt (fineStepAlloc req bgt) := by
  unfold fineStepAlloc
  split
  · refine ⟨?_, fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _,
      Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
    intro sc hsc; simp only [vec48Of_getD, hsc, ↓reduceIte]; exact Nat.le_max_left _ _
  · exact ⟨fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _,
      Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_refl _, Nat.le_refl _⟩

theorem finePeaksLe_stepFree (req : Nat) (bgt : FineBudget) :
    FinePeaksLe bgt (fineStepFree req bgt) := by
  unfold fineStepFree
  split <;> exact ⟨fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem finePeaksLe_step (ev : AllocEvent) (bgt : FineBudget) :
    FinePeaksLe bgt (fineStep ev bgt) := by
  cases ev with
  | alloc req => exact finePeaksLe_stepAlloc req bgt
  | free _ req => exact finePeaksLe_stepFree req bgt
  | aligned align req =>
    show FinePeaksLe bgt (fineStepAligned align req bgt)
    unfold fineStepAligned
    split
    · exact finePeaksLe_stepAlloc req bgt
    · refine FinePeaksLe.trans (finePeaksLe_stepAlloc req bgt) ?_
      dsimp only
      split
      · refine ⟨fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, ?_,
          Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by dsimp only; omega⟩
        intro sc hsc; simp only [vec48Of_getD, hsc, ↓reduceIte]; omega
      · split
        · exact ⟨fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _,
            Nat.le_refl _, Nat.le_refl _, by dsimp only; omega, by dsimp only; omega⟩
        · exact ⟨fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _,
            Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by dsimp only; omega⟩
  | realloc align oldSz newSz =>
    show FinePeaksLe bgt (fineStepRealloc align oldSz newSz bgt)
    unfold fineStepRealloc
    refine FinePeaksLe.trans
      (FinePeaksLe.trans (finePeaksLe_stepAlloc newSz bgt)
        (finePeaksLe_stepFree oldSz (fineStepAlloc newSz bgt))) ?_
    dsimp only
    split
    · refine ⟨fun _ _ => Nat.le_refl _, ?_, fun _ _ => Nat.le_refl _,
        Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
      intro sc hsc; simp only [vec48Of_getD, hsc, ↓reduceIte]; split <;> omega
    · exact FinePeaksLe.refl _

theorem peakPhysOfBudget_mono {b1 b2 : FineBudget} (hp : FinePeaksLe b1 b2)
    {sc : Nat} (hsc : sc < 48) :
    peakPhysOfBudget b1 sc ≤ peakPhysOfBudget b2 sc := by
  unfold peakPhysOfBudget
  have h1 := hp.peak_le sc hsc
  have h4 := hp.exc_le sc hsc
  have h2 :
      (if 0 < sc && coarseBumpable (sc - 1) then b1.peakByNom.getD (sc - 1) 0 else 0) ≤
      (if 0 < sc && coarseBumpable (sc - 1) then b2.peakByNom.getD (sc - 1) 0 else 0) := by
    split
    · exact hp.peak_le (sc - 1) (by omega)
    · exact Nat.le_refl 0
  have h3 :
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then b1.reallocPeakByNom.getD kn 0 else 0).sum ≤
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then b2.reallocPeakByNom.getD kn 0 else 0).sum := by
    refine sum_map_le_model fun kn hkn => ?_
    split
    · exact hp.realloc_le kn (List.mem_range.mp hkn)
    · exact Nat.le_refl 0
  omega

theorem fineMaxGroups_mono {b1 b2 : FineBudget} (hp : FinePeaksLe b1 b2) :
    fineMaxGroups b1 ≤ fineMaxGroups b2 := by
  unfold fineMaxGroups
  have h1 := fineSlabGroups_mono (p1 := peakPhysOfBudget b1) (p2 := peakPhysOfBudget b2)
    (fun sc hsc => peakPhysOfBudget_mono hp hsc)
  have h2 := hp.peak63Count_le
  have h3 := hp.straddle_le
  omega

theorem fineMaxRootGroups_mono {b1 b2 : FineBudget} (hp : FinePeaksLe b1 b2) :
    fineMaxRootGroups b1 ≤ fineMaxRootGroups b2 := by
  unfold fineMaxRootGroups
  have h1 := fineSlabRootGroups_mono (p1 := peakPhysOfBudget b1) (p2 := peakPhysOfBudget b2)
    (fun sc hsc => peakPhysOfBudget_mono hp hsc)
  have h2 := hp.peak63Count_le
  have h3 := hp.straddle_le
  omega

theorem fineMaxMetaAreas_mono {b1 b2 : FineBudget} (hp : FinePeaksLe b1 b2) :
    fineMaxMetaAreas b1 ≤ fineMaxMetaAreas b2 := by
  unfold fineMaxMetaAreas
  have h := fineMaxGroups_mono hp
  exact Nat.add_le_add_left (Nat.div_le_div_right (by omega)) 1

theorem fineMetaIvs_mono {b1 b2 : FineBudget} (hp : FinePeaksLe b1 b2) :
    fineMetaIvs b1 ≤ fineMetaIvs b2 := by
  unfold fineMetaIvs
  have h := fineMaxMetaAreas_mono hp
  omega

theorem finePeakFootprint_mono {b1 b2 : FineBudget} (hp : FinePeaksLe b1 b2) :
    finePeakFootprint b1 ≤ finePeakFootprint b2 := by
  unfold finePeakFootprint
  have hM := fineMetaIvs_mono hp
  have hS := fineSlabRootBytes_mono (p1 := peakPhysOfBudget b1) (p2 := peakPhysOfBudget b2)
    (fun sc hsc => peakPhysOfBudget_mono hp hsc)
  have hB := hp.peak63Bytes_le
  have hC := hp.peak63Count_le
  have hSt := hp.straddle_le
  have hOv := hp.overAlign_le
  omega

theorem fineFootprint_le_peak (bgt : FineBudget) (h : FineBudgetInv bgt) :
    fineFootprint bgt ≤ finePeakFootprint bgt := by
  unfold fineFootprint finePeakFootprint
  have hB := h.live63Bytes_le
  have hC := h.live63Count_le
  omega

/-- Lower-bound user payload proxy that strictly/monotonically decreases on `free`. -/
def fineLiveBytes (bgt : FineBudget) : Nat :=
  ((List.range 48).map fun sc => minReqOfNom sc * bgt.liveByNom.getD sc 0).sum + bgt.live63Bytes

theorem fineLiveBytes_free_le (al n : Nat) (bgt : FineBudget) :
    fineLiveBytes (fineStep (.free al n) bgt) ≤ fineLiveBytes bgt := by
  show fineLiveBytes (fineStepFree n bgt) ≤ fineLiveBytes bgt
  unfold fineStepFree fineLiveBytes
  split
  · dsimp only
    refine Nat.add_le_add_right ?_ _
    refine sum_map_le_model fun sc hsc => ?_
    have hlt := List.mem_range.mp hsc
    simp only [vec48Of_getD, hlt, ↓reduceIte]
    exact Nat.mul_le_mul_left _ (by omega)
  · dsimp only
    exact Nat.add_le_add_left (by omega) _

/-- `mallocngFineCostModel` satisfies all monotonicity & `free`-monotonicity laws of
    `LawfulCostModel`. -/
def fineLawful : LawfulCostModel mallocngFineCostModel where
  Inv                := FineBudgetInv
  inv_init           := fineBudgetInv_init
  inv_step ev bgt h  := fineBudgetInv_step ev h
  peakFootprint      := finePeakFootprint
  footprint_le_peak  := fineFootprint_le_peak
  peakFootprint_mono ev bgt _ := finePeakFootprint_mono (finePeaksLe_step ev bgt)
  maxDynIvs_mono ev bgt _ := by
    show fineMetaIvs bgt + fineMaxRootGroups bgt ≤ _
    exact Nat.add_le_add (fineMetaIvs_mono (finePeaksLe_step ev bgt))
      (fineMaxRootGroups_mono (finePeaksLe_step ev bgt))
  stepReserve_mono ev0 ev bgt _ :=
    FineStepBound_mono (fineMaxMetaAreas_mono (finePeaksLe_step ev bgt)) (Nat.le_refl _)
  req_le_stepReserve ev bgt := req_le_FineStepBound _ _
  liveBytes          := fineLiveBytes
  liveBytes_free_le  := fineLiveBytes_free_le

/-- The failed-request `.alloc 0` reserve is minimal among all events (`ModelOom.stepB_le_of_alloc0_le`). -/
theorem fine_alloc0_le_stepReserve (ev : AllocEvent) (bgt : FineBudget) :
    mallocngFineCostModel.stepReserve (.alloc 0) bgt ≤ mallocngFineCostModel.stepReserve ev bgt :=
  FineStepBound_mono (Nat.le_refl _) (Nat.zero_le _)

/-! ## 4. Closed-Form Client Bounds (Fast O(48) Per-Class Caps & Aggregate Stride-Sum Caps) -/

/-- Physical user-slot cap derived from per-nominal-class peak caps `nomCap`, cross-class
    `realloc` peak caps `rpeakCap`, and `align > 16` exceptional caps `excCap`. -/
def physCapOfNom (nomCap rpeakCap excCap : Nat → Nat) (sc : Nat) : Nat :=
  nomCap sc +
  (if 0 < sc && coarseBumpable (sc - 1) then nomCap (sc - 1) else 0) +
  ((List.range 48).map fun kn =>
    if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then rpeakCap kn else 0).sum +
  excCap sc

/-- Physical user-slot cap requiring no separate `realloc` bound (`reallocPeakByNom ≤ peakByNom`). -/
abbrev physCapOfNomUnrestricted (nomCap excCap : Nat → Nat) : Nat → Nat :=
  physCapOfNom nomCap nomCap excCap

theorem peakPhysOfBudget_le_physCapOfNom {bgt : FineBudget} {nomCap rpeakCap excCap : Nat → Nat}
    (hNom : ∀ sc < 48, bgt.peakByNom.getD sc 0 ≤ nomCap sc)
    (hRp : ∀ kn < 48, bgt.reallocPeakByNom.getD kn 0 ≤ rpeakCap kn)
    (hExc : ∀ sc < 48, bgt.excByClass.getD sc 0 ≤ excCap sc)
    {sc : Nat} (hsc : sc < 48) :
    peakPhysOfBudget bgt sc ≤ physCapOfNom nomCap rpeakCap excCap sc := by
  unfold peakPhysOfBudget physCapOfNom
  have h1 := hNom sc hsc
  have h4 := hExc sc hsc
  have h2 :
      (if 0 < sc && coarseBumpable (sc - 1) then bgt.peakByNom.getD (sc - 1) 0 else 0) ≤
      (if 0 < sc && coarseBumpable (sc - 1) then nomCap (sc - 1) else 0) := by
    split
    · exact hNom (sc - 1) (by omega)
    · exact Nat.le_refl 0
  have h3 :
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then bgt.reallocPeakByNom.getD kn 0 else 0).sum ≤
      ((List.range 48).map fun kn =>
        if canHoldInPlaceRealloc kn sc && !allowedPhysClass kn sc then rpeakCap kn else 0).sum := by
    refine sum_map_le_model fun kn hkn => ?_
    split
    · exact hRp kn (List.mem_range.mp hkn)
    · exact Nat.le_refl 0
  omega

theorem peakPhysOfBudget_le_physCapOfNomUnrestricted {bgt : FineBudget} (hInv : FineBudgetInv bgt)
    {nomCap excCap : Nat → Nat}
    (hNom : ∀ sc < 48, bgt.peakByNom.getD sc 0 ≤ nomCap sc)
    (hExc : ∀ sc < 48, bgt.excByClass.getD sc 0 ≤ excCap sc)
    {sc : Nat} (hsc : sc < 48) :
    peakPhysOfBudget bgt sc ≤ physCapOfNomUnrestricted nomCap excCap sc :=
  peakPhysOfBudget_le_physCapOfNom hNom
    (fun kn hkn => Nat.le_trans (hInv.realloc_le_peak kn hkn) (hNom kn hkn)) hExc hsc

/-- Pre-tabulated static parameters of slab class `sc < 48`, verified equal to the `Tables`
    definitions by `checkFastClassParams_true` (`decide +kernel`) for O(1) kernel evaluation. -/
structure FastClassParams where
  msn    : Nat
  isSt   : Bool
  stCnt  : Nat
  hasRt  : Bool
  cmRt   : Nat
  maxRb  : Nat
  ceilRs : Nat
  snSum  : Nat
  deriving DecidableEq, Repr

def fastSteadyParent : Nat → Nat
  | 0 => 15
  | 1 | 2 => 19
  | 3 | 4 | 5 | 6 => 23
  | _ => 48

def fastClassParams : Nat → FastClassParams
  | 0 => ⟨0, true, 30, false, 32, 0, 0, 0⟩
  | 1 => ⟨9, true, 31, false, 32, 0, 0, 0⟩
  | 2 => ⟨13, true, 20, false, 32, 0, 0, 0⟩
  | 3 => ⟨19, true, 31, false, 32, 0, 0, 0⟩
  | 4 => ⟨22, true, 25, false, 32, 0, 0, 0⟩
  | 5 => ⟨26, true, 21, false, 32, 0, 0, 0⟩
  | 6 => ⟨32, true, 18, false, 32, 0, 0, 0⟩
  | 7 => ⟨19, false, 31, true, 31, 4096, 133, 0⟩
  | 8 => ⟨22, false, 28, true, 28, 4096, 147, 0⟩
  | 9 => ⟨43, false, 24, true, 24, 4096, 171, 0⟩
  | 10 => ⟨26, false, 20, true, 20, 4096, 205, 0⟩
  | 11 => ⟨64, false, 32, true, 16, 8192, 256, 0⟩
  | 12 => ⟨19, false, 28, true, 14, 8192, 293, 0⟩
  | 13 => ⟨43, false, 24, true, 12, 8192, 342, 0⟩
  | 14 => ⟨26, false, 20, true, 10, 8192, 410, 0⟩
  | 15 => ⟨64, false, 32, true, 8, 16384, 512, 228⟩
  | 16 => ⟨0, false, 28, true, 5, 16384, 820, 0⟩
  | 17 => ⟨43, false, 24, true, 6, 16384, 683, 0⟩
  | 18 => ⟨0, false, 20, true, 5, 16384, 820, 0⟩
  | 19 => ⟨64, false, 32, true, 4, 32768, 1024, 380⟩
  | 20 => ⟨0, false, 28, true, 5, 32768, 1639, 0⟩
  | 21 => ⟨0, false, 24, true, 3, 32768, 1366, 0⟩
  | 22 => ⟨0, false, 20, true, 3, 32768, 2731, 0⟩
  | 23 => ⟨0, false, 32, true, 2, 65536, 2048, 433⟩
  | 24 => ⟨0, false, 28, true, 3, 65536, 2731, 0⟩
  | 25 => ⟨0, false, 24, true, 2, 65536, 4096, 0⟩
  | 26 => ⟨0, false, 20, true, 3, 65536, 4096, 0⟩
  | 27 => ⟨0, false, 32, true, 1, 131072, 4096, 0⟩
  | 28 => ⟨0, false, 28, true, 3, 131072, 5462, 0⟩
  | 29 => ⟨0, false, 24, true, 2, 131072, 6144, 0⟩
  | 30 => ⟨0, false, 20, true, 3, 131072, 6827, 0⟩
  | 31 => ⟨0, false, 32, true, 1, 262144, 8192, 0⟩
  | 32 => ⟨0, false, 28, true, 3, 262144, 9558, 0⟩
  | 33 => ⟨0, false, 24, true, 2, 262144, 12288, 0⟩
  | 34 => ⟨0, false, 20, true, 1, 262144, 16384, 0⟩
  | 35 => ⟨0, false, 32, true, 1, 524288, 16384, 0⟩
  | 36 => ⟨0, false, 28, true, 1, 524288, 20480, 0⟩
  | 37 => ⟨0, false, 24, true, 1, 524288, 24576, 0⟩
  | 38 => ⟨0, false, 20, true, 1, 524288, 28672, 0⟩
  | 39 => ⟨0, false, 32, true, 1, 1048576, 32768, 0⟩
  | 40 => ⟨0, false, 28, true, 1, 1048576, 40960, 0⟩
  | 41 => ⟨0, false, 24, true, 1, 1048576, 45056, 0⟩
  | 42 => ⟨0, false, 20, true, 1, 1048576, 53248, 0⟩
  | 43 => ⟨0, false, 16, true, 1, 1048576, 65536, 0⟩
  | 44 => ⟨0, false, 14, true, 1, 1048576, 77824, 0⟩
  | 45 => ⟨0, false, 12, true, 1, 1048576, 90112, 0⟩
  | 46 => ⟨0, false, 10, true, 1, 1048576, 106496, 0⟩
  | 47 => ⟨0, false, 8, true, 1, 1048576, 131072, 0⟩
  | _  => ⟨0, false, 32, false, 32, 0, 0, 0⟩

private def checkFastClassParams : Bool :=
  (List.range 48).all fun sc =>
    let p := fastClassParams sc
    (p.msn == maxSmallNestedGroups sc) &&
    (p.isSt == isSteadyNestedClass sc) &&
    (p.stCnt == steadyCnt sc) &&
    (p.hasRt == hasRootPair sc) &&
    (p.cmRt == cntMinRoot sc) &&
    (p.maxRb == maxRootBytes sc) &&
    (p.ceilRs == ceilRootPerSlot sc) &&
    (p.snSum == ((List.range sc).map fun csc =>
      if canSmallNestIn csc sc then maxSmallNestedGroups csc else 0).sum) &&
    (if sc ≤ 7 then p.snSum == 0 else true) &&
    (if 7 ≤ sc then !p.isSt else true) &&
    ((List.range 7).all fun csc =>
      (steadyParent csc == sc && isSteadyNestedClass csc) == (fastSteadyParent csc == sc))

private theorem checkFastClassParams_true : checkFastClassParams = true := by
  decide +kernel

def fineFastSteadyGst (cap : Nat → Nat) (csc : Nat) : Nat :=
  if cap csc == 0 then 0 else 1 + cap csc / (fastClassParams csc).stCnt

def fineFastOcc (cap : Nat → Nat) (sc : Nat) : Nat :=
  let p := fastClassParams sc
  cap sc + p.snSum +
    ((List.range 7).map fun csc =>
      if fastSteadyParent csc == sc then fineFastSteadyGst cap csc else 0).sum

def fineFastEntry (cap : Nat → Nat) (sc : Nat) : ClassFineBound :=
  let p := fastClassParams sc
  let occ := fineFastOcc cap sc
  if occ == 0 then ClassFineBound.zero
  else
    { gsn := p.msn
      gst := if p.isSt then 1 + occ / p.stCnt else 0
      gr  := if p.hasRt then 1 + occ / p.cmRt else 0
      rb  := if p.hasRt then p.maxRb + p.ceilRs * occ else 0 }

def fineFastSlabGroups (cap : Nat → Nat) : Nat :=
  ((List.range 48).map fun sc =>
    let e := fineFastEntry cap sc
    e.gsn + e.gst + e.gr).sum

def fineFastSlabRootGroups (cap : Nat → Nat) : Nat :=
  ((List.range 48).map fun sc => (fineFastEntry cap sc).gr).sum

def fineFastSlabRootBytes (cap : Nat → Nat) : Nat :=
  ((List.range 48).map fun sc => (fineFastEntry cap sc).rb).sum

/-- Fast O(48) closed-form footprint upper bound under physical class cap `cap`. -/
def fineFastFootprint (cap : Nat → Nat)
    (live63B live63C peak63C stradC ovB : Nat) : Nat :=
  let maxG := fineFastSlabGroups cap + peak63C + stradC
  let maxM := 1 + (7 + maxG) / 101
  4096 * (3 * maxM + 2) + fineFastSlabRootBytes cap +
    live63B + 8195 * live63C + 139246 * stradC + ovB

/-- Fast O(48) closed-form `maxDynIvs` upper bound under physical class cap `cap`. -/
def fineFastMaxDynIvs (cap : Nat → Nat) (peak63C stradC : Nat) : Nat :=
  let maxG := fineFastSlabGroups cap + peak63C + stradC
  let maxM := 1 + (7 + maxG) / 101
  (3 * maxM + 2) + (fineFastSlabRootGroups cap + peak63C + stradC)

/-- Fast O(48) closed-form `stepReserve` upper bound under physical class cap `cap`. -/
def fineFastStepReserve (cap : Nat → Nat) (peak63C stradC maxReq : Nat) : Nat :=
  let maxG := fineFastSlabGroups cap + peak63C + stradC
  let maxM := 1 + (7 + maxG) / 101
  FineStepBound maxM maxReq

private theorem fastClassParams_props {sc : Nat} (hsc : sc < 48) :
    (fastClassParams sc).msn = maxSmallNestedGroups sc ∧
    (fastClassParams sc).isSt = isSteadyNestedClass sc ∧
    (fastClassParams sc).stCnt = steadyCnt sc ∧
    (fastClassParams sc).hasRt = hasRootPair sc ∧
    (fastClassParams sc).cmRt = cntMinRoot sc ∧
    (fastClassParams sc).maxRb = maxRootBytes sc ∧
    (fastClassParams sc).ceilRs = ceilRootPerSlot sc ∧
    (fastClassParams sc).snSum = ((List.range sc).map fun csc =>
      if canSmallNestIn csc sc then maxSmallNestedGroups csc else 0).sum ∧
    (sc ≤ 7 → (fastClassParams sc).snSum = 0) ∧
    (7 ≤ sc → (fastClassParams sc).isSt = false) ∧
    (∀ csc < 7, (steadyParent csc == sc && isSteadyNestedClass csc) = (fastSteadyParent csc == sc)) := by
  have h := List.all_eq_true.mp checkFastClassParams_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, ?_, ?_, ?_⟩
  · intro hle; have h1 := h.1.1.2; simp only [hle, ↓reduceIte, beq_iff_eq] at h1; exact h1
  · intro hge; have h1 := h.1.2; simp only [hge, ↓reduceIte, Bool.not_eq_true'] at h1; exact h1
  · intro csc hcsc
    have h1 := List.all_eq_true.mp h.2 csc (List.mem_range.mpr hcsc)
    exact beq_iff_eq.mp h1

private theorem sum_map_add_model {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x tl ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_map_zero_model {α : Type} (xs : List α) :
    (xs.map fun _ => 0).sum = 0 := by
  induction xs <;> simp [*]

private theorem fineChildNested_zero_of_le_seven (cap : Nat → Nat) {sc : Nat} (hsc : sc ≤ 7) :
    fineChildNested cap sc = 0 := by
  have hp := fastClassParams_props (sc := sc) (by omega)
  have hSn0 : ((List.range sc).map fun csc =>
      if canSmallNestIn csc sc then maxSmallNestedGroups csc else 0).sum = 0 := by
    rw [← hp.2.2.2.2.2.2.2.1]; exact hp.2.2.2.2.2.2.2.2.1 hsc
  have hNoPar : ((List.range 8).all fun s =>
      (List.range 7).all fun c => !(fastSteadyParent c == s)) = true := by decide +kernel
  unfold fineChildNested childNestedFrom
  refine Nat.eq_zero_of_le_zero ?_
  rw [sum_map_add_model]
  have h1 : ((List.range sc).map fun csc =>
      if canSmallNestIn csc sc then ((fineClassBounds cap).getD csc ClassFineBound.zero).gsn else 0).sum ≤ 0 := by
    refine Nat.le_trans
      (sum_map_le_model (g := fun csc => if canSmallNestIn csc sc then maxSmallNestedGroups csc else 0) fun csc hcsc => ?_)
      (by rw [hSn0]; exact Nat.le_refl 0)
    have hlt := List.mem_range.mp hcsc
    show (if canSmallNestIn csc sc then (fineClassEntry cap csc).gsn else 0) ≤
      if canSmallNestIn csc sc then maxSmallNestedGroups csc else 0
    rw [fineClassEntry_eq (by omega)]
    split
    · dsimp only [ClassFineBound.zero]
      split
      · exact Nat.zero_le _
      · exact Nat.le_refl _
    · exact Nat.le_refl 0
  have h2 : ((List.range sc).map fun csc =>
      if steadyParent csc == sc && isSteadyNestedClass csc then
        ((fineClassBounds cap).getD csc ClassFineBound.zero).gst
      else 0).sum ≤ 0 := by
    refine Nat.le_trans (sum_map_le_model (g := fun _ => 0) fun csc hcsc => ?_)
      (by rw [sum_map_zero_model]; exact Nat.le_refl 0)
    have hlt := List.mem_range.mp hcsc
    have hc7 : csc < 7 := by omega
    rw [hp.2.2.2.2.2.2.2.2.2.2 csc hc7]
    have hF := List.all_eq_true.mp
      (List.all_eq_true.mp hNoPar sc (List.mem_range.mpr (by omega)))
      csc (List.mem_range.mpr hc7)
    simp only [Bool.not_eq_true'] at hF
    simp [hF]
  omega

private theorem fineRawOcc_le_fast (cap : Nat → Nat) {sc : Nat} (hsc : sc < 48) :
    fineRawOcc cap sc ≤ fineFastOcc cap sc := by
  by_cases hle7 : sc ≤ 7
  · unfold fineRawOcc fineFastOcc
    dsimp only
    rw [fineChildNested_zero_of_le_seven cap hle7]
    omega
  · have hge8 : 7 < sc := by omega
    have hp := fastClassParams_props hsc
    unfold fineRawOcc fineFastOcc fineChildNested childNestedFrom
    rw [sum_map_add_model]
    have hSn : ((List.range sc).map fun csc =>
        if canSmallNestIn csc sc then ((fineClassBounds cap).getD csc ClassFineBound.zero).gsn else 0).sum ≤
        (fastClassParams sc).snSum := by
      refine Nat.le_trans
        (sum_map_le_model (g := fun csc => if canSmallNestIn csc sc then maxSmallNestedGroups csc else 0) fun csc hcsc => ?_)
        (by rw [← hp.2.2.2.2.2.2.2.1]; exact Nat.le_refl _)
      have hlt := List.mem_range.mp hcsc
      show (if canSmallNestIn csc sc then (fineClassEntry cap csc).gsn else 0) ≤
        if canSmallNestIn csc sc then maxSmallNestedGroups csc else 0
      rw [fineClassEntry_eq (by omega)]
      split
      · dsimp only [ClassFineBound.zero]
        split
        · exact Nat.zero_le _
        · exact Nat.le_refl _
      · exact Nat.le_refl 0
    let fSt : Nat → Nat := fun csc =>
      if steadyParent csc == sc && isSteadyNestedClass csc then
        ((fineClassBounds cap).getD csc ClassFineBound.zero).gst
      else 0
    have hRange : List.range sc = List.range 7 ++ (List.range (sc - 7)).map (7 + ·) := by
      rw [← List.range_add]; congr 1; omega
    have hSt : ((List.range sc).map fSt).sum ≤
        ((List.range 7).map fun csc =>
          if fastSteadyParent csc == sc then fineFastSteadyGst cap csc else 0).sum := by
      rw [hRange, List.map_append, List.sum_append]
      have hTail0 : (((List.range (sc - 7)).map (7 + ·)).map fSt).sum ≤ 0 := by
        refine Nat.le_trans (sum_map_le_model (g := fun _ => 0) fun csc hcsc => ?_)
          (by rw [sum_map_zero_model]; exact Nat.le_refl 0)
        rcases List.mem_map.mp hcsc with ⟨i, hi, rfl⟩
        have hiLt := List.mem_range.mp hi
        have hpC := fastClassParams_props (sc := 7 + i) (by omega)
        have hNotSt : isSteadyNestedClass (7 + i) = false :=
          hpC.2.1.symm.trans (hpC.2.2.2.2.2.2.2.2.2.1 (by omega))
        dsimp only [fSt]
        simp [hNotSt]
      have hHead : ((List.range 7).map fSt).sum ≤
          ((List.range 7).map fun csc =>
            if fastSteadyParent csc == sc then fineFastSteadyGst cap csc else 0).sum := by
        refine sum_map_le_model fun csc hcsc => ?_
        have hc7 := List.mem_range.mp hcsc
        dsimp only [fSt]
        rw [hp.2.2.2.2.2.2.2.2.2.2 csc hc7]
        split
        · show (fineClassEntry cap csc).gst ≤ fineFastSteadyGst cap csc
          have hpC := fastClassParams_props (sc := csc) (by omega)
          have hIsSt : isSteadyNestedClass csc = true := by
            have hAll : ((List.range 7).all isSteadyNestedClass) = true := by decide +kernel
            exact List.all_eq_true.mp hAll csc hcsc
          rw [fineClassEntry_eq (by omega)]
          unfold fineRawOcc fineFastSteadyGst
          rw [fineChildNested_zero_of_le_seven cap (by omega), Nat.add_zero, hpC.2.2.1, hIsSt]
          dsimp only
          split <;> exact Nat.le_refl _
        · exact Nat.le_refl 0
      omega
    dsimp only [fSt] at hSt
    dsimp only; omega

theorem fineClassEntry_le_fast (cap : Nat → Nat) {sc : Nat} (hsc : sc < 48) :
    (fineClassEntry cap sc).le (fineFastEntry cap sc) := by
  have hp := fastClassParams_props hsc
  have hOcc := fineRawOcc_le_fast cap hsc
  rw [fineClassEntry_eq hsc]
  unfold fineFastEntry
  dsimp only
  rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1]
  by_cases h0 : (fineRawOcc cap sc == 0) = true
  · simp only [h0, ↓reduceIte, ClassFineBound.le, ClassFineBound.zero]
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  · have hPos : 0 < fineRawOcc cap sc := by rw [beq_iff_eq] at h0; omega
    have h0' : (fineFastOcc cap sc == 0) = false := beq_false_of_ne (by omega)
    simp only [Bool.eq_false_iff.mpr h0, h0', Bool.false_eq_true, ↓reduceIte, ClassFineBound.le]
    refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
    · split
      · exact Nat.add_le_add_left (Nat.div_le_div_right hOcc) 1
      · exact Nat.le_refl 0
    · split
      · exact Nat.add_le_add_left (Nat.div_le_div_right hOcc) 1
      · exact Nat.le_refl 0
    · split
      · exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hOcc) _
      · exact Nat.le_refl 0


theorem fineSlabGroups_le_fast (cap : Nat → Nat) :
    fineSlabGroups cap ≤ fineFastSlabGroups cap := by
  rw [fineSlabGroups_eq_range]
  unfold fineFastSlabGroups
  refine sum_map_le_model fun sc hsc => ?_
  have h := fineClassEntry_le_fast cap (List.mem_range.mp hsc)
  exact Nat.add_le_add (Nat.add_le_add h.1 h.2.1) h.2.2.1

theorem fineSlabRootGroups_le_fast (cap : Nat → Nat) :
    fineSlabRootGroups cap ≤ fineFastSlabRootGroups cap := by
  rw [fineSlabRootGroups_eq_range]
  unfold fineFastSlabRootGroups
  exact sum_map_le_model fun sc hsc => (fineClassEntry_le_fast cap (List.mem_range.mp hsc)).2.2.1

theorem fineSlabRootBytes_le_fast (cap : Nat → Nat) :
    fineSlabRootBytes cap ≤ fineFastSlabRootBytes cap := by
  rw [fineSlabRootBytes_eq_range]
  unfold fineFastSlabRootBytes
  exact sum_map_le_model fun sc hsc => (fineClassEntry_le_fast cap (List.mem_range.mp hsc)).2.2.2

theorem fine_footprint_le_of_physCap {bgt : FineBudget} {cap : Nat → Nat}
    {live63B live63C peak63C stradC ovB : Nat}
    (hCap : ∀ sc < 48, peakPhysOfBudget bgt sc ≤ cap sc)
    (hL63B : bgt.live63Bytes ≤ live63B) (hL63C : bgt.live63Count ≤ live63C)
    (hP63C : bgt.peak63Count ≤ peak63C) (hStr : bgt.straddle63Cum ≤ stradC)
    (hOv : bgt.overAlignCum ≤ ovB) :
    mallocngFineCostModel.footprint bgt ≤
      fineFastFootprint cap live63B live63C peak63C stradC ovB := by
  show fineFootprint bgt ≤ _
  unfold fineFootprint fineFastFootprint fineMetaIvs fineMaxMetaAreas fineMaxGroups
  dsimp only
  have hSG := Nat.le_trans (fineSlabGroups_mono hCap) (fineSlabGroups_le_fast cap)
  have hSB := Nat.le_trans (fineSlabRootBytes_mono hCap) (fineSlabRootBytes_le_fast cap)
  have hDiv : (7 + (fineSlabGroups (peakPhysOfBudget bgt) + bgt.peak63Count + bgt.straddle63Cum)) / 101 ≤
      (7 + (fineFastSlabGroups cap + peak63C + stradC)) / 101 :=
    Nat.div_le_div_right (by omega)
  omega

theorem fine_maxDynIvs_le_of_physCap {bgt : FineBudget} {cap : Nat → Nat}
    {peak63C stradC : Nat}
    (hCap : ∀ sc < 48, peakPhysOfBudget bgt sc ≤ cap sc)
    (hP63C : bgt.peak63Count ≤ peak63C) (hStr : bgt.straddle63Cum ≤ stradC) :
    mallocngFineCostModel.maxDynIvs bgt ≤ fineFastMaxDynIvs cap peak63C stradC := by
  show fineMaxDynIvs bgt ≤ _
  unfold fineMaxDynIvs fineFastMaxDynIvs fineMetaIvs fineMaxMetaAreas fineMaxGroups fineMaxRootGroups
  dsimp only
  have hSG := Nat.le_trans (fineSlabGroups_mono hCap) (fineSlabGroups_le_fast cap)
  have hSR := Nat.le_trans (fineSlabRootGroups_mono hCap) (fineSlabRootGroups_le_fast cap)
  have hDiv : (7 + (fineSlabGroups (peakPhysOfBudget bgt) + bgt.peak63Count + bgt.straddle63Cum)) / 101 ≤
      (7 + (fineFastSlabGroups cap + peak63C + stradC)) / 101 :=
    Nat.div_le_div_right (by omega)
  omega

theorem fine_stepReserve_le_of_physCap {ev : AllocEvent} {bgt : FineBudget} {cap : Nat → Nat}
    {peak63C stradC maxReq : Nat}
    (hCap : ∀ sc < 48, peakPhysOfBudget bgt sc ≤ cap sc)
    (hP63C : bgt.peak63Count ≤ peak63C) (hStr : bgt.straddle63Cum ≤ stradC)
    (hReq : evReqBytes ev ≤ maxReq) :
    mallocngFineCostModel.stepReserve ev bgt ≤
      fineFastStepReserve cap peak63C stradC maxReq := by
  show fineStepReserve ev bgt ≤ _
  unfold fineStepReserve fineFastStepReserve fineMaxMetaAreas fineMaxGroups
  dsimp only
  have hSG := Nat.le_trans (fineSlabGroups_mono hCap) (fineSlabGroups_le_fast cap)
  exact FineStepBound_mono
    (Nat.add_le_add_left (Nat.div_le_div_right (by omega)) 1) hReq

/-! ## 5. Benchmark Envelope Checks (TidwallBtree & Hashbrown) -/

/-- TidwallBtree S2 envelope (`24,400` blocks in `sc = 32` + `2,600` in `sc = 33`, `≤ 4` driver
    buffers in any class with `reallocPeakByNom ≤ 4`, `align ≤ 16` so `excCap = 0`, `≤ 4` large
    blocks `≤ 80 MiB`): dynamic footprint `< 360 MiB < 380 MiB` even under arbitrary `realloc` churn. -/
theorem fine_tidwallBtree_footprint_lt_380MiB :
    let nomCap := fun sc => if sc == 32 then 24404 else if sc == 33 then 2604 else if sc < 48 then 4 else 0
    let rpeakCap := fun sc => if sc < 48 then 4 else 0
    let excCap := fun _ => 0
    fineFastFootprint (physCapOfNom nomCap rpeakCap excCap) (80 * 1048576) 4 32 0 0 < 380 * 1048576 := by
  dsimp only
  apply decide_eq_true_eq.mp
  decide +kernel

/-- Hashbrown S2 `2.6e6` `16`-byte blocks (`nomSc 16 = 1`, `110 MiB` live `RawTable`/stdio,
    `≤ 32` large peak, `align ≤ 16` so `excCap = 0`): dynamic footprint `< 210 MiB < 250 MiB`, and
    48-bit `VaRoom` holds at `maxReq = 105 MiB`. -/
theorem fine_hashbrown_16B_footprint_lt_250MiB :
    let nomCap := fun sc => if sc == 1 then 2600000 else 0
    let rpeakCap := fun _ => 0
    let excCap := fun _ => 0
    let cap := physCapOfNom nomCap rpeakCap excCap
    fineFastFootprint cap (110 * 1048576) 4 32 0 0 < 250 * 1048576 ∧
    VaRoom (133 * 1048576 + fineFastFootprint cap (216 * 1048576) 8 32 0 0)
      (51 + fineFastMaxDynIvs cap 32 0)
      (fineFastStepReserve cap 32 0 (105 * 1048576)) := by
  dsimp only
  unfold VaRoom
  apply decide_eq_true_eq.mp
  decide +kernel

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit -- proof-setup: allow-public-import

/-!
# Leaf Allocation and Cancellation Helpers for W2 `message_decrypt`

Symbolic `[HasFineReallocCredit M]` bounds for single allocations, deallocations, paired
`alloc ++ dealloc` cancellation, and Segment 8 (`AesDecCtEnv` AES-256-CBC output `Vec<u8>`) in
W2 `message_decrypt`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
  stepEvents_rustAlloc_large stepEvents_rustAlloc_small
  stepEvents_rustDealloc_large stepEvents_rustDealloc_small
)

/-! ## 1. Single-Allocation Charge Projections -/

/-- Symbolic `cumSmall` charge of a single `rustAllocEvents req al` (`0 < req`, `al ≤ 16`). -/
@[expose] def singleAllocCum (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req ≤ HasFineReallocCredit.smallMaxReq M then
    HasFineReallocCredit.smallAllocCost M req
  else
    HasFineReallocCredit.largeMetaCost M

/-- Symbolic `liveLarge` / `peakLarge` charge of a single `rustAllocEvents req al` (`al ≤ 16`). -/
@[expose] def singleAllocLarge (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req ≤ HasFineReallocCredit.smallMaxReq M then
    0
  else
    HasFineReallocCredit.largeCost M req

theorem singleAllocCum_eq_small (M : AllocCostModel) [HasFineReallocCredit M]
    {req : Nat} (hle : req ≤ HasFineReallocCredit.smallMaxReq M) :
    singleAllocCum M req = HasFineReallocCredit.smallAllocCost M req := by
  simp [singleAllocCum, hle]

/-! ## 2. `rustAllocEvents`, `rustDeallocEvents`, and `alloc ++ dealloc` Cancellation -/

theorem stepEvents_rustAlloc_any (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (st : M.σ) (hal : al ≤ 16) (hpos : 0 < req) :
    let st' := M.stepEvents (rustAllocEvents req al) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + singleAllocCum M req ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + singleAllocLarge M req ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + singleAllocLarge M req) := by
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · rcases stepEvents_rustAlloc_small M st hal hpos hle with ⟨hc, hl, hp⟩
    simp only [singleAllocCum, singleAllocLarge, hle, ↓reduceIte, Nat.add_zero]
    exact ⟨hc, hl, by omega⟩
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hle
    rcases stepEvents_rustAlloc_large M st hal hgt with ⟨hc, hl, hp⟩
    simp only [singleAllocCum, singleAllocLarge, hle, ↓reduceIte]
    exact ⟨hc, hl, hp⟩

theorem stepEvents_rustDealloc_noninc (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (st : M.σ) (hal : al ≤ 16) :
    let st' := M.stepEvents (rustDeallocEvents req al) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · exact stepEvents_rustDealloc_small M st hal hle
  · rcases stepEvents_rustDealloc_large M st hal (Nat.lt_of_not_ge hle) with ⟨hc, hl, hp⟩
    exact ⟨hc, Nat.le_trans hl (Nat.sub_le _ _), hp⟩

/-- Paired `rustAllocEvents req al ++ rustDeallocEvents req al` cancels any `sc = 63` large charge back to `liveLarge st`.
-/
theorem stepEvents_rustAlloc_dealloc_cancel (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (st : M.σ) (hal : al ≤ 16) (hpos : 0 < req) :
    let st' := M.stepEvents (rustAllocEvents req al ++ rustDeallocEvents req al) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + singleAllocCum M req ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + singleAllocLarge M req) := by
  dsimp only
  rw [M.stepEvents_append]
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · rcases stepEvents_rustAlloc_small M (al := al) st hal hpos hle with ⟨hc1, hl1, hp1⟩
    rcases stepEvents_rustDealloc_small M (req := req) (al := al)
        (M.stepEvents (rustAllocEvents req al) st) hal hle with ⟨hc2, hl2, hp2⟩
    simp only [singleAllocCum, singleAllocLarge, hle, ↓reduceIte, Nat.add_zero]
    exact ⟨by omega, by omega, by omega⟩
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hle
    rcases stepEvents_rustAlloc_large M (al := al) st hal hgt with ⟨hc1, hl1, hp1⟩
    rcases stepEvents_rustDealloc_large M (req := req) (al := al)
        (M.stepEvents (rustAllocEvents req al) st) hal hgt with ⟨hc2, hl2, hp2⟩
    simp only [singleAllocCum, singleAllocLarge, hle, ↓reduceIte]
    exact ⟨by omega, by omega, by omega⟩

/-! ## 3. W2 Segment 8 (`AesDecCtEnv`) Credit Bounds -/

end LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak

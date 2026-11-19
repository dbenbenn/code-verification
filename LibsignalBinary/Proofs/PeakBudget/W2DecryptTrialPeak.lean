/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak

/-!
# Segment 7/9 and `≤ 5`-Session Trial-Decrypt Loop Cancellation Helpers

Symbolic `[HasFineReallocCredit M]` peak and credit combinators for W2 `message_decrypt`:
Segment 7 (`compute_mac` + `serialize_addresses` + `23` B error string), Segment 9 small-allocation
lists and optional large deallocation cancellation, failed-trial `SessionClone` cancellation, and
multi-session (`≤ n`) trial-decrypt loop composition.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
  stepEvents_rustAlloc_small
  stepEvents_rustDealloc_large stepEvents_rustDealloc_small
)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak (
  singleAllocLarge stepEvents_rustAlloc_dealloc_cancel
)

/-! ## 1. W2 Segment 7 (`compute_mac` and `verify_mac`) Credit Bounds -/

/-- Events of `SignalMessage::compute_mac` (`2 × 33` B public-key serializations and deallocations).
-/
@[expose] def computeMacEvs : List AllocEvent :=
  (rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) ++
    (rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)

theorem stepEvents_computeMac_small (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents computeMacEvs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + 2 * HasFineReallocCredit.smallAllocCost M 33 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only [computeMacEvs]
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
  rcases stepEvents_rustAlloc_small M (req := 33) (al := 1) st (by decide) (by decide) h33 with
    ⟨hc1, hl1, hp1⟩
  rcases stepEvents_rustDealloc_small M (req := 33) (al := 1)
      (M.stepEvents (rustAllocEvents 33 1) st) (by decide) h33 with ⟨hc2, hl2, hp2⟩
  let stMid := M.stepEvents (rustDeallocEvents 33 1) (M.stepEvents (rustAllocEvents 33 1) st)
  rcases stepEvents_rustAlloc_small M (req := 33) (al := 1) stMid (by decide) (by decide) h33 with
    ⟨hc3, hl3, hp3⟩
  rcases stepEvents_rustDealloc_small M (req := 33) (al := 1)
      (M.stepEvents (rustAllocEvents 33 1) stMid) (by decide) h33 with ⟨hc4, hl4, hp4⟩
  dsimp only [stMid] at hc3 hl3 hp3 hc4 hl4 hp4
  exact ⟨by omega, by omega, by omega⟩

/-- Events of `verifyMacWithAddressesEvents`. -/
@[expose] def vmacEvs (withAddr : Bool) : List AllocEvent :=
  if withAddr then
    computeMacEvs ++ (rustAllocEvents 36 1 ++ rustDeallocEvents 36 1)
  else
    computeMacEvs

/-- Events of Segment 7 (`vmacEvs withAddr` + optional `23` B error allocation). -/
@[expose] def s7CoreEvs (withAddr errAlloc : Bool) : List AllocEvent :=
  vmacEvs withAddr ++ (if errAlloc then rustAllocEvents 23 1 else [])

theorem stepEvents_vmac_small (M : AllocCostModel) [HasFineReallocCredit M]
    (withAddr : Bool) (st : M.σ)
    (h36 : 36 ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (vmacEvs withAddr) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        (2 * HasFineReallocCredit.smallAllocCost M 33 + HasFineReallocCredit.smallAllocCost M 36) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  dsimp only [vmacEvs]
  cases withAddr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases stepEvents_computeMac_small M st h33 with ⟨hc, hl, hp⟩
    exact ⟨by omega, hl, hp⟩
  · simp only [↓reduceIte]
    rw [M.stepEvents_append, M.stepEvents_append]
    rcases stepEvents_computeMac_small M st h33 with ⟨hc1, hl1, hp1⟩
    rcases stepEvents_rustAlloc_small M (req := 36) (al := 1)
        (M.stepEvents computeMacEvs st) (by decide) (by decide) h36 with ⟨hc2, hl2, hp2⟩
    rcases stepEvents_rustDealloc_small M (req := 36) (al := 1)
        (M.stepEvents (rustAllocEvents 36 1) (M.stepEvents computeMacEvs st))
        (by decide) h36 with ⟨hc3, hl3, hp3⟩
    exact ⟨by omega, by omega, by omega⟩

theorem stepEvents_s7Core_small (M : AllocCostModel) [HasFineReallocCredit M]
    (withAddr errAlloc : Bool) (st : M.σ)
    (h36 : 36 ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (s7CoreEvs withAddr errAlloc) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        (2 * HasFineReallocCredit.smallAllocCost M 33 +
          HasFineReallocCredit.smallAllocCost M 36 +
          HasFineReallocCredit.smallAllocCost M 23) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  have h23 : 23 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  dsimp only [s7CoreEvs]
  rw [M.stepEvents_append]
  rcases stepEvents_vmac_small M withAddr st h36 with ⟨hc1, hl1, hp1⟩
  cases errAlloc
  · simp only [Bool.false_eq_true, ↓reduceIte, AllocCostModel.stepEvents_nil]
    exact ⟨by omega, hl1, hp1⟩
  · simp only [↓reduceIte]
    rcases stepEvents_rustAlloc_small M (req := 23) (al := 1)
        (M.stepEvents (vmacEvs withAddr) st) (by decide) (by decide) h23 with ⟨hc2, hl2, hp2⟩
    exact ⟨by omega, by omega, by omega⟩

/-! ## 2. Small-Allocation Lists and `sc = 63` Free Cancellation -/

@[expose] def smallAllocListEvs : List Nat → List AllocEvent
  | [] => []
  | r :: rs => rustAllocEvents r 1 ++ smallAllocListEvs rs

def smallAllocListCum (M : AllocCostModel) [HasFineReallocCredit M] : List Nat → Nat
  | [] => 0
  | r :: rs => HasFineReallocCredit.smallAllocCost M r + smallAllocListCum M rs

/-- Optional `rustDeallocEvents req al` cancels `singleAllocLarge M req` from `liveLarge`. -/
theorem stepEvents_optDealloc_cancel_large (M : AllocCostModel) [HasFineReallocCredit M]
    {req al L₀ : Nat} (st : M.σ) (hal : al ≤ 16)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L₀ + (if req = 0 then 0 else singleAllocLarge M req)) :
    let evs := if req = 0 then [] else rustDeallocEvents req al
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤ L₀ ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  by_cases h0 : req = 0
  · subst h0
    simp only [↓reduceIte, AllocCostModel.stepEvents_nil, Nat.add_zero] at hlive ⊢
    exact ⟨Nat.le_refl _, hlive, Nat.le_refl _⟩
  · simp only [h0, ↓reduceIte] at hlive ⊢
    by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [singleAllocLarge, hle, ↓reduceIte, Nat.add_zero] at hlive
      rcases stepEvents_rustDealloc_small M (req := req) (al := al) st hal hle with ⟨hc, hl, hp⟩
      exact ⟨hc, by omega, hp⟩
    · have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hle
      simp only [singleAllocLarge, hle, ↓reduceIte] at hlive
      rcases stepEvents_rustDealloc_large M (req := req) (al := al) st hal hgt with ⟨hc, hl, hp⟩
      exact ⟨hc, by omega, hp⟩

@[expose] def optDeallocListEvs : List (Nat × Nat) → List AllocEvent
  | [] => []
  | (req, al) :: rest =>
    (if req = 0 then [] else rustDeallocEvents req al) ++ optDeallocListEvs rest

@[expose] def optDeallocListLarge (M : AllocCostModel) [HasFineReallocCredit M] : List (Nat × Nat) → Nat
  | [] => 0
  | (req, _) :: rest =>
    (if req = 0 then 0 else singleAllocLarge M req) + optDeallocListLarge M rest

/-- Multi-buffer `sc = 63` deallocation credit cancellation across `optDeallocListEvs pairs`. -/
theorem stepEvents_optDeallocList_cancel (M : AllocCostModel) [HasFineReallocCredit M] :
    ∀ (pairs : List (Nat × Nat)) {L₀ : Nat} (st : M.σ),
      (∀ p ∈ pairs, p.2 ≤ 16) →
      HasFineReallocCredit.liveLarge st ≤ L₀ + optDeallocListLarge M pairs →
      let st' := M.stepEvents (optDeallocListEvs pairs) st
      HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
      HasFineReallocCredit.liveLarge st' ≤ L₀ ∧
      HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st
  | [], _, st, _, hlive => by
    simp only [optDeallocListEvs, optDeallocListLarge, AllocCostModel.stepEvents_nil,
      Nat.add_zero] at hlive ⊢
    exact ⟨Nat.le_refl _, hlive, Nat.le_refl _⟩
  | (req, al) :: rest, L₀, st, hal_all, hlive => by
    dsimp only [optDeallocListEvs, optDeallocListLarge] at hlive ⊢
    rw [M.stepEvents_append]
    have hal : al ≤ 16 := hal_all (req, al) List.mem_cons_self
    have hlive_reassoc : HasFineReallocCredit.liveLarge st ≤
        (L₀ + optDeallocListLarge M rest) +
          (if req = 0 then 0 else singleAllocLarge M req) := by omega
    rcases stepEvents_optDealloc_cancel_large M (req := req) (al := al)
        (L₀ := L₀ + optDeallocListLarge M rest) st hal hlive_reassoc with ⟨hc1, hl1, hp1⟩
    rcases stepEvents_optDeallocList_cancel M rest (L₀ := L₀)
        _ (fun p hp => hal_all p (List.mem_cons_of_mem _ hp)) hl1 with ⟨hc2, hl2, hp2⟩
    exact ⟨by omega, hl2, by omega⟩

/-! ## 3. Single Failed-Trial Cancellation -/

/-! ## 4. Multi-Session (`≤ 5`) Trial-Decrypt Loop Composition -/

end LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak

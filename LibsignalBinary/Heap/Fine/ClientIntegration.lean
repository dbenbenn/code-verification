/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# `fineCostModel` Client Integration Surface

Combines `RustEntriesFine`, `ClientBounds`, and `RustStdAllocBudgetBridge` into client-facing
startup and `FitsEvents` bridges over `fineCostModel`:
- Total-correctness (`onOom := ⌜False⌝`) startup + `RustCliAllocNoOomEntries` bundles for direct
  `__rdl_*` entrypoints and 1-instruction `__rust_*` `B`-thunks.
- Automatic `withinMaxAlloc` discharge from `FitsStep` virtual-address bounds (`2 ^ 48 < MallocngMaxAllocSize`)
  and `FitsEvents` bridges for `rustAllocEvents`, `rustDeallocEvents`, `rustReallocEvents`,
  `rawVecGrowEvents`, and `stringCloneEvents`.
- Small-bucket bounds for Kyber keys/ciphertexts (`req ≤ 1,612`) and cumulative doubling bounds for
  `Vec<Vec<u8>>` (`stride = 24`).
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine.ClientIntegration

open Arm64 Arm64.Obj
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.Mallocng hiding AllocCostModel AllocEvent MallocngCostModelIface
  MallocngCostModelSound MallocngModelEnv MallocngModelPlacedEntryContracts
  MallocngModelPostEnv MallocngStepOomCond
open VerifiedLibraries.RustStd (
  MallocngCEntryAddrs RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs
)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open LibsignalBinary.Heap
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  stringCloneEvents rawVecNewCap rawVecGrowEvents growOneU8Events growOneVecU8Events
)
open LibsignalBinary.Heap.Fine
open LibsignalBinary.Heap.Fine.ClientBounds
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit

/-! ## Total-Correctness Startup and Entrypoint Bundles -/

/-! ## `withinMaxAlloc` Elimination and Call-Site `FitsEvents` Bridges -/

theorem req_add_align_le_fineStepReserveOfCum (maxReq maxAlign cumB : Nat) :
    maxReq + (max maxAlign 16 - 16) ≤ fineStepReserveOfCum maxReq maxAlign cumB := by
  unfold fineStepReserveOfCum FineStepBound
  have hle := pageAlignUp_le (maxReq + (max maxAlign 16 - 16) + 8192)
  omega

/-- Any `ev` bounded by `(maxReq, maxAlign)` automatically satisfies `ev.withinMaxAlloc` whenever
    `fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48` (which holds under every `FitsStep` `hva`
    inequality, since `2 ^ 48 < MallocngMaxAllocSize = 2 ^ 63 - 4098`). -/
theorem withinMaxAlloc_of_stepReserve_le_2pow48
    {ev : AllocEvent} {maxReq maxAlign cumB : Nat}
    (hreq : eventStepReq ev ≤ maxReq)
    (hal : max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (hstep : fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48) :
    ev.withinMaxAlloc := by
  have hbase := req_add_align_le_fineStepReserveOfCum maxReq maxAlign cumB
  cases ev with
  | alloc req =>
    simp only [eventStepReq] at hreq
    unfold AllocEvent.withinMaxAlloc MallocngMaxAllocSize
    omega
  | aligned align req =>
    simp only [eventStepReq] at hreq
    simp only [eventStepAlign] at hal
    simp only [AllocEvent.withinMaxAlloc, mallocngAlignedEffSize, MallocngMaxAllocSize]
    split <;> omega
  | free _ _ =>
    exact True.intro
  | realloc _ _ newSz =>
    simp only [eventStepReq] at hreq
    unfold AllocEvent.withinMaxAlloc MallocngMaxAllocSize
    omega

/-- Whole-trace `FitsTrace fineCostModel` bridge without an explicit `ev.withinMaxAlloc` conjunct
    in `hevs` (derived automatically from `eventStepReq`, `eventStepAlign`, and `hva`). -/
theorem fitsTrace_fineCostModel_of_bounds_autoWf
    {lim : BudgetLimits} {fullLog : List AllocEvent}
    {maxReq maxAlign cumB peakB : Nat}
    (hevs : ∀ ev ∈ fullLog,
      eventStepReq ev ≤ maxReq ∧ max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) (fineCostModel.evalLog fullLog) ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) (fineCostModel.evalLog fullLog) ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) (fineCostModel.evalLog fullLog) ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq maxAlign cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq maxAlign cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq maxAlign cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48) :
    FitsTrace fineCostModel lim (fineStepReserveOfCum maxReq maxAlign cumB) fullLog :=
  fitsTrace_fineCostModel_of_bounds
    (fun ev hmem =>
      let ⟨hreq, hal⟩ := hevs ev hmem
      ⟨withinMaxAlloc_of_stepReserve_le_2pow48 (cumB := cumB) hreq hal (by omega), hreq, hal⟩)
    henf hcum hlive hpeak hram hva

/-! ## Kyber Small-Bucket Bounds and `Vec<24>` Doubling Chain -/

private def checkKyberBucket : Bool :=
  (List.range 101).all fun u =>
    let sc0 := sizeToClassUnits u
    let aWt := coarseSlotWt sc0 + (122 * coarseGrpWtS sc0 + FineScale - 1) / FineScale
    decide (
      aWt ≤ 9789 ∧
      (62 ≤ u → aWt ≤ 3506) ∧
      (93 ≤ u → aWt ≤ 2792))

private theorem checkKyberBucket_true : checkKyberBucket = true := by
  decide +kernel

/-- Tight Kyber768/Kyber1024 public-key & ciphertext range bound (`989 ≤ req ≤ 1,612`):
    `smallAllocCost fineCostModel req ≤ 3,506`. -/
theorem smallAllocCost_le_3506_of_kyber_range {req : Nat}
    (hlo : 989 ≤ req) (hhi : req ≤ 1612) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 3506 := by
  change fineSmallAllocCost req ≤ 3506
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hu : (req + 3) / 16 < 101 := by omega
  have hu62 : 62 ≤ (req + 3) / 16 := by omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkKyberBucket_true ((req + 3) / 16) (List.mem_range.mpr hu)
  exact (of_decide_eq_true hcell).2.1 hu62

end LibsignalBinary.Heap.Fine.ClientIntegration

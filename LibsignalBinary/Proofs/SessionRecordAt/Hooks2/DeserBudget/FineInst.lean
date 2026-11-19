/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.CreditInst
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget

/-!
# Concrete `fineCostModel` Specialization of `DeserBudget`

Instantiates the parametric `[HasFineReallocCredit M]` deserialization, `SessionStructure`
drop-glue, and `2 MiB` wire-slice envelope theorems at `M := fineCostModel`
(`smallMaxReq = 135,167`, `largeCost req = req + 8,195`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineInst

open Arm64 ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks withLsCodeLoaded lsmpl blkPC_6 blkPl_6
)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (blkPl_46 lsProg_46)
open Symbolic.Swarm.TRREF.B3Defs (NonEmptyV1Q DeserializeScopeP_Q)
open LibsignalBinary.Heap (BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (
  FineBudget fineCostModel fineSmallMaxReq fineLargeCost declCost63
  fineCumSmall fineLiveLarge finePeakLarge
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  ssLargeLive ssClonePeakLarge
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  AllocContractsBudgetPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget (
  sessDeserLargeLive sessDeserPeakLarge
  sessDeserLargeLive_le_of_encode_le_2MiB sessDeserPeakLarge_le_of_encode_le_2MiB
  sessDeserLargeLive_le_universal_envelope sessDeserPeakLarge_le_universal_envelope
  sessDeserializeBudgetPlacedSpec
  sessDeserialize_budget_placed_ok sessDeserialize_budget_placed_ok_of_sub
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget (
  dropSessionStructureLocal1BudgetSpecX
  drop_session_structure_local1_budget_placed_ok
  liveLarge_after_dropSessionStructureLocal1_le
  fromRecord_clone_and_drop_budget_bounds
)

/-- Per-allocation `sc = 63` `mmap` page-rounding overhead constant (`8,195` B) in `fineCostModel`. -/
abbrev fineCLarge : Nat := 8195

theorem fineCostModel_smallMaxReq_ge :
    1024 * 104 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  change 1024 * 104 ≤ fineSmallMaxReq
  decide

theorem fineCostModel_largeCost_le (req : Nat)
    (_hgt : HasFineReallocCredit.smallMaxReq fineCostModel < req) :
    HasFineReallocCredit.largeCost fineCostModel req ≤ req + fineCLarge := by
  change fineLargeCost req ≤ req + 8195
  unfold fineLargeCost declCost63
  omega

/-- Concrete `fineCostModel` post-deserialize `sc = 63` live byte bound (`≤ 3,211,282` B) on
`DeserializeScopeP_Q NonEmptyV1Q` for any wire slice `|encodeRecord r| ≤ 2 ^ 21`. -/
theorem sessDeserLargeLive_fine_le_of_encode_le_2MiB
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (hlen : (encodeRecord r).length ≤ 2 ^ 21) :
    sessDeserLargeLive fineCostModel r ≤ 3211282 := by
  have h := sessDeserLargeLive_le_of_encode_le_2MiB fineCostModel
    (cLarge := fineCLarge) (by decide)
    fineCostModel_smallMaxReq_ge fineCostModel_largeCost_le hr hlen
  omega

/-- Concrete `fineCostModel` transient `realloc` peak `sc = 63` byte bound (`≤ 5,316,629` B) on
`DeserializeScopeP_Q NonEmptyV1Q` for any wire slice `|encodeRecord r| ≤ 2 ^ 21`. -/
theorem sessDeserPeakLarge_fine_le_of_encode_le_2MiB
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (hlen : (encodeRecord r).length ≤ 2 ^ 21) :
    sessDeserPeakLarge fineCostModel r ≤ 5316629 := by
  have h := sessDeserPeakLarge_le_of_encode_le_2MiB fineCostModel
    (cLarge := fineCLarge) (by decide)
    fineCostModel_smallMaxReq_ge fineCostModel_largeCost_le hr hlen
  omega

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineInst

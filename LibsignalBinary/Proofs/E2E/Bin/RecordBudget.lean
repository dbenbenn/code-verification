/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.CodeLayout

/-!
# Budget-Threaded `SessionRecord` Codec Contracts

Budget-threaded (`RustCliAllocBudget M`) contracts for `SessionRecord::deserialize`
(`recordDeserializeSpec`) and `SessionRecord::serialize` (`recordSerializeSpec`), small-regime
`PhaseCreditSpec` bounds, and 1 GiB non-vacuity witnesses.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Bin.RecordBudget

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (mallocngAlignedEffSize MallocngMaxAllocSize)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.E2E.Record (lenField encodeRecord)
open CryptoVerification.E2E.Record.Serialization (
  encSessionMem encRecordMem CanonRecord encRecordMem_eq_of_canon
)
open CryptoVerification.E2E.Record.Serialization.SessionLenAux (
  lenField_length bytesField_rootKey_length encSessionMem_length_eq
)
open CryptoVerification.E2E.Bin (RecordDeserializeGhost RecordSerializeGhost)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Heap.Fine (FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (
  eventStepReq eventStepAlign
  fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineStepReserveOfCum
  fineCostModel_smallMaxReq_eq smallAllocCost_le_add_26365 smallReallocCost_le_add_26365
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (
  freeOnly_fineCostModel fineCostModel_modelHyps
  fitsEnv_fineCostModel_of_phaseCredit nonVacLimits
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  BoundedRustEvs SerializeEnv
)
open LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget (
  RecordDeserializeEnv recordDeserializeEnv_fitsEnv_of_len_le
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerializeEnvX)

/-! ## Budget-Threaded `recordDeserializeSpec` and `recordSerializeSpec` -/

/-- Budget-threaded `SessionRecord::deserialize` contract (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`)
    over `RecordDeserializeEnv (encodeRecord ⟨some x.s⟩)`. -/
@[expose] def recordDeserializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (RecordDeserializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (RecordDeserializeEnv (encodeRecord ⟨some x.s⟩))⌝ ∗
      (CryptoVerification.E2E.Bin.recordDeserializeSpec (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜RecordDeserializeEnv (encodeRecord ⟨some x.s⟩) evs⌝ ∗
      (CryptoVerification.E2E.Bin.recordDeserializeSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded `SessionRecord::serialize` contract (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`)
    over `SerializeEnvX x.g x.r`. -/
@[expose] def recordSerializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (RecordSerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (SerializeEnvX x.g x.r)⌝ ∗
      (CryptoVerification.E2E.Bin.recordSerializeSpec (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜SerializeEnvX x.g x.r evs⌝ ∗
      (CryptoVerification.E2E.Bin.recordSerializeSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-! ## Small-Regime `PhaseCreditSpec` and Non-Vacuity Witnesses -/

private theorem eventStepReq_le_reqBytes (ev : AllocEvent) :
    eventStepReq ev ≤ ev.reqBytes := by
  cases ev with
  | alloc req => exact Nat.le_refl req
  | aligned al req =>
    simp only [eventStepReq, AllocEvent.reqBytes, mallocngAlignedEffSize]
    split <;> omega
  | free _ _ => exact Nat.le_refl 0
  | realloc _ _ newSz => exact Nat.le_refl newSz

def witnessSession : Session (List (BitVec 8)) where
  state := {
    sessionVersion := 4#32
    localIdentity := ⟨⟨List.replicate 32 0#8, by decide⟩⟩
    remoteIdentity := none
    rootKey := 0#256
    previousCounter := 0#32
    senderChain := none
    receiverChains := []
    pendingPreKey := false
    pqRatchetState := []
  }
  pendingPreKey := none
  pendingKyberPreKey := none
  localRegistrationId := 1#32
  remoteRegistrationId := 2#32
  aliceBaseKey := []

def witnessSessionGhost : SessionGhost where
  localIk := ⟨33#64, 8#64, witnessSession.state.localIdentity.serialize⟩
  remoteIk := ⟨0#64, 1#64, []⟩
  root := ⟨32#64, 128#64⟩
  chainsCap := 0#64
  chainsPtr := 8#64
  chains := []
  alice := ⟨0#64, 1#64, []⟩
  pq := ⟨0#64, 1#64⟩
  sender := none
  pending := none
  kyber := none
  regIds := List.replicate 8 0#8

end LibsignalBinary.Proofs.E2E.Bin.RecordBudget

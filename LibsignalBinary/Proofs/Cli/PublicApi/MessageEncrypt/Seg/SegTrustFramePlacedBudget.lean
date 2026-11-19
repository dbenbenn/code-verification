/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Budget-Threaded Relocatable Poll Buffer and Seam Frame Bundles for `segTrust`

Adapts the `SegTrustFramePlaced` seam frame bundles to `RustCliAllocBudget M` via `A.atState` for
use in `segTrust_placed_okV`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (SessionState OutgoingTripleRatchet IdentityKey)
open CryptoGames.LibsignalSessionApi (Session CiphertextMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (
  WithStoresEncGhost takenRecord cmSlots cmScratch encSpillsAtV encSubStack encSubStackV
  withStoresEncStackV
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails (dropRecordSlots)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (trustPollRest)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt (encCommonPlaced encStoreExtraPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (
  cliEncCommonRest cliTrustPassive encCommonPlaced_eq trustBaseActivePlaced
  seam_mem_split_placed seam_mem_to_tail_placed trustActivePlaced
  trustBaseActive_join_extra_placed trustActive_split_extra_placed trustPollPlacedOut_words
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  retagSessionStore retagIdentityStore
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

export CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (
  cliEncCommonRest cliTrustPassive encCommonPlaced_eq trustBaseActivePlaced seam_mem_split_placed
)
export CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (
  seam_mem_to_tail_placed trustActivePlaced trustBaseActive_join_extra_placed
  trustActive_split_extra_placed trustPollPlacedOut_words
)

theorem cliTrustPassive_atState [LibsignalPlacement] {M : AllocCostModel}
    (ss_vt id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) (draws : Nat) (s0 : State) :
    cliTrustPassive ss_vt id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' m draws s0 =
      cliTrustPassive ss_vt id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0 := rfl

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlacedBudget

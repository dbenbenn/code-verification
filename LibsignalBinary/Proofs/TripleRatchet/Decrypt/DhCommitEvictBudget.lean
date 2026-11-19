/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas

/-!
# Budget-Threaded Receiver-Chain Eviction Loop Invariant

Defines the budget-threaded receiver-chain eviction loop invariants `evictActive` and `evictActiveX`
over `RustCliAllocBudget M`, along with `VmPreserved` transport lemmas.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvictBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification.RustHeap (vecBuf)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack dropChainStackX)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)

/-- Budget-threaded receiver-chain eviction loop invariant (`dropChainStack = 48 + allocHookStack`). -/
@[expose] def evictActive {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) : SepProp :=
  ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
  ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
  vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
  memRegion (sp + 0x190#64) 104 ∗
  memRegion (sp + 0x500#64) 96 ∗
  A.pool lim st s ∗
  stackAt sp dropChainStack

/-- Budget-threaded receiver-chain eviction loop invariant (`dropChainStackX = 48 + extHookStack`). -/
@[expose] def evictActiveX {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) : SepProp :=
  ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
  ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
  vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
  memRegion (sp + 0x190#64) 104 ∗
  memRegion (sp + 0x500#64) 96 ∗
  A.pool lim st s ∗
  stackAt sp dropChainStackX

/-- Definitional bridge to `DhCommit.evictActive (A.atState lim st s)`. -/
theorem evictActive_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    evictActive A lim st s sp chainsCap chainsPtr gcs =
      CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.evictActive
        (A.atState lim st s) sp chainsCap chainsPtr gcs :=
  rfl

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvictBudget

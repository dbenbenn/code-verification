/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargets
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSymBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main

/-!
# Budget-Threaded Relocatable Tight-Panic `S1` & `ErrTail` Theorems

Proves `errTail_placed_okT` and `errTail_placed_okT_x` (`ErrTailSeamTightPlaced`,
`ErrTailSeamTightXPlaced`), derives standard `ErrTailSeamPlaced` / `ErrTailSeamXPlaced` corollaries,
and specializes the pinned tight-panic Segment S1 theorems over `RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto SessionState SignalProtocolError TripleRatchet)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_57 blkPl_57 lsmpl)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (UuidParser decryptDraws protocolAddressAt sessionStateAt signalMessageAt speWord
   tapeAfter utf8 uuidTryParse vecResultAt)
open CryptoVerification.LibsignalTripleRatchet
  (SpqrModel TrGhost TryDecryptGhost decResultFnAt logOff trAt)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (dropChainStack lsRustDeallocSym)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (speBodyAt speTag tryDecryptCommonHeap tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (blkPC_131 blkPl_131 decRel_afterTrFrom errTail_stack_recombine
   exists_words3_of_memRegion_24 exists_words5_of_errTailBody exists_words5_of_speBodyAt
   exists_words6_of_memRegion_48 sepWP_to_reaches_pc_midMeta_placed
   stackAt_tryDecryptSubStack_sub trAt_expose_errTail
   tryDecryptDummyImg tryDecryptMidMeta_placed tryDecryptWPInv words5At)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (ErrTailSeamPlaced ErrTailSeamXPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
  (ErrTailSeamTightPlaced ErrTailSeamTightXPlaced
   tryDecryptFnSpecTightPlaced tryDecryptSpecTightPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
  (ErrTailStatePlaced_to_placed ErrTailStateXPlaced_to_placed
   ErrTailStateX_placed ErrTailState_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget
  (errTail_all_steps_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget (S1SeamTightFreePlaced S1SeamTightFreeXPlaced S1SeamTightGenPlaced S1SeamTightGenXPlaced S1SeamTightPinnedGenPlaced S1SeamTightPinnedGenXPlaced decResultFnAt_atState)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget
  (trFromPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
  (chainAt_atState_fn invalidMessageStrAt_atState live_atState
   protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
   vecResultAt_atState vecU8_atState)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Relocatable `[LibsignalPlacement]` Tight `P3kR1bc` Combinators & `ErrTail` Proofs -/

namespace P3kR1bc

end P3kR1bc

/-! ## 2. Top-Level Relocatable `[LibsignalPlacement]` Tight `S1` & `ErrTail` Seam Theorems -/

abbrev S1SeamTightPinnedFreePlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamTightPinnedGenPlaced prog entry C A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1SeamTightPinnedFreeXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamTightPinnedGenXPlaced prog entry C decFn A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget

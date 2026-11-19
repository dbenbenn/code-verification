/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget

/-!
# File-Descriptor-Threaded `signal_session_ratchet::decrypt_signal` Slot Contract (Placed)

`FdsGe3Closed`-threaded and `withPreFdsGe3Closed` slot contracts for
`signal_session_ratchet::decrypt_signal` (Block `463`) called from Block `579` under
`[LibsignalFullPlacement]`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalFullPlacement LibsignalHooks lsmpl)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityVtablesPlacedOk SessionOnlyVtablesPlacedOk)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (RunNeeds RunSem mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptSignalNeed decSigDef)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn FilesOkPeer scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptFrozenPlacedOk decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv decSigSlotSpecFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd
  (decSigSlotSpecFrozenPlaced_withFds_to_preFd decSigSlotSpecFrozenPlaced_withFds_to_withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
  (cliDecryptSignal_slot_full_placed_pe slotsOfSigFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (okPlaced_slotWithPreFdsGe3Closed_of_withFdsGe3Closed slotWithFdsGe3Closed
   slotWithPreFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudgetFd

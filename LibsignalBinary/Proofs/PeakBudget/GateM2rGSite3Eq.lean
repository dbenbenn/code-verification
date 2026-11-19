/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget

/-!
# Definitional Equality Between `cliDecPkCanonSlotEnvExact` and `GateM2rGStatesRecvTwins`

Proves by `rfl` that `RealCliDecPkGuardedDefs.cliDecPkCanonSlotEnvExact X W` equals
`GateM2rGStatesRecvTwins.m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
(fun _ K => StatesRecvProtoEnv' K) X W`, and supplies `cliDecPkCanonSlotEnvExact` specializations
of the `hRunSub` eliminators and `DecPkD2cSlotOkFrozenPlaced` lift.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Eq

open Arm64.Obj Arm64.Process
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOkD2c)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
  (DecPkD2cSlotOkFrozenPlaced DecPkD2cSlotOkFrozenPlacedAt)
open LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
  (m2rg_decPkD2cSlotOkFrozenPlaced_cmkVerNeGuardedOf'_of_unguarded
   m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'
   m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'_of_guarded_cliPqInputs_recv
   m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'_of_guarded_tight
   m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed')
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (cliDecPkCanonSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired (StatesRecvProtoEnv')
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)

end LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Eq

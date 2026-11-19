/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactC
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactG
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactGr
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactL
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2 -- proof-setup: allow-public-import
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

/-!
# Guarded-Tight `W1` (`encrypt` `@109`) Exact Slot Assembly

**Checked by Lean.**

Assembles `ckx2_w1EncExact_phaseCredit`, `ckx2_w1EncExact_groupSpec`, and
`ckx2_w1EncExact_singleSlotFineSpec` for `ckx2_cliEncryptBinaryKitSlotEnvExact` from
`w1x_guard`, `w1xl_lift`, `w1x_creditCore`, and `w1x_gr_groupCore`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm

open Arm64.Process (bytesOfString)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall parseArgs)
open LibsignalBinary.Heap (AllocCostModel RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactGr (w1x_gr_groupCore)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactL (w1xl_lift)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
  (ckx2_w1EncExact_groupSpec_of_w1x ckx2_w1EncExact_phaseCredit_of_w1x w1x_creditCore_Stmt)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_cliEncryptBinaryKitSlotEnvExact ckx2_w1EncExact_groupSpec_Stmt
   ckx2_w1EncExact_phaseCredit_Stmt ckx2_w1EncExact_singleSlotFineSpec_of_stmts)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W1BinarySendDom W1BinarySendParams)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)

private theorem w1x_asm_creditCore [LibsignalPlacement] (W : CliHooks) :
    w1x_creditCore_Stmt W :=
  CliKitW1EncExactC.w1x_creditCore W

/-- `PhaseCreditSpec` for `ckx2_cliEncryptBinaryKitSlotEnvExact`. -/
theorem ckx2_w1EncExact_phaseCredit [LibsignalPlacement] (W : CliHooks) :
    ckx2_w1EncExact_phaseCredit_Stmt W :=
  ckx2_w1EncExact_phaseCredit_of_w1x W
    (CliKitW1EncExactG.w1x_guard W)
    w1xl_lift
    (w1x_asm_creditCore W)

/-- `PhaseGroupSpec` for `ckx2_cliEncryptBinaryKitSlotEnvExact`. -/
theorem ckx2_w1EncExact_groupSpec [LibsignalPlacement] (W : CliHooks) :
    ckx2_w1EncExact_groupSpec_Stmt W :=
  ckx2_w1EncExact_groupSpec_of_w1x W
    (CliKitW1EncExactG.w1x_guard W)
    w1xl_lift
    (w1x_gr_groupCore W)

end LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm

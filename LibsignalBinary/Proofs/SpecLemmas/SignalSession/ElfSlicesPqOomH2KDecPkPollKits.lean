/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientIntegration
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsInstPlacedBudgetFd
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget -- proof-setup: allow-public-import
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
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget

/-!
# `CliDecPkPollKitsPlacedOkFds` Discharger at `h2k_ghFixedK` (`ElfSlicesPqOomH2KDecPkPollKits`)

**Checked by Lean.**

Instantiates `DecPkPollKitsInstPlacedBudgetFd.cliDecPkPollKitsPlacedOkFds_of_runHooksBundleFd`
at `fineHookRustCliAllocBudget`, `cliBudgetLimits`, `cliRunBudgets`,
`ReadFileRuleEnvFixed cliIo.rd`, `SessDeserializeCancelEnv`, and `h2k_ghFixedK mpl mmpl`.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KDecPkPollKits

open Arm64 (GhostName)
open Arm64.Obj (MultiPlacement)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunGlue (cliGhostExterns)
open LibsignalBinary.Heap.Fine (fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
  (CliDecPkPollKitsPlacedOkFds)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsInstPlacedBudgetFd
  (cliDecPkPollKitsPlacedOkFds_of_runHooksBundleFd)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges (h2kb_hole2_hG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB
  (F3WitnessRunHooksBundleFd h2ksb_hole2_hHooksBundleFd h2ksb_witness_hG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open VerifiedLibraries (mallocngLib)

/-- Discharges `CliDecPkPollKitsPlacedOkFds` at `h2k_ghFixedK mpl mmpl`. -/
theorem h2k_cliDecPkPollKitsPlacedOkFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    mpl.base 547 ≠ 0#64 →
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      CliDecPkPollKitsPlacedOkFds
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro h547 W γ tp
  exact cliDecPkPollKitsPlacedOkFds_of_runHooksBundleFd mmpl (h2k_ghFixedK mpl mmpl) W h547 rfl
    (h2kb_hole2_hG mpl mmpl hLs hMm γ tp)
    (h2ksb_hole2_hHooksBundleFd mpl mmpl hLs hMm W γ tp)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KDecPkPollKits

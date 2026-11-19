/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
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
# Two-Placement `579 → 617` Lift & `MainOkOverD3F3` Glue

Connects `pqD3ScopedRun` over `cliRunSemOverV4 X W` and `[LibsignalPlacement]`-free
two-placement `(mpl, mmpl)` Block-`579 → 617` harness lifts to `MainOkOverD3F3` and
`MainOkCliF3OverB2NeedLocksPlacedAt`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueOverF3

open Arm64 (GhostName Memory subroutine_ok)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (bytesOfString)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives wirePrekey)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliExternsPlaced cliProcessInputs pqRecvInputs)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops
  (DomainArgv hparse_of_domains parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runAns runRel runRel_dom)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
  (cliRunSemOverV4 pqD3ScopedRun runRel_pqRecv_canonicalNoMatch runRel_pqRecv_validOver)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
  (MainOkCanonNoMatchD3F3 MainOkOverD3F3 MainOkValidOverBodyD3F3 mainOkCliF3Over_of_mainOkOverD3F3
   mainOkOverD3F3_of_clauses)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MainOkCliF3OverB2NeedLocksPlacedAt b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)

/-! ## 1. Pure `pqD3ScopedRun` & `cliRunSemOverV4` Clauses -/

/-- Canonical-`m.bytes` non-matching clause (`MainOkCanonNoMatchD3F3`) at
`RunOf X W := pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))`. -/
theorem mainOkCanonNoMatchD3F3_overV4 (mpl : MultiPlacement) :
    MainOkCanonNoMatchD3F3 mpl
      (fun X W => pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) := by
  unfold MainOkCanonNoMatchD3F3
  intro _hDropNz X W _WP _Run st hst x g hsess m rc hm hnomatch
  exact ⟨runAns (cliRunSemOverV4 X W) (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc),
    runRel_pqRecv_canonicalNoMatch X W st x g m rc hst hsess hm hnomatch⟩

/-- Establishes `MainOkValidOverBodyD3F3` from a Block-`617` `subroutine_ok` over
`pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))`. -/
theorem mainOkValidOverBodyD3F3_of_mainSubroutine
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hmain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) cliProcessInputs)) :
    MainOkValidOverBodyD3F3 mpl mmpl CodeOk libcAddr brkStart stk
      (fun X W => pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) := by
  unfold MainOkValidOverBodyD3F3
  intro hDropNz X W _WP _Run
  refine ⟨hmain hDropNz X W, fun st hst x g hsess body pm m rc hbody hparse hpk hm hnomatch => ?_⟩
  exact ⟨runAns (cliRunSemOverV4 X W) (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc),
    runRel_pqRecv_validOver X W st x g body pm m rc hst hsess hbody hparse hpk hm hnomatch⟩

/-- Establishes `MainOkOverD3F3` from a Block-`617` `subroutine_ok` over
`pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))`. -/
theorem mainOkOverD3F3_of_mainSubroutine
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hmain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) cliProcessInputs)) :
    MainOkOverD3F3 mpl mmpl CodeOk libcAddr brkStart stk :=
  mainOkOverD3F3_of_clauses
    (mainOkValidOverBodyD3F3_of_mainSubroutine hmain)
    (mainOkCanonNoMatchD3F3_overV4 mpl)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueOverF3

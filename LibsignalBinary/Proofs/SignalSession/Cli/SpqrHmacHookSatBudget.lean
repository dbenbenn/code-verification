/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.CreditInst
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced -- proof-setup: allow-public-import
public import ProofLib.StdStartup.MuslStage1Init
public import VerifiedLibraries.Musl.Proofs.CryptoHooks
public import VerifiedLibraries.Musl.Proofs.MemmoveProof
public import VerifiedLibraries.Musl.Proofs.MemsetProof
public import VerifiedLibraries.Musl.Spec
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals

/-!
# Budget-Threaded `libcrux_hmac::hmac` `HookSat` Witnesses

Proves `HookSat` witnesses for `spqrLibcruxHmacSym` (`libcrux_hmac::hmac`) on `cliGhostExterns`
from `gh.extra.lookup spqrLibcruxHmacSym = some (libcruxHmacHookMallocng mmpl W.C.F)` and
`VerifiedLibraries.mallocngLib.Placeable mmpl`, for both generic
`mallocngHookRustCliAllocBudget` and concrete `fineHookRustCliAllocBudget` (unwrapped and
`withLsRet`-narrowed).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open CryptoVerification.E2E (libcruxHmacHookMallocng)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_extra_some)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits MallocngCostModelIface MallocngCostModelSound)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudget fineLibcruxHmac_budget_hookSat
   libcruxHmacHookMallocng_budget_ok mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookSat_withLsRet withLsRet)

/-- Direct `cliGhostExterns` lookup equation for `spqrLibcruxHmacSym` from `gh.extra`. -/
theorem hpo_cliGhostExterns_libcruxHmac_eq
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hHmac : gh.extra.lookup spqrLibcruxHmacSym = some (libcruxHmacHookMallocng mmpl W.C.F)) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) spqrLibcruxHmacSym =
      some (libcruxHmacHookMallocng mmpl W.C.F) :=
  cliGhostExterns_extra_some gh (cliExternsPlaced mmpl W) hHmac

/-- Unwrapped `HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym` over any
    `(M, I)` satisfying `MallocngCostModelSound M I`. -/
theorem hpo_cliLibcruxHmac_mallocngHook_budget_hookSat_unwrapped
    {M : AllocCostModel} {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hHmac : gh.extra.lookup spqrLibcruxHmacSym = some (libcruxHmacHookMallocng mmpl W.C.F)) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim) :=
  ⟨libcruxHmacHookMallocng mmpl W.C.F,
    hpo_cliGhostExterns_libcruxHmac_eq mmpl gh W hHmac,
    libcruxHmacHookMallocng_budget_ok hS γ tp brkStart lim hPl W.C.F⟩

/-- `withLsRet`-narrowed `HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym`
    over any `(M, I)` satisfying `MallocngCostModelSound M I`. -/
theorem hpo_cliLibcruxHmac_mallocngHook_budget_hookSat [CryptoVerification.LibsignalPlacement]
    {M : AllocCostModel} {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hHmac : gh.extra.lookup spqrLibcruxHmacSym = some (libcruxHmacHookMallocng mmpl W.C.F)) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet
        (libcruxHmacBudgetSpec W.C.F M
          (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)) :=
  hookSat_withLsRet
    (hpo_cliLibcruxHmac_mallocngHook_budget_hookSat_unwrapped hS γ mmpl tp brkStart lim gh W hPl hHmac)

/-- Unwrapped `(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)` `HookSat` witness for
    `spqrLibcruxHmacSym` on `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem hpo_cliLibcruxHmac_budget_hookSat_unwrapped
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hHmac : gh.extra.lookup spqrLibcruxHmacSym = some (libcruxHmacHookMallocng mmpl W.C.F)) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  fineLibcruxHmac_budget_hookSat γ tp brkStart lim hPl W.C.F
    (hpo_cliGhostExterns_libcruxHmac_eq mmpl gh W hHmac)

/-- `withLsRet`-narrowed `(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)` `HookSat`
    witness for `spqrLibcruxHmacSym` on `cliGhostExterns gh (cliExternsPlaced mmpl W)`, matching the
    `hHmac` hypothesis of `spqrV1PlacedSeamsOfEnv_of_sendCoins` and `cliSpqrSendCoins_placed_ok_*`. -/
theorem hpo_cliLibcruxHmac_budget_hookSat [CryptoVerification.LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hHmac : gh.extra.lookup spqrLibcruxHmacSym = some (libcruxHmacHookMallocng mmpl W.C.F)) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet
        (libcruxHmacBudgetSpec W.C.F fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  hookSat_withLsRet
    (hpo_cliLibcruxHmac_budget_hookSat_unwrapped γ mmpl tp brkStart lim gh W hPl hHmac)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable `SessionRecord::serialize` Glue at `cliGhostExterns`

Instantiates budget-threaded `SessionRecord::serialize` (Block `52`) and pre-allocated
`SessionStructure::encode_raw` (Block `14`) contracts at `cliGhostExterns g (cliExternsPlaced mmpl W)`
from either `CliGhostAllocHooks` or `CliAllocHooks` over `bumpGhost`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
  (EncodeRawPreallocPlacedOkX encodeRawPreallocSpecX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget
  (recordSerializeEnvSpecX recordSerializeSpecX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
  (SerContractsXPlaced SerializeEnvX serializeCanonSpecX serializeSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget (CliAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks bumpGhost cliGhostAllocHooks_bumpGhost
   cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpy_budget_sat
   cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
  (hSerEnv_placed_cl_of_serContractsX hSerEnv_placed_lscro_of_serContractsX
   hSerEnv_placed_ok_of_serContractsX hSer_placed_cl_of_serContractsX
   hSer_placed_lscro_of_serContractsX hSer_placed_ok_of_serContractsX
   serializeCanonX_placed_cl_of_serContractsX serializeCanonX_placed_lscro_of_serContractsX
   serializeCanonX_placed_ok_of_serContractsX serialize_placed_cl_of_serContractsX
   serialize_placed_lscro_of_serContractsX serialize_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget
  (encodeRawPrealloc_placed_cl_of_serContractsX encodeRawPrealloc_placed_ok_of_serContractsX
   serializeCanonSeqFreeSpecX serializeCanonSeqFree_placed_cl_of_serContractsX
   serializeCanonSeqFree_placed_lscro_of_serContractsX
   serializeCanonSeqFree_placed_ok_of_serContractsX serializeSeqFreeSpecX
   serialize_seqFree_placed_cl_of_serContractsX
   serialize_seqFree_placed_lscro_of_serContractsX
   serialize_seqFree_placed_ok_of_serContractsX)

/-- Short alias for `CliHookSatPlacedBudget.CliAllocHooks` alongside `AllocFsA1Budget.CliAllocHooks`. -/
abbrev SlotsCliAllocHooks [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliAllocHooks M A lim

/-- Short alias for `CliHookSatPlacedBudget.CliGhostAllocHooks`. -/
abbrev SlotsCliGhostAllocHooks [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (g : CliGhostHooks) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostAllocHooks M A lim g

theorem cliAllocHooks_to_slots [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hA : CliAllocHooks A lim) :
    SlotsCliAllocHooks M A lim :=
  ⟨hA.alloc, hA.dealloc, hA.realloc⟩

theorem cliAllocHooks_to_bumpGhost [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hA : CliAllocHooks A lim) :
    CliGhostAllocHooks M A lim bumpGhost :=
  cliGhostAllocHooks_bumpGhost (cliAllocHooks_to_slots hA)

/-! ## 1. `cliGhostExterns g (cliExternsPlaced mmpl W)` Contracts & Block `52` Theorems (`CliGhostAllocHooks`) -/

/-- `SerContractsXPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W))` from
`CliGhostAllocHooks M A lim g`. -/
theorem serContractsX_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    SerContractsXPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  SerContractsXPlaced.of_hooks
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_sessionMemcpy_budget_sat mmpl g W hG extHookStack)

/-- `serializeCanonSpecX M A lim` on Block `52` at `cliGhostExterns g (cliExternsPlaced mmpl W)`
(`withLsCodeLoaded`). -/
theorem serializeCanonX_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok (lsProg_52 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)) :=
  serializeCanonX_placed_ok_of_serContractsX (serContractsX_cli_placed mmpl g W hG)

theorem serializeCanonX_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim g)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCanonSpecX M A lim)) :=
  serializeCanonX_placed_lscro_of_serContractsX (serContractsX_cli_placed mmpl g W hG) hblk

/-- Exact `serializeCanonSeqFreeSpecX M A lim` (`RecordSerializeSeqFreeEnv`) on Block `52` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)` (`withLsCodeLoaded`). -/
theorem serializeCanonSeqFree_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)) :=
  serializeCanonSeqFree_placed_ok_of_serContractsX (serContractsX_cli_placed mmpl gh W hG)

/-! ## 2. `AllocFsA1Budget.CliAllocHooks` Variants (`*_placed*_of_cliHooks` over `bumpGhost`) -/

/-- `SerContractsXPlaced M A lim (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))` from
`AllocFsA1Budget.CliAllocHooks A lim`. -/
theorem serContractsX_placed_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim) :
    SerContractsXPlaced M A lim (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W)) :=
  serContractsX_cli_placed mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget

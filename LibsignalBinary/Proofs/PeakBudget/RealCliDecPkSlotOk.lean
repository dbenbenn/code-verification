/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# Closed Leaf Witnesses for Linked `recv-prekey` (`W4`)

Assembles the closed leaf contracts over the two-argument hook table
`cliGhostExterns gh (cliExternsPlaced mmpl W)` at `fineHookRustCliAllocBudget γ mmpl tp brkStart`
(parametric in `gh : CliGhostHooks`):
1. `formatInnerCallCliLsSpec` and `fmtWriteProtoAddrCliLsSpec` `HookSat` witnesses from `gh.extra`;
2. `aesDecBudgetSpec` and `aesDecWeakBudgetSpec` `HookSat` witnesses over `mallocng`;
3. `RunHooksPlaced` over `cliGhostExterns gh` (`cliRunHooksPlaced_of_ghost`);
4. Subroutine contracts for Block `14` (`SessionStructure::encode_raw`), Block `46`
   (`SessionRecord::deserialize`), Block `519` (`pqxdh_log_closure`), and Block `79`
   (`Pqxdh::accept` success and owned-error paths).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  IsLsBlockProg LibsignalFullPlacement LibsignalHooks LibsignalPlacement lsmpl
)
open CryptoVerification.LibsignalTripleRatchet (withLsFrozen)
open CryptoVerification.E2E (
  UnreachedPqxdhPrimitives aesDecHookMallocng modelPrims
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_46)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsAesDecSym lsFmtWriteSym lsFormatInnerSym lsStringCloneSym
)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced (cliHookTablePlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks IsFsC cliGhostExterns cliGhostExterns_extra_some
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  pqxdhLogClosurePlacedSpec pqxdh_log_closure_frozen_placed_ok_of_block
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec aesDecWeakBudgetSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  pqxdhAcceptOptFieldsFrozenPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlacedBudget (
  pqxdhAcceptErrOwnedFrozenPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineAesDecWeak_budget_hookSat fineAesDec_budget_hookSat fineHookRustCliAllocBudget
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  AllocContractsBudgetPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (
  RecordDeserializeCancelEnv sessDeserializeCancel_recordEnv_fine_specPlaced_ok
)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookSat_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs (
  fmtWriteProtoAddrCliLsSpec formatInnerCallCliLsSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks CliGhostSpqrAllocHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget (
  encodeRawPrealloc_placed_ok_of_serContractsX
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget (
  cliPqxdhAccept_err_owned_full_placed_ok cliPqxdhAccept_opt_fields_full_placed_ok
)

/-! ## 1. Closed Formatting & `mallocng` AES-CBC Hook Contracts on `cliGhostExterns` -/

/-- `formatInnerCallCliLsSpec` `HookSat` at `cliGhostExterns gh (cliExternsPlaced mmpl W)`
from `gh.extra.lookup lsFormatInnerSym = some f`. -/
theorem cliFormatInnerCall_cliLs_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {f : State → State}
    (hLook : gh.extra.lookup lsFormatInnerSym = some f)
    (hOk : HookOk f (formatInnerCallCliLsSpec M A lim)) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerCallCliLsSpec M A lim) :=
  ⟨f, cliGhostExterns_extra_some gh (cliExternsPlaced mmpl W) hLook, hOk⟩

/-- `fmtWriteProtoAddrCliLsSpec` `HookSat` at `cliGhostExterns gh (cliExternsPlaced mmpl W)`
from `gh.extra.lookup lsFmtWriteSym = some f`. -/
theorem cliFmtWriteProtoAddr_cliLs_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {f : State → State}
    (hLook : gh.extra.lookup lsFmtWriteSym = some f)
    (hOk : HookOk f (fmtWriteProtoAddrCliLsSpec M A lim)) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteProtoAddrCliLsSpec M A lim) :=
  ⟨f, cliGhostExterns_extra_some gh (cliExternsPlaced mmpl W) hLook, hOk⟩

/-- `aesDecBudgetSpec` `HookSat` at `cliGhostExterns gh (cliExternsPlaced mmpl W)` over
`fineHookRustCliAllocBudget γ mmpl tp brkStart`. -/
theorem cliAesDec_budget_sat [LibsignalPlacement] (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (gh : CliGhostHooks) (W : CliHooks)
    (hLook : gh.extra.lookup lsAesDecSym = some (aesDecHookMallocng mmpl W.C.D)) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (withLsRet (aesDecBudgetSpec W.C.D fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  hookSat_withLsRet
    (fineAesDec_budget_hookSat γ tp brkStart lim hPl W.C.D
      (cliGhostExterns_extra_some gh (cliExternsPlaced mmpl W) hLook))

/-- `aesDecWeakBudgetSpec` `HookSat` at `cliGhostExterns gh (cliExternsPlaced mmpl W)` over
`fineHookRustCliAllocBudget γ mmpl tp brkStart`. -/
theorem cliAesDecWeak_budget_sat (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (gh : CliGhostHooks) (W : CliHooks)
    (hLook : gh.extra.lookup lsAesDecSym = some (aesDecHookMallocng mmpl W.C.D)) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecWeakBudgetSpec W.C.D fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  fineAesDecWeak_budget_hookSat γ tp brkStart lim hPl W.C.D
    (cliGhostExterns_extra_some gh (cliExternsPlaced mmpl W) hLook)

/-! ## 2. Closed `RunHooksPlaced` & Stage-1 Subroutine Leaf Witnesses -/

/-- `RunHooksPlaced` at `cliGhostExterns gh (cliExternsPlaced mmpl W)` from
`CliGhostSpqrAllocHooks` and `HookSat` witnesses for `String::clone`, `format_inner`, and
`fmt::write`. -/
theorem cliRunHooksPlaced_of_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostSpqrAllocHooks M A lim gh)
    (hStrFsT : ∀ f, gh.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hFmtInner : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerCallCliLsSpec M A lim))
    (hFmtWrite : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteProtoAddrCliLsSpec M A lim)) :
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  RunHooksPlaced.of_hooks mmpl gh W hG hStrFsT hStrClone hFmtInner hFmtWrite

/-- Block `14` (`SessionStructure::encode_raw`) pre-reserved `0`-alloc contract from
`SerContractsXPlaced`. -/
theorem cliEncodeRawPrealloc_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hSer : SerContractsXPlaced M A lim H) :
    EncodeRawPreallocPlacedOkX A.repAlloc H :=
  encodeRawPrealloc_placed_ok_of_serContractsX hSer

/-- Block `46` (`SessionRecord::deserialize`) `RecordDeserializeCancelEnv` contract at
`fineCostModel`. -/
theorem cliSessDeserializeCancel_recordEnv_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustCliAllocBudget fineCostModel} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced fineCostModel A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r) :
    subroutine_ok (lsProg_46 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim
        (fun r => RecordDeserializeCancelEnv (encodeRecord r))) :=
  sessDeserializeCancel_recordEnv_fine_specPlaced_ok hA hsub

/-- Block `519` (`pqxdh_log_closure`, mutated) `withLsFrozen` contract on any caller block under
`[LibsignalFullPlacement]`. -/
theorem cliPqxdhLogClosure_frozen_placed_ok [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 519)
      (withLsFrozen lsmpl pqxdhLogClosurePlacedSpec) :=
  pqxdh_log_closure_frozen_placed_ok_of_block

/-- Block `79` (`Pqxdh::accept` success, mutated) `withLsFrozen` + `AcceptOptFieldsEnv` contract at
`cliGhostExterns gh (cliExternsPlaced mmpl W)` under `[LibsignalFullPlacement]`. -/
theorem cliPqxdhAcceptOptFields_frozen_placed_ok [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
        A lim
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))) :=
  cliPqxdhAccept_opt_fields_full_placed_ok X mmpl gh W hG hF hX hDecaps

/-- Block `79` (`Pqxdh::accept` owned error, mutated) `withLsFrozen` + `AcceptOptFieldsEnv`
contract at `cliGhostExterns gh (cliExternsPlaced mmpl W)` under `[LibsignalFullPlacement]`. -/
theorem cliPqxdhAcceptErrOwned_frozen_placed_ok [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim gh)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptErrOwnedFrozenPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
        A lim
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))) :=
  cliPqxdhAccept_err_owned_full_placed_ok X mmpl gh W hG hF hX hDecaps

end LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk

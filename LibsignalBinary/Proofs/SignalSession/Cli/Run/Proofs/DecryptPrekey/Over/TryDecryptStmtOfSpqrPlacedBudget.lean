/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.AesDecErrRoBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.CryptoGames.DH.X25519
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget

/-!
# Budget-Threaded `[LibsignalPlacement]` `OverCliTryDecryptPqV1PlacedStmt` Discharger

Discharges the `CliGhostAllocHooks`-guarded `OverCliTryDecryptPqV1PlacedStmt` at
`TryDecryptCliEnv` and monotonic `tdEnv` from `aesDecBudgetSpec` and `SpqrV1PlacedSeams`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.TryDecryptStmtOfSpqrPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.CliHandshake.RespClosurePlaced (instIsLsBlockProg_518)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsAesDecSym lsFmtWriteSym lsFormatInnerSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (dpPollProgPlaced)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.AesDecErrRoBudget (cliAesDecBudgetSpecErrRo)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs (
  fmtWriteProtoAddrCliLsSpec formatInnerCallCliLsSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs (
  CliFmtWriteEnv CliFormatInnerEnv cliFmtWriteEnv_nil cliFormatInnerEnv_nil
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget (
  tryDecryptPqV1_placed_ok_PTight_cli_at_block
  tryDecryptPqV1_placed_ok_PTight_cli_at_block_of_tdEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (
  TryDecryptCliEnv TryDecryptCliEnvOf
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  OverCliTryDecryptPqV1PlacedStmt overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-- Discharges `OverCliTryDecryptPqV1PlacedStmt` at `TryDecryptCliEnv` from
`cliAesDecBudgetSpecErrRo`, `SpqrV1PlacedSeams`, and formatting call-descriptor witnesses via
`tryDecryptPqV1_placed_ok_PTight_cli_at_block`. -/
theorem cliTryDecryptPqV1_placed_of_spqr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hAesDec : ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim g →
      HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym
        (withLsRet (cliAesDecBudgetSpecErrRo W.C.D M A lim)))
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim g → SpqrV1PlacedSeams M A lim mmpl g W)
    (hFmtWrite : ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim g →
      HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
        (fmtWriteProtoAddrCliLsSpec M A lim))
    (hFmtInner : ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim g →
      HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
        (formatInnerCallCliLsSpec M A lim)) :
    OverCliTryDecryptPqV1PlacedStmt A lim
      (fun W => TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)) :=
  fun mmpl g W ctl hG hF hX hPub =>
    tryDecryptPqV1_placed_ok_PTight_cli_at_block mmpl g W ctl hG hF hX hPub
      (hAesDec mmpl g W hG) (hSpqr mmpl g W hG)
      (hFmtWrite mmpl g W hG) (hFmtInner mmpl g W hG) (by decide)

/-- Envelope-monotonic discharger for `OverCliTryDecryptPqV1PlacedStmt A lim tdEnv` via
`tryDecryptPqV1_placed_ok_PTight_cli_at_block_of_tdEnv`. -/
theorem cliTryDecryptPqV1_placed_of_spqr_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : CliHooks → InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : CliHooks → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : CliHooks → SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (hAesDec : ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim g →
      HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym
        (withLsRet (cliAesDecBudgetSpecErrRo W.C.D M A lim)))
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim g →
      SpqrV1PlacedSeamsOfEnv M A lim mmpl g W (InitEnv W)
        (fun st msg => RecvBytesEnv W st.bytes msg.bytes) (SendEnv W))
    (hFmtWrite : ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim g →
      HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
        (fmtWriteProtoAddrCliLsSpec M A lim))
    (hFmtInner : ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim g →
      HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
        (formatInnerCallCliLsSpec M A lim))
    (hRecv_ne : ∀ (W : CliHooks) stBs msgBs, ∃ evs, RecvBytesEnv W stBs msgBs evs)
    (hFmtWrite_ne : ∀ _ : CliHooks, ∃ evs, CliFmtWriteEnv evs :=
      fun _ => ⟨[], cliFmtWriteEnv_nil⟩)
    (hFmtInner_ne : ∀ _ : CliHooks, ∃ evs, CliFormatInnerEnv evs :=
      fun _ => ⟨[], cliFormatInnerEnv_nil⟩)
    (htd : ∀ (W : CliHooks) a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) CliFmtWriteEnv (RecvBytesEnv W)
        CliFormatInnerEnv a evs →
      tdEnv W a evs) :
    OverCliTryDecryptPqV1PlacedStmt A lim tdEnv :=
  fun mmpl g W ctl hG hF hX hPub =>
    tryDecryptPqV1_placed_ok_PTight_cli_at_block_of_tdEnv mmpl g W ctl hG hF hX hPub
      (hAesDec mmpl g W hG) (hSpqr mmpl g W hG)
      (hFmtWrite mmpl g W hG) (hFmtInner mmpl g W hG)
      (hRecv_ne W) (hFmtWrite_ne W) (hFmtInner_ne W) (htd W) (by decide)

/-- Pointwise `(mmpl, g, W)` Block-`507` `dpPollProgPlaced` specialization of
`tryDecryptPqV1_placed_ok_PTight_cli_at_block` at `TryDecryptCliEnv`. -/
theorem overPollTryDecrypt_placed_at_of_spqr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hAesDec : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym
      (withLsRet (cliAesDecBudgetSpecErrRo W.C.D M A lim)))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteProtoAddrCliLsSpec M A lim))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerCallCliLsSpec M A lim)) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
          (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))) :=
  tryDecryptPqV1_placed_ok_PTight_cli_at_block mmpl g W ctl hG hF hX hPub hAesDec hSpqr
    hFmtWrite hFmtInner (by decide)

/-- Pointwise `(mmpl, g, W)` Block-`507` `dpPollProgPlaced` specialization of
`tryDecryptPqV1_placed_ok_PTight_cli_at_block_of_tdEnv`. -/
theorem overPollTryDecrypt_placed_at_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hAesDec : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym
      (withLsRet (cliAesDecBudgetSpecErrRo W.C.D M A lim)))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteProtoAddrCliLsSpec M A lim))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerCallCliLsSpec M A lim))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, CliFmtWriteEnv evs := ⟨[], cliFmtWriteEnv_nil⟩)
    (hFmtInner_ne : ∃ evs, CliFormatInnerEnv evs := ⟨[], cliFormatInnerEnv_nil⟩)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) CliFmtWriteEnv RecvBytesEnv CliFormatInnerEnv a evs →
      tdEnv a evs) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)) :=
  tryDecryptPqV1_placed_ok_PTight_cli_at_block_of_tdEnv mmpl g W ctl hG hF hX hPub hAesDec hSpqr
    hFmtWrite hFmtInner hRecv_ne hFmtWrite_ne hFmtInner_ne htd (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.TryDecryptStmtOfSpqrPlacedBudget

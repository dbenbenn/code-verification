/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlaced -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3ExactPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudget
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudget
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux
import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
import LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli
import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedTightBudgetR
import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat
import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeams
import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegsBudget
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat

/-!
# `TopStateTight`-Guarded SPQR Seams for `decryptPrekey` (`W4`)

**Checked by Lean.**

Defines `w4s2_SpqrRecvTopStateGuardedBytesEnv` and `w4s2_TryDecryptTopStateGuardedEnv`,
and discharges `SpqrV1PlacedSeamsOfEnv` at any `brkStart` without `CliElf` dependencies.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2

section SpqrTopStateGuarded

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession
  (ChainKey Crypto MessageKeyGenerator Mut RatchetState SessionState ShaCompress TripleRatchet)
open CryptoVerification
  (IsLsBlockProg LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns lsLogFilterAddr ls_blockPlacement_base lsmpl)
open CryptoVerification.E2E (libcruxHmacHookMallocng)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Bytes MlKem Message PqRatchetState SpqrRecvModel States V1Recv V1State VersionNegotiationPB
   pbToPqRatchetState sha256Compress spqrAuthApi spqrPolyApi spqrV1 spqrV1Recv)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet
  (SendCall TrGhost TryDecryptGhost VecArg sessionMemmoveSpec spqrRecvStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (coinsOf uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced libsignalSessionLib lsFmtWriteSym lsFormatInnerSym lsReadFileSym
  lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
  lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns
   hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (lsRngFillSym trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Alloc (growOneStack)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.SpqrV1.Top.MessageDeserialize (spqrFormatInnerSym)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.SendTotal
  (BOkTight isEkSide st_bCodec st_bRecvCt_tight st_bRecvEk_tight st_bSize_tight)
open CryptoVerification.SpqrV1Sync.TopSync (topPb)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (formatInnerCallCliLsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
  (CliFmtWriteEnv CliFormatInnerEnv)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (sessionMemmoveBoundedSpec)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (TryDecryptCliEnvOfPure tryDecryptCmkSeg4Env tryDecryptEnvArgsToGhost)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness (spqrRecvTightLinkedEnv_nil_exists)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux (spqrRecvBranchHyps_tightLinked)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
  (StatesRecvExactTightEnv StatesRecvProtoEnv' statesRecvExactTightEnv_sub_statesRecvProtoEnv'
   states_recv_placed_ok_x_exactTight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (ValidV1PtsAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_DecodeStateGuardedEnv tlb_DecodeStateTightEnvOf tlb_V1StateMergeBlk325TightOkOf
   tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_decode_props topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
  (SpqrRecvC07C09aBytesEnvOf SpqrRecvC07C09aTightLinkedEnvOf TryDecryptCliLinkedEnvOf
   spqrRecvC07C09aBytesEnvOf_nonempty tryDecryptCliLinkedEnvOf_eq_pure)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_sessionMemsetRegion_budget_sat
   cliGhostExterns_mlkemDecapsAt_budget_sat cliGhostExterns_mlkemEncaps2_budget_sat
   cliGhostExterns_mlkemValidatePk_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
  (cliV1StateMerge_closed_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (chainParamsMerge_decodeState_of_prost cliChainParams_294_cl cliDeallocBudget_at_block
   cliDrop_267_cl cliDrop_270_cl cliEpochDir_299_cl cliFrom_261_cl cliGrowOne_356_cl
   cliLibcMemcpyBudget_at_block cliPushMerge_257_cl cliSessionMemcpyBudget_at_block
   cliSkipBudget_263_cl cliVarint_291_cl decodeErrorPush_of_merge
   epochDirectionMerge_decodeState_of_prost)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
  (hpo_cliLibcruxHmac_budget_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
  (cliBytesExact_290_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliExternsPlaced_sessionMemmove_allocVm_sat cliRecvCt2PlacedAllocExt)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge
  (gu2b_StatesFromPbGuardedEnv gu2b_cliSpqrRecv_statesFromPb_fromPbGuard_ok
   gu2b_spqrV1PlacedSeams_exactFromPb gu2b_spqrV1PlacedSeams_exactFromPb_of_hmac)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeamsOfEnv spqrRecvPlacedInnerDispSpecXOfEnv spqrRecvPlacedInnerDispSpecXTOfEnv
   spqrRecvPlacedInnerSpecXOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
  (cliSpqrRecvPlacedContracts_exact trTrapExternsPlaced_isPanic)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli
  (v1StateMergeBlk325_cli_of_hExt)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedTightBudgetR
  (statesIntoPbExactEnv_tight statesIntoPbTightDom_of_bokTight)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat
  (statesRecvPlacedContracts_of_ro_leaves_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
  (e2ar_epochDirectionMerge_blk325_cl_ok_tight)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
  (e2a_decodeState_cl_placed_ok_of_v1Merge_109)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget
  (mkDecodeStateCalleeContractsClPlacedX_of_blocks)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
  (spqrRecvPlacedDispSpecXOfEnv spqrRecvPlacedDispSpecXTOfEnv spqrRecvPlacedRawDispSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContractsOfEnv decodeStatePlacedSpecXOfEnv statesRecvPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
  (spqr_recv_placed_disp_ok_blockProgram_ext_of_contracts_ofEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux (s9Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv FromS3GenEnv FromS4GenEnv FromS5GenEnv s1InitTrGhost stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux (s7Env)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-- `TopStateTight`-guarded `spqr::recv` byte-slice envelope at `maxOps = 109`. -/
@[expose] def w4s2_SpqrRecvTopStateGuardedBytesEnv (F : ShaCompress) (K : MlKem)
    (stBs msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  TopStateTight F K stBs → SpqrRecvC07C09aBytesEnvOf 109 F K stBs msgBs evs

/-- `TryDecryptCliEnvOfPure` instantiated at `w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K`. -/
@[expose] def w4s2_TryDecryptTopStateGuardedEnv (W : CliHooks) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  TryDecryptCliEnvOfPure W.C (spqrV1 W.C.F W.Q.K) CliFmtWriteEnv
    (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) CliFormatInnerEnv

theorem w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty (F : ShaCompress) (K : MlKem)
    (stBs msgBs : List (BitVec 8)) :
    ∃ evs, w4s2_SpqrRecvTopStateGuardedBytesEnv F K stBs msgBs evs :=
  let ⟨evs, hevs⟩ := spqrRecvC07C09aBytesEnvOf_nonempty 109 F K stBs msgBs
  ⟨evs, fun _ => hevs⟩

private theorem w4s2_fromSessionState_ok_pqrState {PQ : Type} [Inhabited PQ]
    {s s1 : SessionState PQ} {tr0 : TripleRatchet PQ}
    (h : Mut.exec TripleRatchet.fromSessionState s = (.ok tr0, s1)) :
    tr0.pqrState = s.pqRatchetState := by
  unfold Mut.exec TripleRatchet.fromSessionState SessionState.takeRatchetState
    SessionState.takePqRatchetState at h
  rcases s with ⟨_, _, _ | rem, _, _, _, _, _, _⟩
  · cases h
  · cases h; rfl

private theorem w4s2_pqRecvEnv_topStateGuarded_eq (W : CliHooks)
    (x : TryDecryptGhost) (tr : TripleRatchet (List (BitVec 8)))
    (hTop : TopStateTight W.C.F W.Q.K tr.pqrState) :
    PqRecvEnv (spqrV1 W.C.F W.Q.K) (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K)
        CliFormatInnerEnv x tr =
      PqRecvEnv (spqrV1 W.C.F W.Q.K) (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K)
        CliFormatInnerEnv x tr := by
  have hrecv :
      w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K tr.pqrState x.msg.pqRatchet =
        SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K tr.pqrState x.msg.pqRatchet := by
    funext evs
    exact propext ⟨fun h => h hTop, fun h _ => h⟩
  unfold PqRecvEnv
  rw [hrecv]

/-- Under `TopStateTight`, `w4s2_TryDecryptTopStateGuardedEnv W a` equals `TryDecryptCliLinkedEnvOf 109 W.C W.Q.K a`. -/
theorem w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top (W : CliHooks)
    (a : TryDecryptEnvArgs)
    (hTop : TopStateTight W.C.F W.Q.K a.st.pqRatchetState) :
    w4s2_TryDecryptTopStateGuardedEnv W a = TryDecryptCliLinkedEnvOf 109 W.C W.Q.K a := by
  rw [tryDecryptCliLinkedEnvOf_eq_pure 109 W.C W.Q.K]
  unfold w4s2_TryDecryptTopStateGuardedEnv TryDecryptCliEnvOfPure
  cases hfrom : Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error _ => rfl
    | ok tr0 =>
      dsimp only
      apply congrArg (SeqEnv FreeOnlyEvs)
      let x := tryDecryptEnvArgsToGhost a
      let S := spqrV1 W.C.F W.Q.K
      let s4Env := tryDecryptCmkSeg4Env CliFmtWriteEnv
      have hTop0 : TopStateTight W.C.F W.Q.K tr0.pqrState :=
        (w4s2_fromSessionState_ok_pqrState hfrom).symm ▸ hTop
      have hs5g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
          (mkg : MessageKeyGenerator),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS5GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (PqRecvEnv S (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) CliFormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 mkg =
            FromS5GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K) CliFormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 mkg := by
        intro trG tr mkg hT
        unfold FromS5GenEnv
        rw [w4s2_pqRecvEnv_topStateGuarded_eq W x tr hT]
      have hs4g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS4GenEnv W.C uuidTryParse S (stdAesOpt W.C) s4Env
              (PqRecvEnv S (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) CliFormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 ck =
            FromS4GenEnv W.C uuidTryParse S (stdAesOpt W.C) s4Env
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K) CliFormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 ck := by
        intro trG tr ck hT
        unfold FromS4GenEnv
        cases Mut.exec
            (RatchetState.consumeMessageKey W.C.F x.msg.senderRatchetKey ck x.msg.counter x.msgType)
            tr.ratchet with
        | mk r4 r2 =>
          cases r4 with
          | error _ => rfl
          | ok mkg =>
            dsimp only
            exact congrArg (SeqEnv (s4Env x trG tr ck))
              (hs5g trG { tr with ratchet := r2 } mkg hT)
      have hs3g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS3GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (s3DefaultEnv W.C) s4Env
              (PqRecvEnv S (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) CliFormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 =
            FromS3GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (s3DefaultEnv W.C) s4Env
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K) CliFormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 := by
        intro trG tr hT
        unfold FromS3GenEnv
        cases Mut.exec (RatchetState.dhRatchetStep W.C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | mk r3 r1 =>
          cases r3 with
          | error _ => rfl
          | ok ck =>
            dsimp only
            exact congrArg (SeqEnv (s3DefaultEnv W.C x trG tr))
              (hs4g _ { tr with ratchet := r1 } ck hT)
      unfold FromS2GenEnv
      cases tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error _ => rfl
      | ok cko =>
        cases cko with
        | some ck =>
          dsimp only
          exact hs4g (s1InitTrGhost a.G) tr0 ck hTop0
        | none =>
          dsimp only
          exact hs3g (s1InitTrGhost a.G) tr0 hTop0

theorem w4s2_trTrap_hExt (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
  fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne]

private theorem w4s2_hExt_withPanics (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := fun sym hne => by
  rw [← withPanics_cliGhostExterns mmpl gh W]
  simp only [Rust.withPanics, hExt sym hne]

private def w4s2_FromPbStateGuard (F : ShaCompress) (pb : V1State) : Prop :=
  (∃ st : States spqrPolyApi (spqrAuthApi F), BOkTight st ∧ pb = st.into_pb) ∧
    rawV1State pb ≤ 46880 ∧ ValidV1PtsAt 640 pb

private def w4s2_IntoPbStateGuard {F : ShaCompress} (st1 : States spqrPolyApi (spqrAuthApi F)) : Prop :=
  BOkTight st1 ∧ rawV1State st1.into_pb ≤ 46880

private def w4s2_StatesRecvExactPairTightEnv {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (evs : List AllocEvent) : Prop :=
  ∃ outA selfA msgA, StatesRecvExactTightEnv K ⟨outA, selfA, msgA, st, msg⟩ evs

private theorem w4s2_topStateTight_fromPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb)) :
    w4s2_FromPbStateGuard F pb := by
  have hprops := (topStateTight_decode_props hTop hdec).2.2.1 pb hinner
  obtain ⟨_, _, hlt31⟩ := topStateTight_to_tightValid640 hTop
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨_, _, _, st, _, _, _, vn?, ch?, _, hw⟩ := hTop
  have hdec_eq : spqrDecodeState stBytes = .ok (pbToPqRatchetState (topPb st vn? ch?)) := by
    have hbeq : stBytes = encodeState (pbToPqRatchetState (topPb st vn? ch?)) := hw.htop.hbytes
    rw [hbeq] at hsize ⊢
    exact spqrDecodeState_encodeState (pbToPqRatchetState (topPb st vn? ch?)) hsize
  rw [hdec_eq] at hdec
  have hpre := Except.ok.inj hdec; subst hpre
  simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hinner
  cases hinner
  exact ⟨⟨st, hw.hbok, rfl⟩, hprops⟩

private theorem w4s2_topStateTight_intoPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb))
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    {sckaMsg : Message spqrPolyApi} {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hrecv : States.recv K st0 sckaMsg = .ok v) :
    w4s2_IntoPbStateGuard v.state := by
  obtain ⟨⟨st, hbok, rfl⟩, -⟩ := w4s2_topStateTight_fromPbStateGuard hTop hdec hinner
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st :=
    st_bCodec F st hbok.1
  rw [hcodec] at hfrom
  have hst0 := Except.ok.inj hfrom; subst hst0
  rcases v with ⟨key, st1⟩
  have hbok1 : BOkTight st1 := by
    cases hek : isEkSide st
    · exact st_bRecvCt_tight F K hek hbok hrecv
    · exact st_bRecvEk_tight F K hek hbok hrecv
  exact ⟨hbok1, st_bSize_tight F st1 hbok1⟩

private theorem w4s2_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hpre | ⟨evs₁, evs₂, rfl, he1, he2⟩
  · exact Or.inl (h1 evs hpre)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ he1, h2 evs₂ he2⟩

private theorem w4s2_spqrRecvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight
    {F : ShaCompress} {K : MlKem}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hFromPb_sub : ∀ pb evs, w4s2_FromPbStateGuard F pb → FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ g evs, w4s2_IntoPbStateGuard g.st → IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    {stBytes : Bytes} (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {evs : List AllocEvent}
    (h : SpqrRecvTightLinkedEnv F K
      (fun _ => tlb_DecodeStateTightEnvOf 109) FromPbEnv IntoPbEnv
      (w4s2_StatesRecvExactPairTightEnv K)
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    SpqrRecvC07C09aTightLinkedEnvOf 109 F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs := by
  rcases h with ⟨hTight, hLink⟩
  refine ⟨?_, hLink⟩
  rcases hTight with hfree | hseq
  · exact Or.inl hfree
  · refine Or.inr (w4s2_seqEnv_mono (fun _ hd => hd) (fun _ hafter => ?_) hseq)
    rcases hafter with hfree1 | ⟨hdec, hbr⟩
    · exact Or.inl hfree1
    · refine Or.inr ⟨hdec, ?_⟩
      rcases hbr with hless | hgt | ⟨hinner, heq⟩
      · exact Or.inl hless
      · exact Or.inr (Or.inl hgt)
      · refine Or.inr (Or.inr ⟨hinner, ?_⟩)
        have hPbG : w4s2_FromPbStateGuard F pb :=
          w4s2_topStateTight_fromPbStateGuard hTop hdec hinner
        rcases heq with hmdErr | heq
        · exact Or.inl hmdErr
        · refine Or.inr (w4s2_seqEnv_mono (fun _ hf => hf) (fun _ hmd => ?_) heq)
          rcases hmd with hfree2 | hfromSeq
          · exact Or.inl hfree2
          · refine Or.inr (w4s2_seqEnv_mono (fun evsF hf => hFromPb_sub pb evsF hPbG hf)
              (fun _ haf => ?_) hfromSeq)
            rcases haf with hfree3 | ⟨hfrom, hrecvSeq⟩
            · exact Or.inl hfree3
            · refine Or.inr ⟨hfrom, w4s2_seqEnv_mono
                (fun _ ⟨outA, selfA, msgA, hr⟩ =>
                  statesRecvExactTightEnv_sub_statesRecvProtoEnv' K
                    ⟨outA, selfA, msgA, st0, sckaMsg⟩ hfrom hr)
                (fun _ har => ?_) hrecvSeq⟩
              rcases har with hfree4 | ⟨hrecv, hxS, hv1c⟩
              · exact Or.inl hfree4
              · refine Or.inr ⟨hrecv, hxS, ?_⟩
                have hIntoG : w4s2_IntoPbStateGuard xSInto.st :=
                  hxS.symm ▸ w4s2_topStateTight_intoPbStateGuard hTop hdec hinner hfrom hrecv
                refine w4s2_seqEnv_mono (fun _ hc => hc) (fun _ he1 => ?_) hv1c
                rcases he1 with hfree5 | ⟨hc1, hc2, haddSeq⟩
                · exact Or.inl hfree5
                · refine Or.inr ⟨hc1, hc2, w4s2_seqEnv_mono (fun _ ha => ha) (fun _ he2 => ?_) haddSeq⟩
                  rcases he2 with hfree6 | hrkSeq
                  · exact Or.inl hfree6
                  · refine Or.inr (w4s2_seqEnv_mono (fun _ hrk => hrk) (fun _ he3 => ?_) hrkSeq)
                    rcases he3 with hfree7 | ⟨hrkOk, hintoSeq⟩
                    · exact Or.inl hfree7
                    · exact Or.inr ⟨hrkOk,
                        w4s2_seqEnv_mono (fun evsI hi => hIntoPb_sub xSInto evsI hIntoG hi)
                          (fun _ ht => ht) hintoSeq⟩

/-- `FitsEnv M lim st (fun _ => True)` is unsatisfiable because allocations exceeding
`MallocngMaxAllocSize` violate `withinMaxAlloc`. -/
theorem w4s2_not_fitsEnv_top {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    ¬ FitsEnv M lim st (fun _ => True) := by
  intro h
  have h1 := h [AllocEvent.alloc (MallocngMaxAllocSize + 1)] trivial
  have h2 : (AllocEvent.alloc (MallocngMaxAllocSize + 1)).withinMaxAlloc := h1.1.1
  dsimp only [AllocEvent.withinMaxAlloc] at h2
  omega

/-- Bridges `ContractsPlacedBudget.spqrRecvPlacedDispSpecXTOfEnv` to
`StoreKit.withLsCodeRoLoaded lsmpl (spqrRecvPlacedInnerDispSpecXTOfEnv ...)` on any `prog`/`entry`. -/
theorem w4s2_spqrRecvPlacedInnerDispSpecXTOfEnv_of_placedDispSpecXT [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {R : SpqrRecvModel} {Env : VecArg → VecArg → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry (spqrRecvPlacedDispSpecXTOfEnv A lim R Env)) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerDispSpecXTOfEnv M A lim R Env)) := by
  refine subroutine_ok_mono hok
    (fun ((st, msg, ret), stB) Fr s0 hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedDispSpecXTOfEnv, spqrRecvPlacedDispSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedRawDispSpecXOfEnv, lsLogOff] at hpre ⊢
      let H_sp : SepProp :=
        tokenInitPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim stB s0 ∗ stackAt s0.sp spqrRecvStack ∗ Fr
      have hpre' : s0.mem ⊨
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜st.bytes.length < 2 ^ 32 ∧ msg.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s0.sp.toNat⌝ ∗
          (⌜FitsEnv M lim stB (Env st msg)⌝ ∗
          (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret⌝ ∗
            H_sp))) := by
        dsimp only [H_sp]
        exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcro, hpre'⟩ := hpre'
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hbds, hpre'⟩ := hpre'
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfit, hpre'⟩ := hpre'
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx1, hx8⟩, hsp⟩ := hpre'
      have hcro' : CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem :=
        ⟨hcro.1, hcro.2⟩
      have hgoal : s0.mem ⊨
          ⌜st.bytes.length < 2 ^ 32 ∧ msg.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s0.sp.toNat⌝ ∗
          (⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret ∧
            FitsEnv M lim stB (Env st msg)⌝ ∗ H_sp)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hbds, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcro', ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hx8, hfit⟩, hsp⟩
      dsimp only [H_sp] at hgoal
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hgoal)
    (fun ((st, msg, ret), stB) Fr s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedDispSpecXTOfEnv, spqrRecvPlacedDispSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedRawDispSpecXOfEnv, lsLogOff] at hpost ⊢
      refine Satisfies.mono
        (sepConj_mono_left (sepConj_mono_right (Entails.sepExists_mono fun evs => ?_))) hpost
      apply Entails.pure_left
      rintro ⟨htr, hevs, hnp⟩
      exact Entails.pure_right hevs (Entails.pure_right ⟨htr, hnp⟩ (Entails.refl _)))
    (fun _ _ _ _ hpanic => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedDispSpecXTOfEnv, spqrRecvPlacedDispSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedRawDispSpecXOfEnv] at hpanic ⊢
      exact hpanic)

private theorem w4s2_spqrRecv_topStateGuarded_seam_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hDecPre_sub : ∀ g evs, TopStateTight W.C.F W.Q.K g.st.bytes →
      DecodePreEnv g evs → tlb_DecodeStateTightEnvOf 109 evs)
    (hDecPost_sub : ∀ g evs, TopStateTight W.C.F W.Q.K g.st.bytes →
      DecodePostEnv g evs → tlb_DecodeStateTightEnvOf 109 evs)
    (hFromPb_sub : ∀ pb evs, w4s2_FromPbStateGuard W.C.F pb →
      FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ (g : StatesIntoPbGhost W.C.F) evs, w4s2_IntoPbStateGuard g.st →
      IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    (hRecvC : SpqrRecvPlacedContractsOfEnv H_inner A lim W.C.F W.Q.K
      DecodePreEnv DecodePostEnv
      (InitInnerEnv W.C.F)
      FromPbEnv
      (fun g => w4s2_StatesRecvExactPairTightEnv W.Q.K g.self g.msg)
      IntoPbEnv
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerDispSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes))) := by
  refine w4s2_spqrRecvPlacedInnerDispSpecXTOfEnv_of_placedDispSpecXT
    (spqr_recv_placed_disp_ok_blockProgram_ext_of_contracts_ofEnv
      (fun (st msg : VecArg) => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (trTrapExternsPlaced_isPanic mmpl gh W)
      hRecvC
      (fun st _ _ _ _ _ =>
        spqrRecvTightLinkedEnv_nil_exists W.C.F W.Q.K
          (fun _ => tlb_DecodeStateTightEnvOf 109)
          (fun _ => StatesFromPbTightEnv)
          (fun _ => StatesIntoPbTightEnv)
          (StatesRecvProtoEnv' W.Q.K)
          st.bytes)
      (fun st msg s0 st_cost _ _ _ _ hfit => ?_))
  by_cases hTop : TopStateTight W.C.F W.Q.K st.bytes
  · refine spqrRecvBranchHyps_tightLinked
      (DecodeStateEnv' := fun _ => tlb_DecodeStateTightEnvOf 109)
      (StatesFromPbEnv' := FromPbEnv)
      (StatesIntoPbEnv' := IntoPbEnv)
      (StatesRecvEnv' := w4s2_StatesRecvExactPairTightEnv W.Q.K)
      st msg s0 st_cost
      (fun evs hpre => hDecPre_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpre)
      (fun evs hpost => hDecPost_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpost)
      (fun _ _ h => h)
      (fun _ _ _ h => h)
      (fun _ _ h => h)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =>
        FitsEnv.mono
          (fun evs hevs _ =>
            ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
              w4s2_spqrRecvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight
                hFromPb_sub hIntoPb_sub hTop hevs⟩)
          hfit)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs _ =>
        ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
          w4s2_spqrRecvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight
            hFromPb_sub hIntoPb_sub hTop hevs⟩)
  · exact False.elim
      (w4s2_not_fitsEnv_top (FitsEnv.mono (fun _ _ h => False.elim (hTop h)) hfit))

private theorem w4s2_hookSat_withAllocVmPreserved_memmove_of_zero
    {H : String → Option (State → State)} {sym : String} (hookStack : Nat)
    (h : HookSat H sym (withAllocVmPreserved (sessionMemmoveBoundedSpec 0))) :
    HookSat H sym (withAllocVmPreserved (sessionMemmoveBoundedSpec hookStack)) := by
  refine ProofLib.HookSat.mono h fun ⟨base, buf, dst, src, len⟩ R s0 hpre =>
    ⟨(base, buf, dst, src, len), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withAllocVmPreserved, sessionMemmoveBoundedSpec,
      sessionMemmoveSpec, libcMemmoveSpec, stackAt] at hpre ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp]
    ac_nf at hpre ⊢
  · dsimp only [withAllocVmPreserved, sessionMemmoveBoundedSpec,
      sessionMemmoveSpec, stackAt] at hpost ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp] at hpost
    ac_nf at hpost ⊢

private theorem w4s2_statesRecv_recv_exactTight_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      spqrLibcruxHmacSym
      (withLsRet (LibsignalBinary.Heap.SpecBudget.libcruxHmacBudgetSpec W.C.F M A lim))) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvPlacedSpecOfEnv M A lim W.C.F W.Q.K
          (fun g => w4s2_StatesRecvExactPairTightEnv W.Q.K g.self g.msg))) := by
  let ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hExt := w4s2_trTrap_hExt mmpl gh W
  have hExt_wp := w4s2_hExt_withPanics mmpl gh W hExt
  letI : HkdfPlacedHooksExactSat W.C.F (Rust.withPanics ext) :=
    HkdfPlacedHooksExactSat.of_allocHooks_ext (mmpl := mmpl) (W := W)
      hA.toCliGhostAllocHooks hF hExt_wp
  have hmemset_wp := hookSat_of_eq (hExt_wp _ (by decide))
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  letI : HkdfPlacedHooksExactBudgetSat W.C.F (Rust.withPanics ext) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hmemset_wp
  have hC := statesRecvPlacedContracts_of_ro_leaves_sat
    (cliRecvCt2PlacedAllocExt mmpl gh W hA hExt)
    (w4s2_hookSat_withAllocVmPreserved_memmove_of_zero growOneStack
      (hookSat_of_eq (hExt_wp _ (by decide))
        (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W hA.extraOk)))
    hmemset_wp
    (hookSat_of_eq (hExt_wp _ (by decide))
      (cliGhostExterns_mlkemValidatePk_budget_sat gh (cliExternsPlaced mmpl W) hA.extraOk hK))
    (hookSat_of_eq (hExt_wp _ (by decide))
      (cliGhostExterns_mlkemEncaps2_budget_sat gh (cliExternsPlaced mmpl W) hA.extraOk hK))
    (hookSat_of_eq (hExt_wp _ (by decide))
      (cliGhostExterns_mlkemDecapsAt_budget_sat gh (cliExternsPlaced mmpl W) hA.extraOk 36864
        (by decide) (by decide) hK))
    (hookSat_of_eq (hExt_wp _ (by decide)) hHmac)
    (hA.onceCallHookOk_ext mmpl W hExt)
  have h332 := states_recv_placed_ok_x_exactTight A lim W.C.F W.Q.K ext hC
  have h0 :=
    LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
      (callerProg := spqrRecvPlacedProg ext) (i := 329) h332
  exact subroutine_ok_mono h0
    (fun (g, stB) _ _ hpre => by
      dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
        at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
      exact Entails.pure_mono fun ⟨h1, h2, h3, h4, hfit, hlr⟩ =>
        ⟨h1, h2, h3, h4, hfit.mono (fun evs hevs => ⟨g.outA, g.selfA, g.msgA, hevs⟩), hlr⟩)
    (fun (g, stB) _ _ _ hpost => by
      dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
        at hpost ⊢
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, hevs⟩ =>
        ⟨h1, ⟨g.outA, g.selfA, g.msgA, hevs⟩⟩)
    (fun _ _ _ _ hp => hp)

private theorem w4s2_decodeStateCalleeContractsClPlacedX_cliExt [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap A lim ext := by
  have hExt_wp := w4s2_hExt_withPanics mmpl gh W hExt
  exact mkDecodeStateCalleeContractsClPlacedX_of_blocks
    (cliDeallocBudget_at_block mmpl gh W hA hExt_wp (i := 325))
    (fun stk _ _ => cliLibcMemcpyBudget_at_block mmpl gh W hA hExt_wp stk (i := 325))
    (fun stk _ _ => cliSessionMemcpyBudget_at_block mmpl gh W hA hExt_wp stk (i := 325))
    (cliFrom_261_cl mmpl gh W hA hExt)
    (decodeErrorPush_of_merge (cliPushMerge_257_cl mmpl gh W hA hExt))
    (cliVarint_291_cl mmpl gh W hA hExt)
    (cliSkipBudget_263_cl mmpl gh W hA hExt)
    (chainParamsMerge_decodeState_of_prost (cliChainParams_294_cl mmpl gh W hA hExt))
    (cliGrowOne_356_cl mmpl gh W hA hExt)
    (cliDrop_267_cl mmpl gh W hA hExt)
    (cliDrop_270_cl mmpl gh W hA hExt)
    (cliBytesExact_290_cro mmpl gh W hA hExt)
    (epochDirectionMerge_decodeState_of_prost (cliEpochDir_299_cl mmpl gh W hA hExt))
    (cliV1StateMerge_closed_cl mmpl gh W hA hExt)

private theorem w4s2_decodeState_recv_tight109_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim 80
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := by
  let ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hc := w4s2_decodeStateCalleeContractsClPlacedX_cliExt mmpl gh W hA
    (w4s2_trTrap_hExt mmpl gh W)
  have hEpochDir := e2ar_epochDirectionMerge_blk325_cl_ok_tight hc
  have hDec325 := e2a_decodeState_cl_placed_ok_of_v1Merge_109
    (F := W.C.F) (K := W.Q.K) hc hEpochDir hV1Merge
  have hblk325 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := by
    have h0 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (blkPl_325).base
        (withLsCodeRoLoaded lsmpl
          (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := hDec325
    rwa [IsLsBlockProg.eq_blockProgram
          (prog := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)),
        ls_blockPlacement_base (i := 325)] at h0
  exact LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
    (callerProg := spqrRecvPlacedProg ext) (i := 329) hblk325

/-- Establishes `SpqrV1PlacedSeamsOfEnv` at `w4s2_SpqrRecvTopStateGuardedBytesEnv` for arbitrary
`brkStart` and explicit `hHmac` and `hFmt` `HookSat` witnesses. -/
theorem w4s2_spqrSeams_topStateGuarded_of_hmac [LibsignalPlacement]
    (mmpl : MultiPlacement) (ghFixed : CliGhostHooks)
    (W : CliHooks) (hF : W.C.F = sha256Compress)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hHmac : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (LibsignalBinary.Heap.SpecBudget.libcruxHmacBudgetSpec W.C.F fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)))
    (hFmt : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) spqrFormatInnerSym
      (formatInnerCallCliLsSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)) :
    SpqrV1PlacedSeamsOfEnv fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits mmpl ghFixed W
      (LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget.InitialStateEnv W.C.F)
      (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge.gu2b_SpqrSendCoinsExactFromPbLinkedEnv
        W.C.F W.Q.K) := by
  have hBase :=
    gu2b_spqrV1PlacedSeams_exactFromPb_of_hmac mmpl ghFixed W hGSpqr hF hK hHmac hFmt
  have hRecvBase := cliSpqrRecvPlacedContracts_exact mmpl ghFixed W hGSpqr hF hK hHmac hFmt
  have hV1Merge :=
    v1StateMergeBlk325_cli_of_hExt mmpl ghFixed W
      (w4s2_trTrap_hExt mmpl ghFixed W) hGSpqr.toCliGhostAllocHooks
  have hDec := w4s2_decodeState_recv_tight109_ok mmpl ghFixed W hGSpqr.toCliGhostAllocHooks hV1Merge
  have hFromPb := gu2b_cliSpqrRecv_statesFromPb_fromPbGuard_ok mmpl ghFixed W hGSpqr
  have hRecv := w4s2_statesRecv_recv_exactTight_ok mmpl ghFixed W hF hK hGSpqr hHmac
  exact
    { spqrInitialState := hBase.spqrInitialState
      spqrRecv := w4s2_spqrRecv_topStateGuarded_seam_of_contracts mmpl ghFixed W
        (DecodePreEnv := tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (DecodePostEnv := tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (FromPbEnv := gu2b_StatesFromPbGuardedEnv W.C.F)
        (IntoPbEnv := StatesIntoPbExactEnv)
        (fun _ _ hTop h => tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight hTop h)
        (fun _ _ hTop h => tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight hTop h)
        (fun _ _ hG hf => hf hG)
        (fun _ _ hG hEnv =>
          statesIntoPbExactEnv_tight (statesIntoPbTightDom_of_bokTight hG.1) hEnv)
        { dealloc_ok := hRecvBase.dealloc_ok
          memcpy_ok := hRecvBase.memcpy_ok
          dropEpochSlice_ok := hRecvBase.dropEpochSlice_ok
          dropOptProtoInnerState_ok := hRecvBase.dropOptProtoInnerState_ok
          dropOptProtoChain_ok := hRecvBase.dropOptProtoChain_ok
          dropChain_ok := hRecvBase.dropChain_ok
          dropPqRatchetState_ok := hRecvBase.dropPqRatchetState_ok
          dropStates_ok := hRecvBase.dropStates_ok
          decodeState_ok := hDec
          initInner_ok := hRecvBase.initInner_ok
          chainFrom_ok := hRecvBase.chainFrom_ok
          chainFromPb_ok := hRecvBase.chainFromPb_ok
          chainNew_ok := hRecvBase.chainNew_ok
          chainAddEpoch_ok := hRecvBase.chainAddEpoch_ok
          chainRecvKey_ok := hRecvBase.chainRecvKey_ok
          chainIntoPb_ok := hRecvBase.chainIntoPb_ok
          messageDeserialize_ok := hRecvBase.messageDeserialize_ok
          statesFromPb_ok := hFromPb
          statesRecv_ok := hRecv
          statesIntoPb_ok := hRecvBase.statesIntoPb_ok
          encodeToVec_ok := hRecvBase.encodeToVec_ok
          h_inner_eq := hRecvBase.h_inner_eq }
      spqrSendCoins := hBase.spqrSendCoins }

/-- Establishes `SpqrV1PlacedSeamsOfEnv` at `w4s2_SpqrRecvTopStateGuardedBytesEnv` for arbitrary `brkStart`. -/
theorem w4s2_spqrSeams_topStateGuarded [LibsignalPlacement]
    (mmpl : MultiPlacement) (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (hF : W.C.F = sha256Compress)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hHmacLookup : ghFixed.extra.lookup spqrLibcruxHmacSym =
      some (libcruxHmacHookMallocng mmpl W.C.F))
    (γ : GhostName) (tp brkStart : BitVec 64)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hFmt : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) spqrFormatInnerSym
      (formatInnerCallCliLsSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)) :
    SpqrV1PlacedSeamsOfEnv fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits mmpl ghFixed W
      (LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget.InitialStateEnv W.C.F)
      (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge.gu2b_SpqrSendCoinsExactFromPbLinkedEnv
        W.C.F W.Q.K) :=
  w4s2_spqrSeams_topStateGuarded_of_hmac mmpl ghFixed W hF hK γ tp brkStart hGSpqr
    (hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp brkStart cliBudgetLimits ghFixed W hPl_mng hHmacLookup)
    hFmt

end SpqrTopStateGuarded

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2

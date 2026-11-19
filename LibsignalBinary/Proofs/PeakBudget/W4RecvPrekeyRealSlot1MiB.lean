/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
import LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.E2E.Seed.Defs
import LibsignalBinary.Proofs.PeakBudget.W4InnerPeakSpec

/-!
# Parametric `(smallFileCap, maxCt)` & Split-Directory `recv-prekey` Slot Specs

Parametric `(smallFileCap, maxCt)` and per-directory split generalizations of
`W4RecvPrekeyRealSlot.W4RecvPrekeyRealDom`:
1. Parameterizes `ctLen ≤ maxCt` (`W4TryDecryptCallDomOf`, `W4TryDecryptPathACDomOf`,
   `W4FailedTdDomOf`, `W4ArchivedTrialDomOf`, `W4RecvPrekeyRealDomOf`).
2. Provides Variant (i) (`W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes`, uniform `2 MiB`
   directory cap and `1 MiB` message cap) and Variant (ii) (`W4RecvPrekeyRealDomSplit 4096
   sessionCapBytes msgCapBytes`, splitting `[own, peers, signed, oneTime] ≤ 4096` from
   `kpkDir ≤ 2 MiB`) `SingleSlotFineSpec` instances.
3. Proves closed 5-slot whole-`main` `< 90%` (`≤ 966,367,641` B) and `≤ 1 GiB` RAM bounds by
   kernel `decide`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB

open CryptoGames.LibsignalSession
  (MessageKeyGenerator ReceiverChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost VecPin)
open CryptoVerification.LibsignalSpqrV1 (Bytes MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost addressText keyName pathOf)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliDecoupledRamNeed cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
   cliMaxAddrTextBytes cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (dropClonedSessionEvents_groupSpec dropVecVecClone1Events_groupSpec
   optTailCloneEvents_groupSpec phaseGroupSpec_append_eq recordSerializeDomFineGrpS
   segCloneDomFineGrpS segCloneEnv_dom_fine_groupSpec senderChainCloneDomFineGrpS
   senderChainCloneEnv_dom_fine_groupSpec serializeSomeCancelEnv_groupSpec vecCloneEvents_groupSpec
   vecVecClone1Events_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec (m3PhaseDeltaCum_tight m6DeltaCum)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (pksmSliceCum)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (cliRealNinetyPctOneGiB cliRealPksmCumCap cliRealPksmGrpSCap cliRealPksmLiveCap
   cliRealPksmPeakCap cliRealPksmReqCap
   cliRun1MiBCustomPksmCum cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmMaxReq
   cliRun1MiBCustomPksmPeak cliRunOpenedCustomPksmGrpS
   w3InitRealCum w3InitRealGrpS w3InitRealLive w3InitRealMaxReq w3InitRealPeak)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightCumOf cliMainTightGrpCountOf cliMainTightGrpSOf cliMainTightLiveOf
   cliMainTightPeakOf cliMainTightRamNeedOf cliMainTightReqOf)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec FreeOnlyAlign16Evs IterSeqEnv PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (RecordSerializeCancelEnv dropClonedSessionEvents sessLoadPollTightDeltaCum
   sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak sessLoadPollTightMaxReq
   sessStorePollMaxReq sessStorePollTightDeltaCum sessStorePollTightDeltaLive
   sessStorePollTightDeltaPeak smallStorePollTightDeltaCum smallStorePollTightDeltaLive
   smallStorePollTightDeltaPeak smallStorePollTightMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (SerializePrev1CancelEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12 w2TryDecryptFailTightGroupS_split_12
   w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738
   w2TryDecryptSeeds12GroupS_split_12 w2TryDecryptSeedsEnv_12_linked_fine_groupSpec_split_12
   w2TryDecryptTightEnv_linked_fine_groupSpec_split_12
   w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit (w2TryDecryptTightGroupS_split_12)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (w1SendRealDcanCum w1SendRealDcanGrpS w1SendRealDcanLive w1SendRealDcanMaxReq w1SendRealDcanPeak)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (SessionCloneDom ghostCloneValid_of_sessionGhostValid serialize_dom_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (w2CmkChainTightLive w2TryDecryptMaxReq w2TryDecryptTightLive w2TryDecryptTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak (DoublingChainLe)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (optDeallocListEvs optDeallocListLarge)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanGrpS w2RecvWhisperRealDcanLive
   w2RecvWhisperRealDcanMaxReq w2RecvWhisperRealDcanPeak)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
  (w2TryDecryptGenSeeds738Cum w2TryDecryptSeeds738Cum w2TryDecrypt_genSeeds_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv phaseCredit_archivedTrialLoop_le4)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BoundedEvs W4InitBobSpqrEnv W4StageP2OverBobEnv phaseCredit_w4BoundedEvs_small
   phaseCredit_w4InitBob_small phaseCredit_w4StageP2OverBob_small w4InitBobOuterCum)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers (phaseCreditSpec_ite_nil phaseCreditSpec_or4)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (W4DecryptPrekeyPathAEnv W4DecryptPrekeyPathBEnv W4DecryptPrekeyPathCEnv
   W4StageP2PathACliEnv W4StageP2PathCCliEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (W4StageP1UntrustedCliEnv W4StageP4PathACliEnv W4StageP4PathCCliEnv opened_all_dirDomainCaps
   phaseCreditSpec_seq_freeOnly_exact w4SpqrInitCum)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
  (W4DecryptPrekeyTightDom w4DecryptPrekeySplitSlot_opened_fine_phaseCredit
   w4DecryptPrekeySplitTightCum w4DecryptPrekeySplitTightLive w4DecryptPrekeySplitTightMaxReq
   w4DecryptPrekeySplitTightPeak w4StageP1OkCli_fine_phaseCredit
   w4StageP1UntrustedCli_fine_phaseCredit w4StageP2Matched_dom_fine_phaseCredit
   w4StageP3_fine_phaseCredit_tight w4StageP4MatchedCli_dom_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (ChainRecvKeyZeroSkip FreshBobPrev1Dom fineOptLarge optLargeCost_fine_eq
   tryDecryptCloneFail_dom_fine_cancel_phaseCredit w4ErrTail_fine_phaseCredit_tight
   w4KeyIdSmallStoreStep16_fine_phaseCredit w4PeerSmallStoreStep32_fine_phaseCredit
   w4SessStorePrev1Step_freshBob_fine_phaseCredit w4SessStoreStep_dom_fine_phaseCredit
   w4SmallStoreStep16_fine_phaseCredit w4SmallStoreStep32_fine_phaseCredit
   w4SpqrInit32_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4ArchivedTrial W4FailedTdCancelEnv W4FailedTryDecryptCall W4RecvPrekeyRealDom
   W4RecvPrekeyRealEnv W4RecvPrekeyRealParams W4RecvPrekeyTryDecACEnv W4TrialDecEnv W4TrialRunEnv
   W4TryDecryptCall W4TryDecryptFailLinkedEnv W4TryDecryptPathACEnv W4TryDecryptPathBEnv
   mkW4RecvPrekeySlotParams segCloneFreshBobFineGrpS serializePrev1FreshBobFineGrpS
   spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec w4RealFailTdCum w4RealTdACCum w4RealTrialCum
   w4RealTrialFineGrpS w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
  (archivedTrialLoop_le4_groupSpec phaseGroupSpec_ite_nil w4BoundedEvs_groupSpec w4ErrTailFineGrpS
   w4ErrTail_fine_groupSpec w4InitBobSpqrFineGrpS w4SmallStoreStep16FineGrpS
   w4SmallStoreStep16_fine_groupSpec w4SmallStoreStep32FineGrpS w4StageP1OkBaseFineGrpS
   w4StageP1OkCli_fine_groupSpec w4StageP1UntrustedBaseFineGrpS w4StageP1UntrustedCli_fine_groupSpec
   w4StageP2Matched_groupSpec w4StageP2OverBob_fine_groupSpec w4StageP2PathACliFineGrpS
   w4StageP2PathACli_fine_groupSpec w4StageP3FineGrpS w4StageP3_fine_groupSpec
   w4StageP4MatchedCli_fine_groupSpec w4StageP4PathACli_fine_groupSpec
   w4StageP4PathCCli_fine_groupSpec w4TryDecryptCloneFail_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (W4TryDecryptCloneFailEnv)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec (pksmTryFromCapDeltaGrpS)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
  (SessionDropCapsOk chainPairFreeEvents dropSessionStructureLocal1Events dropVecChainEvents
   dropVecMessageKeyEvents mkFreeEvents optCkCapVal optTailCapVal pinFreeEvents senderFreeEvents
   sgnCapFreeEvents ssFirst3FreeEvents ssTail3FreeEvents stepEvents_dropSessionStructureLocal1_bounds
   vec104FreeEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (ssStateLargeLive)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserLargeLive)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq
   deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec sessDeserializeCancelEnv_fine_groupSpec
   sessDeserializeCancelEnv_fine_phaseCreditSpec sessDeserializeCancelEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv segCloneEvents)

/-! ## Parametric `(smallFileCap, maxCt)` & Split-Directory Domain Predicates -/

/-- Pure domain bounds for one `W4TryDecryptCall` parameterized by `maxCt`. -/
structure W4TryDecryptCallDomOf (F : ShaCompress) (K : MlKem) (maxCt : Nat)
    (td : W4TryDecryptCall F) : Prop where
  dh_le : td.dhCap ≤ 5
  caps_len : td.caps.length ≤ 12
  chain_le : DoublingChainLe 2000 td.caps
  top_tight : TopStateTight F K td.stBytes
  ct_le : td.ctLen ≤ maxCt

/-- Pure domain bounds for a fresh-Bob Path A / Path C `try_decrypt` parameterized by `maxCt`. -/
structure W4TryDecryptPathACDomOf (F : ShaCompress) (K : MlKem) (maxCt : Nat)
    (td : W4TryDecryptCall F) : Prop where
  base : W4TryDecryptCallDomOf F K maxCt td
  zero_skip : ChainRecvKeyZeroSkip td.w.xRk

/-- Pure domain bounds for a failed `try_decrypt` trial parameterized by `maxCt`. -/
structure W4FailedTdDomOf (F : ShaCompress) (K : MlKem) (maxCt : Nat)
    (fc : W4FailedTryDecryptCall F) : Prop where
  td_dom : W4TryDecryptCallDomOf F K maxCt fc.td
  align_le : ∀ p ∈ fc.failDropPairs, p.2 ≤ 16
  cancel_live : w2CmkChainTightLive 2000 + 605066 ≤ optDeallocListLarge fineCostModel fc.failDropPairs

/-- Pure domain bounds for one archived-session trial parameterized by `maxCt`. -/
structure W4ArchivedTrialDomOf (F : ShaCompress) (K : MlKem) (maxCt : Nat)
    (x : W4ArchivedTrial F) : Prop where
  enc_le : (encodeRecord x.r_dec).length ≤ deserCancelFineMaxReq
  live_le_peak : sessDeserLargeLive fineCostModel x.r_dec ≤ deserCancelFinePeak
  live_le_drop :
    sessDeserLargeLive fineCostModel x.r_dec ≤ ssStateLargeLive fineCostModel x.G_dec x.st_dec
  drop_caps : SessionDropCapsOk x.G_dec x.st_dec
  tr_gv : SessionGhostValid x.G_tr x.ses_tr
  tr_dom : SessionCloneDom 286196 x.ses_tr
  tr_fail : W4FailedTdDomOf F K maxCt x.fc_tr

/-- Parametric uniform-directory domain bundle (`Variant (i)` at `(sessionCapBytes, msgCapBytes)`),
generalizing `W4RecvPrekeyRealDom` over `(smallFileCap, maxCt)`. -/
structure W4RecvPrekeyRealDomOf (smallFileCap maxCt : Nat)
    (R : W4RecvPrekeyRealParams) : Prop where
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  outer_dom : W4DecryptPrekeyTightDom (mkW4RecvPrekeySlotParams R)
    2097152 smallFileCap 286196 286196 2097152 286196 2097152 16384 2097152 2457152 4096
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomOf R.F R.K maxCt R.fc_cur
  trials_dom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDomOf R.F R.K maxCt x
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomOf R.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomOf R.F R.K maxCt R.td_AC

/-- Per-directory split domain bundle (`Variant (ii)` at `(4096, sessionCapBytes, msgCapBytes)`),
separating `[own, peers, signed, oneTime] ≤ smallFileCap` from `kpkDir ≤ kpkFileCap`. -/
structure W4RecvPrekeyRealDomSplit (smallFileCap kpkFileCap maxCt : Nat)
    (R : W4RecvPrekeyRealParams) : Prop where
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  nonKpk_small_cap : ∀ d ∈ [StoresGhost.opened.identity.own, StoresGhost.opened.identity.peers,
      StoresGhost.opened.signed, StoresGhost.opened.oneTime],
    ∀ n bs, R.rd R.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap
  kpk_cap : ∀ n bs, R.rd R.files (pathOf R.kpkDir.path n) = .ok bs → bs.length ≤ kpkFileCap
  outer_dom : W4DecryptPrekeyTightDom (mkW4RecvPrekeySlotParams R)
    2097152 (max smallFileCap kpkFileCap) 286196 286196 2097152 286196 2097152
    16384 2097152 2457152 4096
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomOf R.F R.K maxCt R.fc_cur
  trials_dom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDomOf R.F R.K maxCt x
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomOf R.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomOf R.F R.K maxCt R.td_AC

/-! ## Parametric & Closed `Nat` Constants for Variants (i) and (ii) -/

@[expose] def w4FailTdPeakOf (maxCt : Nat) : Nat := w2TryDecryptTightPeak 2000 605066 621350 maxCt
@[expose] def w4TdMaxReqOf (maxCt : Nat) : Nat := w2TryDecryptMaxReq 5 2000 302480 maxCt
@[expose] def w4TrialPeakOf (maxCt : Nat) : Nat := 1080975 + fineOptLarge 286196 + w4FailTdPeakOf maxCt
@[expose] def w4TrialMaxReqOf (maxCt : Nat) : Nat := max (max (max 208000 286196) (w4TdMaxReqOf maxCt)) 192
@[expose] def w4TdBLiveOf (maxCt : Nat) : Nat := w2TryDecryptTightLive 2000 605066 maxCt
@[expose] def w4TdACLiveOf (maxCt : Nat) : Nat := w2TryDecryptTightLive 2000 294391 maxCt
@[expose] def w4TdACPeakOf (maxCt : Nat) : Nat := w2TryDecryptTightPeak 2000 294391 294391 maxCt

/-- Parametric uniform-`smallFileCap` `Δcum` (`w4DecryptPrekeySplitTightCum`). -/
@[expose] def w4RecvPrekeyRealCumOf (smallFileCap : Nat) : Nat :=
  w4DecryptPrekeySplitTightCum 2097152 smallFileCap 0 deserCancelFineCum
    w4RealFailTdCum deserCancelFineCum w4RealTrialCum 9923
    w4RealFailTdCum w4RealTdACCum 4096

/-- Parametric uniform-`smallFileCap` `Δlive` (`w4DecryptPrekeySplitTightLive`). -/
@[expose] def w4RecvPrekeyRealLiveOf (smallFileCap maxCt : Nat) : Nat :=
  w4DecryptPrekeySplitTightLive 2097152 smallFileCap 0 deserCancelFineLive
    2097152 2097152 2457152 (w4TdBLiveOf maxCt) (w4TdACLiveOf maxCt)

/-- Parametric uniform-`smallFileCap` `Δpeak` (`w4DecryptPrekeySplitTightPeak`). -/
@[expose] def w4RecvPrekeyRealPeakOf (smallFileCap maxCt : Nat) : Nat :=
  w4DecryptPrekeySplitTightPeak 2097152 smallFileCap 0 deserCancelFineLive deserCancelFinePeak
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    (w4FailTdPeakOf maxCt) deserCancelFinePeak (w4TrialPeakOf maxCt)
    (w4TdBLiveOf maxCt) (w4FailTdPeakOf maxCt) (w4TdACLiveOf maxCt) (w4TdACPeakOf maxCt)

/-- Parametric uniform-`smallFileCap` `maxReq` (`w4DecryptPrekeySplitTightMaxReq`). -/
@[expose] def w4RecvPrekeyRealMaxReqOf (smallFileCap maxCt : Nat) : Nat :=
  w4DecryptPrekeySplitTightMaxReq 2097152 smallFileCap 0 deserCancelFineMaxReq
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    (w4TdMaxReqOf maxCt) deserCancelFineMaxReq (w4TrialMaxReqOf maxCt) 192
    (w4TdMaxReqOf maxCt) (w4TdMaxReqOf maxCt) 4096

/-- Per-directory split `Δcum` separating `smallCap` from `kpkCap`. -/
def w4RecvPrekeySplitDirCum (smallCap kpkCap : Nat) : Nat :=
  let cL := 488 + sessLoadPollTightDeltaCum 2097152 deserCancelFineCum
  let c32_s := 738 + smallStorePollTightDeltaCum smallCap 0
  let c32_k := 738 + smallStorePollTightDeltaCum kpkCap 0
  let c16_s := 488 + smallStorePollTightDeltaCum smallCap 0
  let c16_k := 488 + smallStorePollTightDeltaCum kpkCap 0
  let cP1Ok := cL + c32_s
  let cUntr := cP1Ok + 9619
  let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 0
  let cSt1 := 738 + sessStorePollTightDeltaCum 1184912 0
  let cPathB := cP1Ok + (4 * (deserCancelFineCum + w4RealTrialCum) + (8420940 + 9923)) +
    (w4RealFailTdCum + 8186) + (c32_s + cSt0)
  let cPathA := cP1Ok + ((4 * c16_s + c16_k) + w4InitBobOuterCum 4096 + w4SpqrInitCum 32 + 8186) +
    (w4RealTdACCum + 8186) + (c32_s + c32_k + c16_s + cSt0)
  let cPathC := cP1Ok +
    ((8277456 + w4RealFailTdCum + 8186) + 4 * (deserCancelFineCum + w4RealTrialCum) +
      (4 * c16_s + c16_k) + (8420940 + 9923 + w4InitBobOuterCum 4096 + w4SpqrInitCum 32) + 8186) +
    (w4RealTdACCum + 8186) + (c32_s + c32_k + c16_s + cSt1)
  max (max cUntr cPathB) (max cPathA cPathC)

/-- Per-directory split `Δlive` separating `smallCap` from `kpkCap`. -/
def w4RecvPrekeySplitDirLive (smallCap kpkCap maxCt : Nat) : Nat :=
  let l_tdB := w4TdBLiveOf maxCt
  let l_tdAC := w4TdACLiveOf maxCt
  let lL := sessLoadPollTightDeltaLive 2097152 deserCancelFineLive
  let l_s := smallStorePollTightDeltaLive smallCap 0
  let l_k := smallStorePollTightDeltaLive kpkCap 0
  let lP1 := lL + l_s
  let lSt0 := sessStorePollTightDeltaLive (fineOptLarge 2097152) 0
  let lSt1 := sessStorePollTightDeltaLive (fineOptLarge 2457152) 0
  let lUntr := lP1
  let lPathB := lP1 + fineOptLarge 2097152 + l_tdB + (l_s + lSt0)
  let lPathA := lP1 + (4 * l_s + l_k) + l_tdAC + (l_s + l_k + l_s + lSt0)
  let lPathC := lP1 + ((4 * l_s + l_k) + fineOptLarge 2097152) + l_tdAC + (l_s + l_k + l_s + lSt1)
  max (max lUntr lPathB) (max lPathA lPathC)

/-- Per-directory split raw `Δpeak` before clamping with `Δlive`. -/
def w4RecvPrekeySplitDirRawPeak (smallCap kpkCap maxCt : Nat) : Nat :=
  let p_cur := w4FailTdPeakOf maxCt
  let p_dec := deserCancelFinePeak
  let p_tr := w4TrialPeakOf maxCt
  let l_tdB := w4TdBLiveOf maxCt
  let p_tdB := w4FailTdPeakOf maxCt
  let l_tdAC := w4TdACLiveOf maxCt
  let p_tdAC := w4TdACPeakOf maxCt
  let lL := sessLoadPollTightDeltaLive 2097152 deserCancelFineLive
  let pL := sessLoadPollTightDeltaPeak 2097152 deserCancelFinePeak
  let l_s := smallStorePollTightDeltaLive smallCap 0
  let p_s := smallStorePollTightDeltaPeak smallCap 0
  let l_k := smallStorePollTightDeltaLive kpkCap 0
  let p_k := smallStorePollTightDeltaPeak kpkCap 0
  let lP1 := lL + l_s
  let pP1 := max pL (lL + max p_s l_s)
  let pSt0 := sessStorePollTightDeltaPeak
    (1080975 + fineOptLarge 286196 + fineOptLarge 2097152) 0
  let pSt1 := sessStorePollTightDeltaPeak
    (fineOptLarge 16384 + fineOptLarge 2097152 + fineOptLarge 2457152) 0
  let pOver := 1080975 + fineOptLarge 286196 + fineOptLarge 2097152
  let lOver := fineOptLarge 2097152
  let pPeakB :=
    let pP2B := max (p_dec + p_tr) pOver
    let pP3B := max p_tdB l_tdB
    let pP4B := max p_s (l_s + pSt0)
    max pP1 (lP1 + max pP2B (lOver + max pP3B (l_tdB + pP4B)))
  let pPeakA :=
    let pP2A := max p_s (l_s + max p_k (l_k + max p_s (l_s + max p_s (l_s + max p_s l_s))))
    let pP3A := max p_tdAC l_tdAC
    let pP4A := max p_s (l_s + max p_k (l_k + max p_s (l_s + pSt0)))
    max pP1 (lP1 + max pP2A ((4 * l_s + l_k) + max pP3A (l_tdAC + pP4A)))
  let pPeakC :=
    let pP2Store := max p_s (l_s + max p_k (l_k + max p_s (l_s + max p_s
      (l_s + max pOver (lOver + max p_s l_s)))))
    let pP2C := max (1080975 + fineOptLarge 286196 + p_cur) (max (p_dec + p_tr) pP2Store)
    let pP3C := max p_tdAC l_tdAC
    let pP4C := max p_s (l_s + max p_k (l_k + max p_s (l_s + pSt1)))
    max pP1 (lP1 + max pP2C (((4 * l_s + l_k) + lOver) + max pP3C (l_tdAC + pP4C)))
  max (max pP1 pPeakB) (max pPeakA pPeakC)

/-- Per-directory split `Δpeak` (`max rawPeak live`). -/
def w4RecvPrekeySplitDirPeak (smallCap kpkCap maxCt : Nat) : Nat :=
  max (w4RecvPrekeySplitDirRawPeak smallCap kpkCap maxCt)
    (w4RecvPrekeySplitDirLive smallCap kpkCap maxCt)

/-- Per-directory split `maxReq`. -/
def w4RecvPrekeySplitDirMaxReq (smallCap kpkCap maxCt : Nat) : Nat :=
  let r_td := w4TdMaxReqOf maxCt
  let r_tr := w4TrialMaxReqOf maxCt
  let rL := max 24 (sessLoadPollTightMaxReq 2097152 deserCancelFineMaxReq)
  let r32_s := max 32 (smallStorePollTightMaxReq smallCap 0)
  let r32_k := max 32 (smallStorePollTightMaxReq kpkCap 0)
  let r16_s := max 16 (smallStorePollTightMaxReq smallCap 0)
  let r16_k := max 16 (smallStorePollTightMaxReq kpkCap 0)
  let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 286196) 2097152) 0)
  let rSt1 := max 32 (sessStorePollMaxReq (max (max 208000 16384) (max (max 24 2097152) 2457152)) 0)
  max (max rL (max (max r32_s r32_k) (max (max r16_s r16_k) 40)))
    (max (max (max (max 208000 286196) r_td) (max deserCancelFineMaxReq r_tr))
      (max (max (max (max 208000 286196) 2097152) 192)
        (max (max (max r_td r_td) 192) (max (max 4096 4224) (max rSt0 rSt1)))))

/-- Variant (i) closed constants at `(sessionCapBytes, msgCapBytes)`:
`cum = 288,625,123`, `live = 30,610,803`, `peak = 32,716,150`, `maxReq = 2,457,152`. -/
@[expose] def w4RecvPrekeyReal1MiB_i_Cum : Nat := w4RecvPrekeyRealCumOf sessionCapBytes
@[expose] def w4RecvPrekeyReal1MiB_i_Live : Nat := w4RecvPrekeyRealLiveOf sessionCapBytes msgCapBytes
@[expose] def w4RecvPrekeyReal1MiB_i_Peak : Nat := w4RecvPrekeyRealPeakOf sessionCapBytes msgCapBytes
@[expose] def w4RecvPrekeyReal1MiB_i_MaxReq : Nat := w4RecvPrekeyRealMaxReqOf sessionCapBytes msgCapBytes

theorem w4RecvPrekeyReal1MiB_i_eq :
    w4RecvPrekeyReal1MiB_i_Cum = 288625123 ∧
    w4RecvPrekeyReal1MiB_i_Live = 30610803 ∧
    w4RecvPrekeyReal1MiB_i_Peak = 32716150 ∧
    w4RecvPrekeyReal1MiB_i_MaxReq = 2457152 ∧
    w4RecvPrekeyReal1MiB_i_Live ≤ w4RecvPrekeyReal1MiB_i_Peak :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Variant (ii) closed constants at `(4096, sessionCapBytes, msgCapBytes)`:
`cum = 284,695,267`, `live = 15,873,374`, `peak = 17,978,721`, `maxReq = 2,457,152`. -/
@[expose] def w4RecvPrekeyReal1MiB_ii_Cum : Nat := w4RecvPrekeySplitDirCum 4096 sessionCapBytes
@[expose] def w4RecvPrekeyReal1MiB_ii_Live : Nat := w4RecvPrekeySplitDirLive 4096 sessionCapBytes msgCapBytes
@[expose] def w4RecvPrekeyReal1MiB_ii_Peak : Nat := w4RecvPrekeySplitDirPeak 4096 sessionCapBytes msgCapBytes
@[expose] def w4RecvPrekeyReal1MiB_ii_MaxReq : Nat := w4RecvPrekeySplitDirMaxReq 4096 sessionCapBytes msgCapBytes

theorem w4RecvPrekeyReal1MiB_ii_eq :
    w4RecvPrekeyReal1MiB_ii_Cum = 284695267 ∧
    w4RecvPrekeyReal1MiB_ii_Live = 15873374 ∧
    w4RecvPrekeyReal1MiB_ii_Peak = 17978721 ∧
    w4RecvPrekeyReal1MiB_ii_MaxReq = 2457152 ∧
    w4RecvPrekeyReal1MiB_ii_Live ≤ w4RecvPrekeyReal1MiB_ii_Peak :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## Inner Credit, Drop-Cancellation, & Group Helpers -/

private theorem dhSmall_of_le_5 {dhCap : Nat} (h : dhCap ≤ 5) :
    104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  rw [fineCostModel_smallMaxReq_eq]
  match dhCap, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide

private theorem w2Seeds738Cum_le_5 {dhCap : Nat} (needGrow : Bool) (h : dhCap ≤ 5) :
    w2TryDecryptSeeds738Cum dhCap needGrow 12 23313687 ≤ w4RealFailTdCum := by
  unfold w4RealFailTdCum
  match dhCap, needGrow, h with
  | 0, false, _ | 0, true, _ | 1, false, _ | 1, true, _
  | 2, false, _ | 2, true, _ | 3, false, _ | 3, true, _
  | 4, false, _ | 4, true, _ | 5, false, _ | 5, true, _ => decide

private theorem w2GenSeeds12Cum_le_5 {dhCap : Nat} (needGrow : Bool) (h : dhCap ≤ 5) :
    w2TryDecryptGenSeeds738Cum 12 dhCap needGrow 12 3897904 ≤ w4RealTdACCum := by
  unfold w4RealTdACCum
  match dhCap, needGrow, h with
  | 0, false, _ | 0, true, _ | 1, false, _ | 1, true, _
  | 2, false, _ | 2, true, _ | 3, false, _ | 3, true, _
  | 4, false, _ | 4, true, _ | 5, false, _ | 5, true, _ => decide

private theorem w2MaxReqOf_le_5 {dhCap maxCt : Nat} (h : dhCap ≤ 5) :
    w2TryDecryptMaxReq dhCap 2000 302480 maxCt ≤ w4TdMaxReqOf maxCt := by
  unfold w4TdMaxReqOf w2TryDecryptMaxReq
  have h104 : max 416 (104 * (2 * dhCap)) ≤ max 416 (104 * (2 * 5)) := by
    match dhCap, h with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _,
     Nat.le_trans
       (Nat.max_le.mpr
         ⟨Nat.le_trans h104 (Nat.le_max_left _ _),
          Nat.le_max_right _ _⟩)
       (Nat.le_max_right _ _)⟩

private theorem deallocCreditSpec_mono_le {M : AllocCostModel} [HasFineReallocCredit M]
    {E : List AllocEvent → Prop} {d₁ d₂ : Nat}
    (h : DeallocCreditSpec M E d₂) (hd : d₁ ≤ d₂) :
    DeallocCreditSpec M E d₁ where
  req_align := h.req_align
  credit_sub st0 {_} hE := by
    obtain ⟨hc, hl, hp⟩ := h.credit_sub st0 hE
    exact ⟨hc, Nat.le_trans hl (Nat.sub_le_sub_left hd _), hp⟩

private theorem pinFreeEvents_freeOnlyAlign16 (pin : VecPin) :
    FreeOnlyAlign16Evs (pinFreeEvents pin) := by
  unfold pinFreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) pin.cap.toNat

private theorem sgnCapFreeEvents_freeOnlyAlign16 (cap : BitVec 64) :
    FreeOnlyAlign16Evs (sgnCapFreeEvents cap) := by
  unfold sgnCapFreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) cap.toNat

private theorem vec104FreeEvents_freeOnlyAlign16 (cap : BitVec 64) :
    FreeOnlyAlign16Evs (vec104FreeEvents cap) := by
  unfold vec104FreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) (cap.toNat * 104)

private theorem mkFreeEvents_freeOnlyAlign16 (mk : MessageKeyGhost) :
    FreeOnlyAlign16Evs (mkFreeEvents mk) := by
  unfold mkFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (pinFreeEvents_freeOnlyAlign16 mk.cipher)
        (pinFreeEvents_freeOnlyAlign16 mk.mac))
      (pinFreeEvents_freeOnlyAlign16 mk.iv))
    (pinFreeEvents_freeOnlyAlign16 mk.seed)

private theorem mkListFreeEvents_freeOnlyAlign16
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (mks.flatMap fun gk => mkFreeEvents gk.1) := by
  induction mks with
  | nil => simp only [List.flatMap_nil]; exact FreeOnlyAlign16Evs.nil
  | cons gk tl ih =>
    simp only [List.flatMap_cons]; intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact mkFreeEvents_freeOnlyAlign16 gk.1 ev h1
    · exact ih ev h2

private theorem dropVecMessageKeyEvents_freeOnlyAlign16 (cap : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (dropVecMessageKeyEvents cap mks) := by
  intro ev hev; dsimp only [dropVecMessageKeyEvents] at hev
  rcases List.mem_append.mp hev with h1 | h2
  · exact mkListFreeEvents_freeOnlyAlign16 mks ev h1
  · exact vec104FreeEvents_freeOnlyAlign16 cap ev h2

private theorem chainPairFreeEvents_freeOnlyAlign16 (gc : ChainGhost × ReceiverChain) :
    FreeOnlyAlign16Evs (chainPairFreeEvents gc) := by
  unfold chainPairFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (pinFreeEvents_freeOnlyAlign16 ⟨gc.1.srk.cap, gc.1.srk.ptr⟩)
        (pinFreeEvents_freeOnlyAlign16 ⟨gc.1.priv.cap, gc.1.priv.ptr⟩))
      (sgnCapFreeEvents_freeOnlyAlign16 (optCkCapVal gc.1.ck gc.2.chainKey)))
    (dropVecMessageKeyEvents_freeOnlyAlign16 gc.1.mkCap (gc.1.keys.zip gc.2.messageKeys))

private theorem chainListFreeEvents_freeOnlyAlign16
    (cs : List (ChainGhost × ReceiverChain)) :
    FreeOnlyAlign16Evs (cs.flatMap chainPairFreeEvents) := by
  induction cs with
  | nil => simp only [List.flatMap_nil]; exact FreeOnlyAlign16Evs.nil
  | cons gc tl ih =>
    simp only [List.flatMap_cons]; intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact chainPairFreeEvents_freeOnlyAlign16 gc ev h1
    · exact ih ev h2

private theorem dropSessionStructureLocal1Events_freeOnlyAlign16
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    FreeOnlyAlign16Evs (dropSessionStructureLocal1Events G st) := by
  unfold dropSessionStructureLocal1Events ssFirst3FreeEvents ssTail3FreeEvents dropVecChainEvents
  have h1 := FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (pinFreeEvents_freeOnlyAlign16 ⟨G.localIk.cap, G.localIk.ptr⟩)
      (pinFreeEvents_freeOnlyAlign16 ⟨G.remoteIk.cap, G.remoteIk.ptr⟩))
    (pinFreeEvents_freeOnlyAlign16 G.root)
  have h2 : FreeOnlyAlign16Evs (senderFreeEvents G.sender) := by
    cases G.sender with
    | none => exact FreeOnlyAlign16Evs.nil
    | some sg =>
      unfold senderFreeEvents
      exact FreeOnlyAlign16Evs.append
        (FreeOnlyAlign16Evs.append
          (FreeOnlyAlign16Evs.append
            (pinFreeEvents_freeOnlyAlign16 ⟨sg.srk.cap, sg.srk.ptr⟩)
            (pinFreeEvents_freeOnlyAlign16 ⟨sg.priv.cap, sg.priv.ptr⟩))
          (sgnCapFreeEvents_freeOnlyAlign16 sg.ck.cap))
        (dropVecMessageKeyEvents_freeOnlyAlign16 sg.mkCap [])
  have h3 : FreeOnlyAlign16Evs
      (((G.chains.zip st.receiverChains).flatMap chainPairFreeEvents) ++
        vec104FreeEvents G.chainsCap) := by
    intro ev hev
    rcases List.mem_append.mp hev with h3a | h3b
    · exact chainListFreeEvents_freeOnlyAlign16 (G.chains.zip st.receiverChains) ev h3a
    · exact vec104FreeEvents_freeOnlyAlign16 G.chainsCap ev h3b
  have h4 := FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (sgnCapFreeEvents_freeOnlyAlign16 (optTailCapVal G.pending))
      (sgnCapFreeEvents_freeOnlyAlign16 (optTailCapVal G.kyber)))
    (pinFreeEvents_freeOnlyAlign16 ⟨G.alice.cap, G.alice.ptr⟩)
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append (FreeOnlyAlign16Evs.append h1 h2) h3) h4)
    (pinFreeEvents_freeOnlyAlign16 G.pq)

private theorem deallocCreditSpec_dropSessionStructureLocal1
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hok : SessionDropCapsOk G st) :
    DeallocCreditSpec fineCostModel
      (· = dropSessionStructureLocal1Events G st)
      (ssStateLargeLive fineCostModel G st) where
  req_align := by
    rintro _ rfl ev hev
    exact (PhaseCreditSpec.freeOnly_align16 fineCostModel).req_align _
      (dropSessionStructureLocal1Events_freeOnlyAlign16 G st) ev hev
  credit_sub := by
    rintro st0 _ rfl
    exact stepEvents_dropSessionStructureLocal1_bounds fineCostModel hok st0

private theorem optDeallocListEvs_freeOnly (pairs : List (Nat × Nat)) :
    FreeOnlyEvs (optDeallocListEvs pairs) := by
  induction pairs with
  | nil => exact fun _ h => nomatch h
  | cons p rest ih =>
    rcases p with ⟨req, al⟩
    intro ev hev
    simp only [optDeallocListEvs, List.mem_append] at hev
    rcases hev with he | he
    · split at he
      · nomatch he
      · unfold rustDeallocEvents at he; rw [List.mem_singleton] at he; exact ⟨al, req, he⟩
    · exact ih ev he

private theorem w4TryDecryptPathBOf_phaseCredit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptCallDomOf F K maxCt td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathBEnv F K td)
      w4RealFailTdCum (w4TdBLiveOf maxCt) (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hBase := w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    td.stBytes td.w.pre_pb td.w.vn td.w.pb td.w.st0 td.w.sckaMsg td.w.v
    td.w.xInit td.w.xNew td.w.xAdd td.w.xRk td.w.xSInto td.w.xCInto
    (dhSmall_of_le_5 hDom.dh_le) hDom.caps_len hDom.chain_le hDom.top_tight hDom.ct_le
  exact hBase.mono
    (w2Seeds738Cum_le_5 td.needGrow hDom.dh_le)
    (Nat.le_refl _) (Nat.le_refl _) (w2MaxReqOf_le_5 hDom.dh_le)

private theorem w4TryDecryptPathACOf_phaseCredit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptPathACDomOf F K maxCt td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathACEnv F K td)
      w4RealTdACCum (w4TdACLiveOf maxCt) (w4TdACPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hBase := w2TryDecrypt_genSeeds_fine_phaseCreditSpec (maxSeeds := 12)
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    (dhSmall_of_le_5 hDom.base.dh_le) hDom.base.caps_len hDom.base.chain_le
    (spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec F K td.stBytes td.w
      hDom.base.top_tight hDom.zero_skip)
    hDom.base.ct_le
  exact hBase.mono
    (w2GenSeeds12Cum_le_5 td.needGrow hDom.base.dh_le)
    (Nat.le_refl _) (Nat.le_refl _) (w2MaxReqOf_le_5 hDom.base.dh_le)

private theorem w4FailedTdCancelOf_phaseCredit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDomOf F K maxCt fc) :
    PhaseCreditSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w4RealFailTdCum 0 (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hTd0 : PhaseCreditSpec fineCostModel (W4TryDecryptFailLinkedEnv F K fc.td) _ _ _ _ :=
    w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
      (needGrow := fc.td.needGrow) (withAddr := fc.td.withAddr) (errAlloc := fc.td.errAlloc)
      fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
      fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
      (dhSmall_of_le_5 hDom.td_dom.dh_le) hDom.td_dom.caps_len hDom.td_dom.chain_le
      hDom.td_dom.top_tight hDom.td_dom.ct_le
  have hTd := hTd0.mono
    (w2Seeds738Cum_le_5 fc.td.needGrow hDom.td_dom.dh_le)
    (Nat.le_of_eq (Nat.zero_add _).symm)
    (Nat.le_refl _) (w2MaxReqOf_le_5 hDom.td_dom.dh_le)
  have hDrop := deallocCreditSpec_mono_le
    (LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak.DeallocCreditSpec.optDeallocList
      fineCostModel fc.failDropPairs hDom.align_le)
    hDom.cancel_live
  have hCancel := hTd.concat_dealloc_cancel hDrop
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCancel).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem w4TrialDecOf_phaseCredit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {x : W4ArchivedTrial F}
    (hDom : W4ArchivedTrialDomOf F K maxCt x) :
    PhaseCreditSpec fineCostModel (W4TrialDecEnv F x)
      deserCancelFineCum (sessDeserLargeLive fineCostModel x.r_dec)
      deserCancelFinePeak deserCancelFineMaxReq := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hmaxR : max 212992 (encodeRecord x.r_dec).length ≤ deserCancelFineMaxReq :=
    Nat.max_le.mpr ⟨by decide, hDom.enc_le⟩
  have hSym := sessDeserializeCancelEnv_phaseCreditSpec fineCostModel h33 hmaxR
  have hCl := sessDeserializeCancelEnv_fine_phaseCreditSpec hDom.enc_le
  exact
    { req_align := hCl.req_align
      credit_le := fun st0 {_} hE => by
        obtain ⟨hc, _, hp⟩ := hCl.credit_le st0 hE
        obtain ⟨_, hl, _⟩ := hSym.credit_le st0 hE
        exact ⟨hc, hl, hp⟩ }

private theorem w4TrialRunOf_phaseCredit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {x : W4ArchivedTrial F}
    (hDom : W4ArchivedTrialDomOf F K maxCt x) :
    PhaseCreditSpec fineCostModel (W4TrialRunEnv F K x)
      w4RealTrialCum 0 (w4TrialPeakOf maxCt) (w4TrialMaxReqOf maxCt) := by
  have hCloneFail := tryDecryptCloneFail_dom_fine_cancel_phaseCredit
    (curPqCap := 286196)
    (Or.inr ⟨x.ses_tr, rfl, hDom.tr_gv, hDom.tr_dom⟩)
    (w4FailedTdCancelOf_phaseCredit hDom.tr_fail)
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCloneFail).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-! ## Parametric `PhaseGroupSpec` (`w4RecvPrekeyRealOf_fine_groupSpec`) -/

private theorem segCloneEnv_freshBob_fine_groupSpec
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G ses.state) segCloneFreshBobFineGrpS := by
  have hgv := ghostCloneValid_of_sessionGhostValid hbob.gv
  have hloc := vecCloneEvents_groupSpec fineCostModel G.localIk
  have hrem := vecCloneEvents_groupSpec fineCostModel G.remoteIk
  have hroot := PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
  have hsnd : PhaseGroupSpec fineCostModel
      (· = match G.sender, ses.state.senderChain with
           | some gs, some sc =>
             LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget.senderChainCloneEvents gs sc
           | _, _ => [])
      senderChainCloneDomFineGrpS := by
    rcases hgv.sender_ok with ⟨hn1, hn2⟩ | ⟨gs, sc, hgs, hsc, _hsrk, _hpriv⟩
    · rw [hn1, hn2]; exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rw [hgs, hsc]; exact senderChainCloneEnv_dom_fine_groupSpec sc (by omega) (by omega)
  have hrc : PhaseGroupSpec fineCostModel
      (· = if ses.state.receiverChains = [] then []
           else rustAllocEvents (104 * ses.state.receiverChains.length) 8 ++
             (G.chains.zip ses.state.receiverChains).flatMap
               LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget.chainCloneEvents)
      0 := by
    rw [hbob.rc_nil]; simp only [↓reduceIte]; exact PhaseGroupSpec.nil fineCostModel
  have hpend := optTailCloneEvents_groupSpec fineCostModel G.pending
  have hkyb := optTailCloneEvents_groupSpec fineCostModel G.kyber
  have halice := vecCloneEvents_groupSpec fineCostModel G.alice
  have hpq : PhaseGroupSpec fineCostModel
      (· = if ses.state.pqRatchetState.length = 0 then []
           else rustAllocEvents ses.state.pqRatchetState.length 1)
      (3 * FineScale) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel ses.state.pqRatchetState.length 1
  have s1 := phaseGroupSpec_append_eq fineCostModel hloc hrem
  have s2 := phaseGroupSpec_append_eq fineCostModel s1 hroot
  have s3 := phaseGroupSpec_append_eq fineCostModel s2 hsnd
  have s4 := phaseGroupSpec_append_eq fineCostModel s3 hrc
  have s5 := phaseGroupSpec_append_eq fineCostModel s4 hpend
  have s6 := phaseGroupSpec_append_eq fineCostModel s5 hkyb
  have s7 := phaseGroupSpec_append_eq fineCostModel s6 halice
  have s8 := phaseGroupSpec_append_eq fineCostModel s7 hpq
  unfold SegCloneEnv segCloneEvents segCloneFreshBobFineGrpS
  exact s8.mono (by decide)

private theorem serializePrev1CancelEnv_freshBob_fine_groupSpec
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    PhaseGroupSpec fineCostModel (SerializePrev1CancelEnv G ses enc)
      serializePrev1FreshBobFineGrpS := by
  unfold SerializePrev1CancelEnv serializePrev1FreshBobFineGrpS
  have hcl := segCloneEnv_freshBob_fine_groupSpec hbob
  have hvv := vecVecClone1Events_fine_groupSpec enc
  have hout := PhaseGroupSpec.rustAlloc_any fineCostModel (encodeRecordPrev1Mem G ses enc).length 1
  have hd1 := dropClonedSessionEvents_groupSpec fineCostModel G ses.state
  have hd2 := dropVecVecClone1Events_groupSpec fineCostModel enc
  exact (((hcl.concat hvv).concat hout).concat (hd1.concat hd2)).mono (by decide)

private theorem recordSerializeCancelEnv_of_valid_fine_groupSpec {pqCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g r) recordSerializeDomFineGrpS := by
  unfold RecordSerializeCancelEnv recordSerializeDomFineGrpS
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · rename_i G ses
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    exact serializeSomeCancelEnv_groupSpec fineCostModel (segCloneEnv_dom_fine_groupSpec hgv hdom)

private theorem w4FailedTdCancelOf_fine_groupSpec {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDomOf F K maxCt fc) :
    PhaseGroupSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w2TryDecryptFailTightGroupS_split_12 := by
  have hFail := w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12 F K
    fc.td.dhCap fc.td.needGrow fc.td.withAddr fc.td.errAlloc fc.td.ctLen
    fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
    fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
    hDom.td_dom.caps_len hDom.td_dom.top_tight
  have hDrop : PhaseGroupSpec fineCostModel (· = optDeallocListEvs fc.failDropPairs) 0 :=
    (PhaseGroupSpec.freeOnly fineCostModel).of_imp fun _ h => by
      subst h; exact optDeallocListEvs_freeOnly fc.failDropPairs
  have hCat := (hFail.concat hDrop).mono (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hCat).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem p2c_grp_reassoc (gCl gCur gErr gLoop s16 gSer gPush gBob : Nat) :
    (gCl + gCur + gErr) +
      (gLoop + (s16 + (s16 + (s16 + (s16 + ((gSer + gPush + gBob) + (s16 + gErr))))))) ≤
      (gCl + gErr + 5 * s16 + gSer + gBob + gErr) + gCur + gLoop + gPush := by
  omega

private theorem four_stages_grp_reassoc (a b c d : Nat) :
    a + (b + (c + d)) ≤ a + b + c + d := by
  omega

private theorem w4StageP2PathCCli_curDom_fine_groupSpec {α : Type} {pqCap : Nat}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop}
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkDir kpkDir opkDir ownDir : DirGhost)
    (spkId kpkId opkId : BitVec 32)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {g_cur g_dec g_tr g_archSer g_push : Nat}
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = st_cur ∧ SessionGhostValid G_cur ses_cur ∧
          SessionCloneDom pqCap ses_cur)
    (hCur : PhaseGroupSpec fineCostModel CurTrialFailEnv g_cur)
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DropEnv x) 0)
    (hArchSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_arch r_arch) g_archSer)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2PathCCliEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      ((segCloneDomFineGrpS + w4ErrTailFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
          g_archSer + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS) +
        g_cur + 4 * (g_dec + g_tr) + g_push) := by
  have hE1 : PhaseGroupSpec fineCostModel
      (fun e1 => FreeOnlyEvs e1 ∨
        W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
          (· = dropClonedSessionEvents G_cur st_cur) e1)
      (segCloneDomFineGrpS + g_cur + w4ErrTailFineGrpS) := by
    rcases hCurDom with hNo | ⟨ses_cur, hst_eq, hgv, hdom⟩
    · have hEmpty : PhaseGroupSpec fineCostModel
          (W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
            (· = dropClonedSessionEvents G_cur st_cur)) 0 :=
        { groups_le := fun _ {_} hE => by
            rcases hE with h1 | ⟨_, _, _, h1, _⟩
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1; exact False.elim (hNo e2 htf)
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1; exact False.elim (hNo e2 htf) }
      exact ((PhaseGroupSpec.freeOnly fineCostModel).or hEmpty).mono (Nat.zero_le _)
    · subst hst_eq
      exact ((PhaseGroupSpec.freeOnly fineCostModel).or
        (w4TryDecryptCloneFail_fine_groupSpec
          (segCloneEnv_dom_fine_groupSpec hgv hdom) hCur
          (dropClonedSessionEvents_groupSpec fineCostModel G_cur ses_cur.state))).mono
        (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  have hE2 := ((PhaseGroupSpec.freeOnly fineCostModel).or
    (archivedTrialLoop_le4_groupSpec fineCostModel hlen4 hDec hTr hDrop)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  have hSpk := w4SmallStoreStep16_fine_groupSpec rd files spkDir (keyName spkId)
  have hKpk := w4SmallStoreStep16_fine_groupSpec rd files kpkDir (keyName kpkId)
  have hOptPk := phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId)
  have hKp := w4SmallStoreStep16_fine_groupSpec rd files ownDir ownKeyName
  have hOver := w4StageP2OverBob_fine_groupSpec x_res hasOpk F x_spqr hArchSer hPush
  have hReg := w4SmallStoreStep16_fine_groupSpec rd files ownDir ownRegName
  have hErr := w4ErrTail_fine_groupSpec
  exact (hE1.seq (hE2.seq (hSpk.seq (hKpk.seq (hOptPk.seq
    (hKp.seq (hOver.seq (hReg.seq hErr)))))))).mono
    (p2c_grp_reassoc segCloneDomFineGrpS g_cur w4ErrTailFineGrpS (4 * (g_dec + g_tr))
      w4SmallStoreStep16FineGrpS g_archSer g_push w4InitBobSpqrFineGrpS)

/-- Parametric `PhaseGroupSpec` for `W4RecvPrekeyRealEnv R` under `W4RecvPrekeyRealDomOf`. -/
theorem w4RecvPrekeyRealOf_fine_groupSpec {smallFileCap maxCt : Nat}
    (R : W4RecvPrekeyRealParams) (hDom : W4RecvPrekeyRealDomOf smallFileCap maxCt R) :
    PhaseGroupSpec fineCostModel (W4RecvPrekeyRealEnv R) w4RecvPrekeyRealGrpS := by
  let P := mkW4RecvPrekeySlotParams R
  let TryDecAC := W4RecvPrekeyTryDecACEnv R
  have hDeser : ∀ bs : List (BitVec 8), bs.length ≤ 2097152 →
      PhaseGroupSpec fineCostModel (P.DeserEnv bs) deserCancelFineGrpS :=
    fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs
  have hCur : PhaseGroupSpec fineCostModel P.CurTrialFailEnv w2TryDecryptFailTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.hasCurSession then W4FailedTdCancelEnv R.F R.K R.fc_cur else fun _ => False) _
    cases hcs : R.hasCurSession
    · exact { groups_le := fun _ {_} h => False.elim h }
    · exact w4FailedTdCancelOf_fine_groupSpec (hDom.cur_fail_dom hcs)
  have hDec : ∀ x ∈ P.archivedTrials,
      PhaseGroupSpec fineCostModel (P.DecEnv x) deserCancelFineGrpS :=
    fun x _ => sessDeserializeCancelEnv_fine_groupSpec x.r_dec
  have hTr : ∀ x ∈ P.archivedTrials,
      PhaseGroupSpec fineCostModel (P.TrialEnv x) w4RealTrialFineGrpS := by
    intro x hx
    have hxd := hDom.trials_dom x hx
    have hcf := w4TryDecryptCloneFail_fine_groupSpec
      (segCloneEnv_dom_fine_groupSpec hxd.tr_gv hxd.tr_dom)
      (w4FailedTdCancelOf_fine_groupSpec hxd.tr_fail)
      (dropClonedSessionEvents_groupSpec fineCostModel x.G_tr x.ses_tr.state)
    exact ((PhaseGroupSpec.freeOnly fineCostModel).or hcf).mono
      (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  have hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0 := by
    intro x _
    exact (PhaseGroupSpec.freeOnly fineCostModel).of_imp fun _ h => by
      subst h
      exact FreeOnlyAlign16Evs.toFreeOnlyEvs
        (dropSessionStructureLocal1Events_freeOnlyAlign16 x.G_dec x.st_dec)
  have hPush : PhaseGroupSpec fineCostModel P.VecPushEnv (3 * FineScale) := by
    change PhaseGroupSpec fineCostModel (W4BoundedEvs 1 192) (3 * FineScale)
    simpa [Nat.one_mul] using w4BoundedEvs_groupSpec fineCostModel 1 192
  have hArchSer := recordSerializeCancelEnv_of_valid_fine_groupSpec hDom.outer_dom.arch_valid
  have hOut0Ser := recordSerializeCancelEnv_of_valid_fine_groupSpec hDom.outer_dom.out0_valid
  have hOut1Ser := serializePrev1CancelEnv_freshBob_fine_groupSpec hDom.outer_dom.out1_freshBob
  have hTdB : PhaseGroupSpec fineCostModel P.TryDecEnv w2TryDecryptTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.isPathB then W4TryDecryptPathBEnv R.F R.K R.td_B else fun _ => False) _
    cases hpb : R.isPathB
    · exact { groups_le := fun _ {_} h => False.elim h }
    · have hd := hDom.tdB_dom hpb
      exact w2TryDecryptTightEnv_linked_fine_groupSpec_split_12 R.F R.K
        R.td_B.dhCap R.td_B.needGrow R.td_B.withAddr R.td_B.errAlloc R.td_B.ctLen
        R.td_B.stBytes R.td_B.w.pre_pb R.td_B.w.vn R.td_B.w.pb R.td_B.w.st0
        R.td_B.w.sckaMsg R.td_B.w.v R.td_B.w.xInit R.td_B.w.xNew R.td_B.w.xAdd
        R.td_B.w.xRk R.td_B.w.xSInto R.td_B.w.xCInto hd.caps_len hd.top_tight
  have hTdAC : PhaseGroupSpec fineCostModel TryDecAC w2TryDecryptSeeds12GroupS_split_12 := by
    unfold TryDecAC W4RecvPrekeyTryDecACEnv
    cases hpac : R.isPathAC
    · exact { groups_le := fun _ {_} h => False.elim h }
    · have hd := (hDom.tdAC_dom hpac).base
      exact w2TryDecryptSeedsEnv_12_linked_fine_groupSpec_split_12 R.F R.K
        R.td_AC.dhCap R.td_AC.needGrow R.td_AC.withAddr R.td_AC.errAlloc R.td_AC.ctLen
        R.td_AC.stBytes R.td_AC.w.pre_pb R.td_AC.w.vn R.td_AC.w.pb R.td_AC.w.st0
        R.td_AC.w.sckaMsg R.td_AC.w.v R.td_AC.w.xInit R.td_AC.w.xNew R.td_AC.w.xAdd
        R.td_AC.w.xRk R.td_AC.w.xSInto R.td_AC.w.xCInto hd.caps_len hd.top_tight
  have hP1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  let gU := w4StageP1UntrustedBaseFineGrpS + deserCancelFineGrpS
  let gB := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    (4 * (deserCancelFineGrpS + w4RealTrialFineGrpS) + recordSerializeDomFineGrpS + 3 * FineScale) +
    w4StageP3FineGrpS w2TryDecryptTightGroupS_split_12 +
    (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + recordSerializeDomFineGrpS)))
  let gA := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    w4StageP2PathACliFineGrpS +
    w4StageP3FineGrpS w2TryDecryptSeeds12GroupS_split_12 +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + recordSerializeDomFineGrpS)))
  let gC := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    ((segCloneDomFineGrpS + w4ErrTailFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
        recordSerializeDomFineGrpS + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS) +
      w2TryDecryptFailTightGroupS_split_12 +
      4 * (deserCancelFineGrpS + w4RealTrialFineGrpS) + 3 * FineScale) +
    w4StageP3FineGrpS w2TryDecryptSeeds12GroupS_split_12 +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + serializePrev1FreshBobFineGrpS)))
  have hLeU : gU ≤ w4RecvPrekeyRealGrpS :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hLeB : gB ≤ w4RecvPrekeyRealGrpS :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hLeA : gA ≤ w4RecvPrekeyRealGrpS :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hLeC : gC ≤ w4RecvPrekeyRealGrpS :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hArms : PhaseGroupSpec fineCostModel
      (fun e =>
        W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
        W4DecryptPrekeyPathBEnv P e ∨
        W4DecryptPrekeyPathAEnv ({ P with TryDecEnv := TryDecAC }) e ∨
        W4DecryptPrekeyPathCEnv ({ P with TryDecEnv := TryDecAC }) e)
      w4RecvPrekeyRealGrpS :=
    { groups_le := fun st0 {e} hArm => by
        rcases hArm with hU | hB | hA | hC
        · exact ((w4StageP1UntrustedCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer
            hDeser).mono hLeU).groups_le st0 hU
        · have hp2 := w4StageP2Matched_groupSpec fineCostModel hDom.outer_dom.trials_len4
            hDec hTr hDrop hArchSer hPush
          have hp3 := w4StageP3_fine_groupSpec hTdB
          have hp4 := w4StageP4MatchedCli_fine_groupSpec P.rd P.files P.peersDir P.sessDir P.peer
            hOut0Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (four_stages_grp_reassoc _ _ _ _)).mono hLeB).groups_le st0 hB
        · have hp2 := w4StageP2PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
          have hp3 := w4StageP3_fine_groupSpec hTdAC
          have hp4 := w4StageP4PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut0Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (four_stages_grp_reassoc _ _ _ _)).mono hLeA).groups_le st0 hA
        · have hp2 := w4StageP2PathCCli_curDom_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
            hDom.outer_dom.cur_dom hCur hDom.outer_dom.trials_len4
            hDec hTr hDrop hArchSer hPush
          have hp3 := w4StageP3_fine_groupSpec hTdAC
          have hp4 := w4StageP4PathCCli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut1Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (four_stages_grp_reassoc _ _ _ _)).mono hLeC).groups_le st0 hC }
  have hSeq := (hArms.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-! ## Variant (i): Parametric & `(sessionCapBytes, msgCapBytes)` `SingleSlotFineSpec` -/

/-- Parametric `PhaseCreditSpec fineCostModel` for `W4RecvPrekeyRealEnv R` under
`W4RecvPrekeyRealDomOf smallFileCap maxCt R`. -/
theorem w4RecvPrekeyRealOf_phaseCreditSpec {smallFileCap maxCt : Nat}
    (R : W4RecvPrekeyRealParams) (hDom : W4RecvPrekeyRealDomOf smallFileCap maxCt R) :
    PhaseCreditSpec fineCostModel (W4RecvPrekeyRealEnv R)
      (w4RecvPrekeyRealCumOf smallFileCap)
      (w4RecvPrekeyRealLiveOf smallFileCap maxCt)
      (w4RecvPrekeyRealPeakOf smallFileCap maxCt)
      (w4RecvPrekeyRealMaxReqOf smallFileCap maxCt) := by
  let P := mkW4RecvPrekeySlotParams R
  have hCur : PhaseCreditSpec fineCostModel P.CurTrialFailEnv
      w4RealFailTdCum 0 (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
    change PhaseCreditSpec fineCostModel
      (if R.hasCurSession then W4FailedTdCancelEnv R.F R.K R.fc_cur else fun _ => False) _ _ _ _
    cases hcs : R.hasCurSession
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact w4FailedTdCancelOf_phaseCredit (hDom.cur_fail_dom hcs)
  have hPush : PhaseCreditSpec fineCostModel P.VecPushEnv 9923 0 0 192 := by
    have hsm : 192 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; decide
    have hc9923 : 1 * (2 * 192 + 9539) ≤ 9923 := by decide
    exact PhaseCreditSpec.mono hc9923 (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
      (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 192 hsm)
  have hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv
      w4RealFailTdCum (w4TdBLiveOf maxCt) (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
    change PhaseCreditSpec fineCostModel
      (if R.isPathB then W4TryDecryptPathBEnv R.F R.K R.td_B else fun _ => False) _ _ _ _
    cases hpb : R.isPathB
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact w4TryDecryptPathBOf_phaseCredit (hDom.tdB_dom hpb)
  have hTdAC : PhaseCreditSpec fineCostModel (W4RecvPrekeyTryDecACEnv R)
      w4RealTdACCum (w4TdACLiveOf maxCt) (w4TdACPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
    unfold W4RecvPrekeyTryDecACEnv
    cases hpac : R.isPathAC
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact w4TryDecryptPathACOf_phaseCredit (hDom.tdAC_dom hpac)
  exact w4DecryptPrekeySplitSlot_opened_fine_phaseCredit P
    (l_dec := fun x => sessDeserLargeLive fineCostModel x.r_dec)
    rfl rfl rfl hDom.kpk_dir rfl rfl hDom.outer_dom
    (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
    hCur
    (fun x hx => (hDom.trials_dom x hx).live_le_peak)
    (fun x hx => w4TrialDecOf_phaseCredit (hDom.trials_dom x hx))
    (fun x hx => w4TrialRunOf_phaseCredit (hDom.trials_dom x hx))
    (fun x hx => deallocCreditSpec_mono_le
      (deallocCreditSpec_dropSessionStructureLocal1 (hDom.trials_dom x hx).drop_caps)
      (hDom.trials_dom x hx).live_le_drop)
    hPush hTdB hTdAC

/-- Variant (i) closed `SingleSlotFineSpec` (`W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes`):
`(288,625,123, 30,610,803, 32,716,150, 2,457,152, 5,867,151,338)`. -/
@[expose] def w4RecvPrekeyReal1MiB_i_singleSlotFineSpec
    (R : W4RecvPrekeyRealParams)
    (hDom : W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes R) :
    SingleSlotFineSpec (W4RecvPrekeyRealEnv R) where
  cum := w4RecvPrekeyReal1MiB_i_Cum
  live := w4RecvPrekeyReal1MiB_i_Live
  peak := w4RecvPrekeyReal1MiB_i_Peak
  maxReq := w4RecvPrekeyReal1MiB_i_MaxReq
  grpS := w4RecvPrekeyRealGrpS
  credit := w4RecvPrekeyRealOf_phaseCreditSpec R hDom
  live_le_peak := w4RecvPrekeyReal1MiB_i_eq.2.2.2.2
  groups := w4RecvPrekeyRealOf_fine_groupSpec R hDom

/-! ## Variant (ii): Per-Directory Split `(4096, sessionCapBytes, msgCapBytes)` `SingleSlotFineSpec` -/

private theorem max_mono {a a' b b' : Nat} (ha : a ≤ a') (hb : b ≤ b') :
    max a b ≤ max a' b' :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem seqPeak_mono {p1 p1' l1 l1' q q' : Nat}
    (hp : p1 ≤ p1') (hl : l1 ≤ l1') (hq : q ≤ q') :
    max p1 (l1 + q) ≤ max p1' (l1' + q') :=
  max_mono hp (Nat.add_le_add hl hq)

private theorem fourStagePeak_mono
    {p1 p1' l1 l1' p2 p2' l2 l2' p3 p3' l3 l3' p4 p4' : Nat}
    (hp1 : p1 ≤ p1') (hl1 : l1 ≤ l1')
    (hp2 : p2 ≤ p2') (hl2 : l2 ≤ l2')
    (hp3 : p3 ≤ p3') (hl3 : l3 ≤ l3')
    (hp4 : p4 ≤ p4') :
    max p1 (l1 + max p2 (l2 + max p3 (l3 + p4))) ≤
      max p1' (l1' + max p2' (l2' + max p3' (l3' + p4'))) :=
  seqPeak_mono hp1 hl1 (seqPeak_mono hp2 hl2 (seqPeak_mono hp3 hl3 hp4))

private theorem p2a_bob_maxReq_le (ikmCap : Nat) :
    max (max ikmCap 1569) (max 4224 68) ≤ max ikmCap 4224 :=
  Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨Nat.le_max_left _ _,
       Nat.le_trans (by decide : 1569 ≤ 4224) (Nat.le_max_right _ _)⟩,
     Nat.max_le.mpr ⟨Nat.le_max_right _ _,
       Nat.le_trans (by decide : 68 ≤ 4224) (Nat.le_max_right _ _)⟩⟩

private theorem p2a_split_cum_le (cs ck b1 b2 c : Nat) :
    cs + (ck + (cs + (cs + ((b1 + b2) + (cs + c))))) ≤ (4 * cs + ck) + b1 + b2 + c := by
  omega

private theorem p2a_split_live_le (ls lk : Nat) :
    ls + (lk + (ls + (ls + (0 + ls)))) ≤ 4 * ls + lk := by
  omega

private theorem p2a_split_maxReq_le (rs rk ikmCap : Nat) :
    max rs (max rk (max rs (max rs (max (max ikmCap 4224) (max rs 192))))) ≤
      max (max rs rk) (max ikmCap 4224) := by
  let T := max (max rs rk) (max ikmCap 4224)
  have hrs : rs ≤ T := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hrk : rk ≤ T := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hb : max ikmCap 4224 ≤ T := Nat.le_max_right _ _
  have h192 : 192 ≤ T :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hb)
  exact Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨hrk, Nat.max_le.mpr ⟨hrs,
    Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨hb, Nat.max_le.mpr ⟨hrs, h192⟩⟩⟩⟩⟩⟩

private theorem p2c_split_cum_le (cCur cLoop cs ck cOver cTail : Nat) :
    cCur + (cLoop + (cs + (ck + (cs + (cs + (cOver + (cs + cTail))))))) ≤
      cCur + cLoop + (4 * cs + ck) + cOver + cTail := by
  omega

private theorem p2c_split_live_le (ls lk lOver : Nat) :
    0 + (0 + (ls + (lk + (ls + (ls + (lOver + ls)))))) ≤ (4 * ls + lk) + lOver := by
  omega

private theorem p2c_split_maxReq_le (rCurAll rDec rTr rSerAll rs rk ikmCap : Nat) :
    max (max rCurAll 192)
      (max (max rDec rTr)
        (max rs (max rk (max rs (max rs
          (max (max rSerAll (max ikmCap 4224)) (max rs 192))))))) ≤
    max (max rCurAll (max rDec rTr))
      (max rSerAll (max (max rs rk) (max ikmCap 4224))) := by
  let T := max (max rCurAll (max rDec rTr))
    (max rSerAll (max (max rs rk) (max ikmCap 4224)))
  have hL : max rCurAll (max rDec rTr) ≤ T := Nat.le_max_left _ _
  have hR : max rSerAll (max (max rs rk) (max ikmCap 4224)) ≤ T := Nat.le_max_right _ _
  have h1 : rCurAll ≤ T := Nat.le_trans (Nat.le_max_left _ _) hL
  have h2 : max rDec rTr ≤ T := Nat.le_trans (Nat.le_max_right _ _) hL
  have h3 : rSerAll ≤ T := Nat.le_trans (Nat.le_max_left _ _) hR
  have h4 : max (max rs rk) (max ikmCap 4224) ≤ T := Nat.le_trans (Nat.le_max_right _ _) hR
  have hrs : rs ≤ T := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _) |> fun h => Nat.le_trans h h4
  have hrk : rk ≤ T := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _) |> fun h => Nat.le_trans h h4
  have hikm : max ikmCap 4224 ≤ T := Nat.le_trans (Nat.le_max_right _ _) h4
  have h192 : 192 ≤ T :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hikm)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨h1, h192⟩,
     Nat.max_le.mpr ⟨h2,
       Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨hrk, Nat.max_le.mpr ⟨hrs,
         Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨h3, hikm⟩,
           Nat.max_le.mpr ⟨hrs, h192⟩⟩⟩⟩⟩⟩⟩⟩

private theorem p4_split_maxReq_le (r32s r32k r16s rSt : Nat) :
    max r32s (max r32k (max r16s rSt)) ≤ max (max r32s r32k) (max r16s rSt) := by
  have hs : r32s ≤ max (max r32s r32k) (max r16s rSt) :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hk : r32k ≤ max (max r32s r32k) (max r16s rSt) :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  exact Nat.max_le.mpr ⟨hs, Nat.max_le.mpr ⟨hk, Nat.le_max_right _ _⟩⟩

private theorem zero_or_max4_le (x : Nat) :
    max 0 (max (max x x) (max x x)) ≤ x := by
  omega

private theorem slot_final_peak_le (rp l : Nat) :
    max 0 (max (max rp rp) (max rp rp)) ≤ max rp l :=
  Nat.le_trans (zero_or_max4_le rp) (Nat.le_max_left rp l)

/-! ## Closed 5-Slot Whole-`main` Kernel `by decide` RAM Checks -/

/-- Direct 5-slot `run` constants under Variant (i) (`W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes`). -/
@[expose] def cliRealDirectRunCum_i : Nat :=
  cliRun1MiBCustomPksmCum cliRealPksmCumCap w3InitRealCum
    w1SendRealDcanCum w2RecvWhisperRealDcanCum w4RecvPrekeyReal1MiB_i_Cum

@[expose] def cliRealDirectRunLive_i : Nat :=
  cliRun1MiBCustomPksmLive cliRealPksmLiveCap w3InitRealLive
    w1SendRealDcanLive w2RecvWhisperRealDcanLive w4RecvPrekeyReal1MiB_i_Live

@[expose] def cliRealDirectRunPeak_i : Nat :=
  cliRun1MiBCustomPksmPeak cliRealPksmLiveCap cliRealPksmPeakCap w3InitRealPeak
    w1SendRealDcanLive w1SendRealDcanPeak w2RecvWhisperRealDcanPeak w4RecvPrekeyReal1MiB_i_Peak

@[expose] def cliRealDirectRunMaxReq_i : Nat :=
  cliRun1MiBCustomPksmMaxReq cliRealPksmReqCap w3InitRealMaxReq
    w1SendRealDcanMaxReq w2RecvWhisperRealDcanMaxReq w4RecvPrekeyReal1MiB_i_MaxReq

@[expose] def cliRealDirectRunGrpS_i : Nat :=
  cliRunOpenedCustomPksmGrpS msgCapBytes cliRealPksmGrpSCap w3InitRealGrpS
    w1SendRealDcanGrpS w2RecvWhisperRealDcanGrpS w4RecvPrekeyRealGrpS

/-- Direct 5-slot `run` constants under Variant (ii) (`W4RecvPrekeyRealDomSplit 4096 sessionCapBytes msgCapBytes`). -/
@[expose] def cliRealDirectRunCum_ii : Nat :=
  cliRun1MiBCustomPksmCum cliRealPksmCumCap w3InitRealCum
    w1SendRealDcanCum w2RecvWhisperRealDcanCum w4RecvPrekeyReal1MiB_ii_Cum

@[expose] def cliRealDirectRunLive_ii : Nat :=
  cliRun1MiBCustomPksmLive cliRealPksmLiveCap w3InitRealLive
    w1SendRealDcanLive w2RecvWhisperRealDcanLive w4RecvPrekeyReal1MiB_ii_Live

@[expose] def cliRealDirectRunPeak_ii : Nat :=
  cliRun1MiBCustomPksmPeak cliRealPksmLiveCap cliRealPksmPeakCap w3InitRealPeak
    w1SendRealDcanLive w1SendRealDcanPeak w2RecvWhisperRealDcanPeak w4RecvPrekeyReal1MiB_ii_Peak

@[expose] def cliRealDirectRunMaxReq_ii : Nat :=
  cliRun1MiBCustomPksmMaxReq cliRealPksmReqCap w3InitRealMaxReq
    w1SendRealDcanMaxReq w2RecvWhisperRealDcanMaxReq w4RecvPrekeyReal1MiB_ii_MaxReq

/-- Direct 5-slot `run` constants with adversarial outer PKSM (`pksmSliceCum msgCapBytes`). -/
@[expose] def cliD3DirectRunCum_i : Nat :=
  cliRun1MiBCustomPksmCum (pksmSliceCum msgCapBytes) w3InitRealCum
    w1SendRealDcanCum w2RecvWhisperRealDcanCum w4RecvPrekeyReal1MiB_i_Cum

@[expose] def cliD3DirectRunGrpS_i : Nat :=
  cliRunOpenedCustomPksmGrpS msgCapBytes (pksmTryFromCapDeltaGrpS msgCapBytes) w3InitRealGrpS
    w1SendRealDcanGrpS w2RecvWhisperRealDcanGrpS w4RecvPrekeyRealGrpS

@[expose] def cliD3Pow2SetupCum_1820 : Nat :=
  (2 * (16 * 1820) + 9539) +
    ((2 * 64 + 9539) +
      (([4, 8, 16, 32, 64, 128, 256, 512, 1024] : List Nat).map
        (fun k => 2 * (16 * (2 * k)) + 9539)).sum) +
    (2 * 16384 + 9539) + (2 * 16384 + 28617)

@[expose] def cliD3Pow2SetupGrpS_1820 : Nat := (3 + 3 * 10 + 3 + 6 + 57) * FineScale

@[expose] def cliD3DirectMainRamNeed_i : Nat :=
  let mainCum := cliD3Pow2SetupCum_1820 + m3PhaseDeltaCum_tight + cliD3DirectRunCum_i +
    cliMaxDirtyEntries * (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum
  let mainPeak := cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i
  let mainReq := max (max (16 * 2048) 16384) (cliMainTightReqOf cliRealDirectRunMaxReq_i)
  let grpS := cliD3Pow2SetupGrpS_1820 + cliD3DirectRunGrpS_i +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale
  let grpCount := (grpS + FineScale - 1) / FineScale
  cliDecoupledRamNeed cliDefaultStaticBytes mainCum mainPeak mainReq grpCount

/-- Whole-`main` `< 90%` (`≤ 966,367,641` B) and `≤ 1 GiB` RAM checks under Variant (i)
(`962,211,497` B canonical PKSM; `1,063,684,458` B adversarial outer PKSM). -/
theorem cliRealDirect1MiB_i_fits_90pct_and_oneGiB :
    cliMainTightRamNeedOf cliRealDirectRunCum_i cliRealDirectRunLive_i
      cliRealDirectRunPeak_i cliRealDirectRunMaxReq_i cliRealDirectRunGrpS_i ≤
      cliRealNinetyPctOneGiB ∧
    cliMainTightRamNeedOf cliRealDirectRunCum_i cliRealDirectRunLive_i
      cliRealDirectRunPeak_i cliRealDirectRunMaxReq_i cliRealDirectRunGrpS_i ≤
      cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      (cliMainTightCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainTightGrpCountOf cliRealDirectRunGrpS_i) ≤ 2 ^ 48 ∧
    cliD3DirectMainRamNeed_i = 1063684458 ∧
    cliD3DirectMainRamNeed_i ≤ cliOneGiB :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

end LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB

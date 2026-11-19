/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import LibsignalBinary.Proofs.E2E.RecordX.ScopeP
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
import LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
import LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
import LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.E2E.Seed.Defs

/-!
# Concrete W1 (`send` / `encrypt`) Real Slot Closure

Instantiates `CliTopBudgetSpec.SingleSlotFineSpec` for `WithStoresEncTightEnv` on `StoresGhost.opened`
under `CliPqxdhInputs W i` and `.send peerAddr`, both parametrically in `DeserEnv` and hard-wired with
`RecordDeserializeCancelEnv`, and discharges the `cliSendSlot*Cap` numerical ceilings.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot

open Arm64.Process (bytesOfString initFsState)
open CryptoGames.LibsignalSession
  (Crypto Mut OutgoingTripleRatchet SessionState ShaCompress Spqr)
open CryptoGames.LibsignalSessionApi (Session SessionRecord execOk)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.E2E.Epochs
  (exec_bind exec_get exec_liftE exec_map exec_modifyGet exec_pure exec_set exec_throw)
open CryptoVerification.E2E.Record (RecordRepr encodeRecord)
open CryptoVerification.E2E.RecordX (RecordInScopeP SessionScopeP)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (PreKeyMsgNewCall WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost addressText cliInputs pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1IdKit w1SessKit)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocEvent rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (FilesBounded PeerSpqrValid dirDomainCaps_opened_sess parseArgs_peer_name_length_le
   peerSpqrValid_of_cliPqInputs_send)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (cliSessLoadPollEnv_groupSpec cliSessStorePollEnv_dom_fine_groupSpec
   cliSmallStorePollEnv_groupSpec phaseGroupSpec_exists_guarded recordSerializeDomFineGrpS)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (cliIo_rd_runFiles_length_le_of_filesBounded w1CliOpenedCustomSendCum
   w1CliOpenedCustomSendLive w1CliOpenedCustomSendMaxReq w1CliOpenedCustomSendPeak)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (SingleSlotFineSpec cliSendSlotCumCap cliSendSlotGrpSCap cliSendSlotLiveCap
   cliSendSlotPeakCap cliSendSlotReqCap)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec (CliAddrTextEnv CliDirGetEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSmallStorePollEnv optLargeCost
   sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
   sessStorePollMaxReq sessStorePollTightDeltaCum sessStorePollTightDeltaLive
   sessStorePollTightDeltaPeak smallStorePollDeltaCum smallStorePollDeltaLive
   smallStorePollDeltaPeak smallStorePollMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
  (msgCapBytes sessionCapBytes spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
  (SpqrSendTightCapEnv spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
   spqrSendTightMaxReq spqrSend_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec (spqrSendTightCap_groupSpec spqrSendTightGroupS w1CliOpenedTightSendCum w1CliOpenedTightSendLive w1CliOpenedTightSendMaxReq w1CliOpenedTightSendPeak)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_send)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_length_le topStateTight_spqrV1_send topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
  (OtrEncryptStepEnv WithStoresEncTightEnv tryCloneLargeDelta_fineCostModel_le_add
   tryCloneSmallDelta_fineCostModel_le_143484)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak (otrAfterNone otrAfterSome)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid SessionCloneDom sessionCloneDom_of_scopeKit_pq)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
  (cliSessStorePoll_exists_dom_phaseCredit_tight encodeRecord_length_le_of_scopeKit)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv fineCostModel_wireGroupHyps kyberPayloadLen preKeyMsgNewDeltaCum
   preKeyMsgNewDeltaGrpS preKeyMsgNewDeltaLive preKeyMsgNewDeltaPeak preKeyMsgNewMaxReq
   preKeyMsgNew_phaseGroup signalMessageNewDeltaCum signalMessageNewDeltaGrpS
   signalMessageNewDeltaLive signalMessageNewDeltaPeak signalMessageNewMaxReq
   signalMessageNewSerLen signalMessageNew_phaseGroup)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
  (tryCloneLargeDelta tryCloneSmallDelta)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq
   deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessionKitBudgetEnv cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (cliSessionKitLoadPollEnv_imp_cliSessLoadPollEnv w1_hLoadEq_of_cliSessionKitBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)

attribute [local simp]
  exec_bind exec_get exec_liftE exec_map exec_modifyGet exec_pure exec_set exec_throw

/-! ## 1. W1 Numerical Cap Constants -/

/-- AES-256-CBC PKCS#7 padded ciphertext byte cap at `msgCapBytes = 1 MiB` (`1,048,592` B). -/
@[expose] def w1CtLenCap : Nat := (msgCapBytes / 16 + 1) * 16

/-- Serialized `SignalMessage` byte cap (`1,052,953` B). -/
@[expose] def w1SmSerCap : Nat := w1CtLenCap + 4096 + 265

/-- Serialized `PreKeySignalMessage` byte cap (`1,054,778` B, covering `≤ 1,569` B ML-KEM-1024). -/
@[expose] def w1PkOutCap : Nat := w1SmSerCap + 1569 + 256

@[expose] def w1SigCumCap : Nat := 4 * w1CtLenCap + 4 * 4096 + 2 * w1SmSerCap + 86121
@[expose] def w1SigLiveCap : Nat := w1CtLenCap + 4096 + w1SmSerCap + 32816
@[expose] def w1SigPeakCap : Nat := 2 * w1CtLenCap + 2 * 4096 + w1SmSerCap + 65662
@[expose] def w1SigReqCap : Nat := w1SmSerCap

@[expose] def w1PkCumCap : Nat := 2 * 1569 + 2 * w1SmSerCap + 2 * w1PkOutCap + 47827
@[expose] def w1PkLiveCap : Nat := w1PkOutCap + 8195
@[expose] def w1PkPeakCap : Nat := 1569 + w1SmSerCap + w1PkOutCap + 41041
@[expose] def w1PkReqCap : Nat := w1PkOutCap

/-- Post-`encrypt` `pqRatchetState` byte cap (`spqrSendTightMaxReq = 286,196` B). -/
@[expose] def w1PostPqCap : Nat := spqrSendTightMaxReq

/-- Post-`encrypt` serialized `SessionRecord` byte cap (`spqrSendTightMaxReq + 2097192 = 2,383,388` B). -/
@[expose] def w1StoreEncCap : Nat := w1PostPqCap + 2097192

@[expose] def w1StoreCumCap : Nat := sessStorePollTightDeltaCum 8420940 0
@[expose] def w1StoreLiveCap : Nat := sessStorePollTightDeltaLive (w1StoreEncCap + 8195) 0
@[expose] def w1StorePeakCap : Nat :=
  sessStorePollTightDeltaPeak
    (1080975 + (w1PostPqCap + 8195) + (w1StoreEncCap + 8195)) 0
@[expose] def w1StoreMaxReqCap : Nat :=
  sessStorePollMaxReq (max (max 208000 w1PostPqCap) w1StoreEncCap) 0

/-- Small-allocation slack (`143,362` B) covering `tryCloneSmallDelta` when `x.ptext.length ≤ msgCapBytes`.
-/
@[expose] def w1SmallCtDeltaCap : Nat := 143362

@[expose] def w1SendRealCum (deserCum : Nat) : Nat :=
  let c_otr := spqrSendTightDeltaCum + 738 + 122 + w1SigCumCap
  let c_ld := sessLoadPollDeltaCum sessionCapBytes deserCum
  let c_id := smallStorePollDeltaCum sessionCapBytes 0
  let c_ap := 738 + 738 + w1StoreCumCap
  let c_save := (738 + c_id) + c_ap
  let c_cm := (738 + c_id) + max 9619 c_save
  let c_fo := max 9619 (2792 + c_otr + w1PkCumCap + c_cm)
  (488 + c_ld) + max 9619 c_fo + w1SmallCtDeltaCap

@[expose] def w1SendRealLive (deserLive : Nat) : Nat :=
  let l_otr := spqrSendTightDeltaLive + (w1CtLenCap + 8195) + w1SigLiveCap
  let l_ld := sessLoadPollDeltaLive sessionCapBytes deserLive
  let l_id := smallStorePollDeltaLive sessionCapBytes 0
  let l_cm := l_id + (l_id + w1StoreLiveCap)
  let l_fo := l_otr + w1PkLiveCap + l_cm
  l_ld + l_fo

@[expose] def w1SendRealPeak (deserLive deserPeak : Nat) : Nat :=
  let l_otr := spqrSendTightDeltaLive + (w1CtLenCap + 8195) + w1SigLiveCap
  let p_otr :=
    max spqrSendTightDeltaPeak (spqrSendTightDeltaLive + (w1CtLenCap + 8195) + w1SigPeakCap)
  let l_ld := sessLoadPollDeltaLive sessionCapBytes deserLive
  let p_ld := sessLoadPollDeltaPeak sessionCapBytes deserPeak
  let l_id := smallStorePollDeltaLive sessionCapBytes 0
  let p_id := smallStorePollDeltaPeak sessionCapBytes 0
  let p_cm := max p_id (l_id + max p_id (l_id + w1StorePeakCap))
  let p_fo := max p_otr (l_otr + max w1PkPeakCap (w1PkLiveCap + p_cm))
  max p_ld (l_ld + p_fo)

@[expose] def w1SendRealMaxReq (deserMaxReq : Nat) : Nat :=
  w1CliOpenedTightSendMaxReq msgCapBytes sessionCapBytes deserMaxReq
    w1SigReqCap w1PkReqCap w1StoreMaxReqCap

@[expose] def w1SendRealGrpS (deserGrpS : Nat) : Nat :=
  24 * FineScale + spqrSendTightGroupS + (42 * FineScale + deserGrpS) +
    signalMessageNewDeltaGrpS + preKeyMsgNewDeltaGrpS +
    144 * FineScale + 144 * FineScale + (6 * FineScale + recordSerializeDomFineGrpS)

/-! ## 2. Guards and `StoresGhost.opened` Store-Kit Envelopes -/

/-- Guard on `SignalMessageNewGhost` (`ciphertext ≤ ctLenCap`, `pqRatchet ≤ 4096`,
`serialized ≤ smSerCap`). -/
abbrev W1SigGuard
    (_r : SessionRecord (List (BitVec 8))) (_sess : Session (List (BitVec 8)))
    (_otr : OutgoingTripleRatchet (List (BitVec 8))) (_taken : SessionState (List (BitVec 8)))
    (g : SignalMessageNewGhost) : Prop :=
  g.ciphertext.length ≤ w1CtLenCap ∧
    g.pqRatchet.length ≤ 4096 ∧
    signalMessageNewSerLen uuidTryParse g ≤ w1SmSerCap

/-- Guard on `PreKeyMsgNewCall` (`kyber ≤ 1569`, inner `SignalMessage ≤ smSerCap`,
outer `PreKeySignalMessage ≤ pkOutCap`). -/
abbrev W1PkCallGuard
    (_r : SessionRecord (List (BitVec 8))) (_sess : Session (List (BitVec 8)))
    (_otr : OutgoingTripleRatchet (List (BitVec 8))) (_taken : SessionState (List (BitVec 8)))
    (call : PreKeyMsgNewCall) : Prop :=
  kyberPayloadLen call.kp ≤ 1569 ∧
    call.msg.serialized.length ≤ w1SmSerCap ∧
    call.model.serialized.length ≤ w1PkOutCap


/-- `WithStoresEncTightEnv` instantiation for W1 (`send`) on `StoresGhost.opened`, parametric in `DeserEnv`.
-/
theorem w1_real_hLoadEq_placed [LibsignalPlacement]
    {A : RustAlloc} {F : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {SerValEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {vtSym idVtSym : String} {rem : AddrVal}
    (hrem : rem = peer.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ sessionCapBytes) :
    ∀ evs,
      (cliSessionKitBudgetEnv A cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
        (fun _ => CliAddrTextEnv peer)
        (CliDirGetEnv (ReadFileRuleEnv cliIo.rd))
        (fun r => DeserEnv (encodeRecord r))
        SerValEnv PutEnv vtSym idVtSym).loadPollEnv
        StoresGhost.opened.sessions rem evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs :=
  w1_hLoadEq_of_cliSessionKitBudgetEnv hrem (by unfold sessionCapBytes; decide) hSessFileCap
    (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)

private theorem w1SigGuard_bounds {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {g : SignalMessageNewGhost}
    (hg : W1SigGuard r sess otr taken g) :
    signalMessageNewDeltaCum uuidTryParse g ≤ w1SigCumCap ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ w1SigLiveCap ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ w1SigPeakCap ∧
      signalMessageNewMaxReq uuidTryParse g ≤ w1SigReqCap := by
  rcases hg with ⟨hct, hpq, hser⟩
  have h36 : 36 ≤ w1SmSerCap := by unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hct_sm : w1CtLenCap ≤ w1SmSerCap := by unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hpq_sm : 4096 ≤ w1SmSerCap := by unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold signalMessageNewDeltaCum w1SigCumCap
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left 4 hct) (Nat.mul_le_mul_left 4 hpq))
        (Nat.mul_le_mul_left 2 hser))
      (Nat.le_refl _)
  · unfold signalMessageNewDeltaLive w1SigLiveCap
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hct hpq) hser) (Nat.le_refl _)
  · unfold signalMessageNewDeltaPeak w1SigPeakCap
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hct) (Nat.mul_le_mul_left 2 hpq)) hser)
      (Nat.le_refl _)
  · unfold signalMessageNewMaxReq w1SigReqCap
    exact Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨h36, Nat.le_trans hct hct_sm⟩,
       Nat.max_le.mpr ⟨Nat.le_trans hpq hpq_sm, hser⟩⟩

private theorem w1PkCallGuard_bounds {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {call : PreKeyMsgNewCall}
    (hc : W1PkCallGuard r sess otr taken call) :
    preKeyMsgNewDeltaCum call ≤ w1PkCumCap ∧
      preKeyMsgNewDeltaLive call ≤ w1PkLiveCap ∧
      preKeyMsgNewDeltaPeak call ≤ w1PkPeakCap ∧
      preKeyMsgNewMaxReq call ≤ w1PkReqCap := by
  rcases hc with ⟨hkp, hsm, hout⟩
  have h33 : 33 ≤ w1PkOutCap := by unfold w1PkOutCap w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hkp_pk : 1569 ≤ w1PkOutCap := by unfold w1PkOutCap w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hsm_pk : w1SmSerCap ≤ w1PkOutCap := by unfold w1PkOutCap w1SmSerCap w1CtLenCap msgCapBytes; decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold preKeyMsgNewDeltaCum WireMsgPeakSpec.preKeyMsgNewRawDeltaCum w1PkCumCap
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left 2 hkp) (Nat.mul_le_mul_left 2 hsm))
        (Nat.mul_le_mul_left 2 hout))
      (Nat.le_refl _)
  · unfold preKeyMsgNewDeltaLive WireMsgPeakSpec.preKeyMsgNewRawDeltaLive w1PkLiveCap
    exact Nat.add_le_add_right hout 8195
  · unfold preKeyMsgNewDeltaPeak WireMsgPeakSpec.preKeyMsgNewRawDeltaPeak w1PkPeakCap
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hkp hsm) hout) (Nat.le_refl _)
  · unfold preKeyMsgNewMaxReq WireMsgPeakSpec.preKeyMsgNewRawMaxReq w1PkReqCap
    exact Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨Nat.le_trans hkp hkp_pk, h33⟩,
       Nat.max_le.mpr ⟨Nat.le_trans hsm hsm_pk, hout⟩⟩

private theorem fromSessionState_pqr_and_taken_local
    {st : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState st = .ok (otr, taken)) :
    otr.pqrState = st.pqRatchetState ∧ taken = { st with pqRatchetState := [] } := by
  unfold execOk OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_get, exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, exec_pure, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨rfl, ?_⟩
        cases st
        dsimp only at hsc hrem
        subst hsc hrem
        rfl

private theorem otr_encrypt_pqrState_cases {PQC : Type}
    (C : Crypto) (S : Spqr (List (BitVec 8)) PQC)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : PQC)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) :
    (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S ptext addrs coins) otr).2.pqrState =
      otr.pqrState ∨
    ∃ newPqr pqrKey pqrMsg,
      S.send otr.pqrState coins = some (newPqr, pqrKey, pqrMsg) ∧
      (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S ptext addrs coins) otr).2.pqrState =
        newPqr := by
  unfold OutgoingTripleRatchet.encrypt
  simp only [exec_bind, exec_get]
  cases S.sendPanics otr.pqrState coins
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases S.send otr.pqrState coins with _ | ⟨newPqr, pqrKey, pqrMsg⟩
    · left; simp
    · dsimp only
      rcases otr.senderChainKey.nextChainKey C.F with _ | _
      · left; simp
      · right; refine ⟨newPqr, pqrKey, pqrMsg, rfl, ?_⟩; simp
  · left; simp

private theorem otr_encrypt_topStateTight
    {F : ShaCompress} {K : MlKem} (C : Crypto) (hF : C.F = F)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8))
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (hTop : TopStateTight F K otr.pqrState) :
    TopStateTight F K
      (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec (spqrV1 F K).spqr
        ptext addrs coins) otr).2.pqrState := by
  subst hF
  rcases otr_encrypt_pqrState_cases C (spqrV1 C.F K).spqr ptext addrs coins otr with
    heq | ⟨newPqr, _, _, hs, heq⟩
  · rw [heq]; exact hTop
  · rw [heq]; exact topStateTight_spqrV1_send hTop hs

private theorem storedRecord_scopeKit_and_bounds
    {F : ShaCompress} {K : MlKem}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (hKit : scopeKit r)
    (hcur : r.currentSession = some sess)
    (htaken : taken = { sess.state with pqRatchetState := [] })
    (hTop' : TopStateTight F K otr'.pqrState) :
    (∀ ses, (storedRecord sess otr' taken).currentSession = some ses →
      SessionCloneDom w1PostPqCap ses) ∧
    (encodeRecord (storedRecord sess otr' taken)).length ≤ w1StoreEncCap := by
  subst htaken
  have hpqCap : otr'.pqrState.length ≤ w1PostPqCap := by
    have hle := topStateTight_length_le hTop'
    have heq : spqrStateTightCapBytes = w1PostPqCap := by
      unfold spqrStateTightCapBytes w1PostPqCap spqrSendTightMaxReq
      decide
    rwa [heq] at hle
  have hotr'_lt32 : otr'.pqrState.length < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hpqCap (by unfold w1PostPqCap spqrSendTightMaxReq; decide)
  obtain ⟨⟨hInP, _, hRepr⟩, s0, hs0, hSessP⟩ := hKit
  have hsess_eq : s0 = sess := Option.some.inj (hs0.symm.trans hcur)
  subst hsess_eq
  have hInSess := hInP s0 hcur
  have hReprSess := hRepr s0 hcur
  have hRecIn' :
      RecordInScopeP (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    unfold OutgoingTripleRatchet.applyToSessionState
    exact ⟨hInSess.1, hInSess.2.1, hInSess.2.2⟩
  have hRepr' :
      RecordRepr (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    refine ⟨hReprSess.1, ?_, ?_, hReprSess.2.2.2⟩
    · intro sc' hsc'
      simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_eq_some_iff] at hsc'
      obtain ⟨sc, hsc, rfl⟩ := hsc'
      exact hReprSess.2.1 sc hsc
    · simpa [Session.Wf, OutgoingTripleRatchet.applyToSessionState] using hReprSess.2.2.1
  have hSessP' :
      SessionScopeP
        { s0 with state := otr'.applyToSessionState { s0.state with pqRatchetState := [] } } :=
    ⟨hSessP.1, hSessP.2.1, hSessP.2.2.1, hSessP.2.2.2⟩
  have hScope' :
      scopeKit (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    refine ⟨⟨hRecIn', ?_, hRepr'⟩, _, rfl, hSessP'⟩
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    exact hotr'_lt32
  have hPq' : ∀ ses,
      (storedRecord s0 otr' { s0.state with pqRatchetState := [] }).currentSession = some ses →
      ses.state.pqRatchetState.length ≤ w1PostPqCap := by
    intro ses hses
    simp only [storedRecord, Option.some.injEq] at hses
    subst hses
    exact hpqCap
  exact ⟨fun ses hses => sessionCloneDom_of_scopeKit_pq hScope' hses (hPq' ses hses),
    encodeRecord_length_le_of_scopeKit hScope' hPq'⟩

private theorem optLargeCost_fine_w1PostPqCap :
    optLargeCost fineCostModel w1PostPqCap = w1PostPqCap + 8195 := by
  unfold optLargeCost
  rw [fineCostModel_smallMaxReq_eq, fineCostModel_largeCost_eq]
  have hnot : ¬ (w1PostPqCap ≤ 135167) := by
    unfold w1PostPqCap spqrSendTightMaxReq
    decide
  simp only [hnot, ↓reduceIte]

private theorem optLargeCost_fine_w1StoreEncCap :
    optLargeCost fineCostModel w1StoreEncCap = w1StoreEncCap + 8195 := by
  unfold optLargeCost
  rw [fineCostModel_smallMaxReq_eq, fineCostModel_largeCost_eq]
  have hnot : ¬ (w1StoreEncCap ≤ 135167) := by
    unfold w1StoreEncCap w1PostPqCap spqrSendTightMaxReq
    decide
  simp only [hnot, ↓reduceIte]

private theorem smallAllocCost_fine_24 :
    HasFineReallocCredit.smallAllocCost fineCostModel 24 = 488 := by
  change fineSmallAllocCost 24 = 488
  decide

private theorem smallAllocCost_fine_32 :
    HasFineReallocCredit.smallAllocCost fineCostModel 32 = 738 := by
  change fineSmallAllocCost 32 = 738
  decide

private theorem smallAllocCost_fine_1569 :
    HasFineReallocCredit.smallAllocCost fineCostModel 1569 = 2792 := by
  change fineSmallAllocCost 1569 = 2792
  decide

private theorem w1Cum_mono_aux {L N p0 cs p1 s b sm pk cm k : Nat} (h : s ≤ b + k) :
    L + max N (max N (p0 + (cs + (p1 + s + sm)) + pk + cm)) ≤
      L + max N (max N (p0 + (cs + p1 + b + sm) + pk + cm)) + k := by
  omega

private theorem w1Live_mono_aux {l_ld l_s x y l_sig l_pk l_cm : Nat} (h : x ≤ y) :
    l_ld + ((l_s + x + l_sig) + l_pk + l_cm) ≤
      l_ld + ((l_s + y + l_sig) + l_pk + l_cm) := by
  omega

private theorem w1Peak_mono_aux {p_ld l_ld p_s l_s x y p_sig l_sig p_pk l_pk p_cm : Nat}
    (h : x ≤ y) :
    max p_ld
        (l_ld +
          max (max p_s (l_s + x + p_sig))
            ((l_s + x + l_sig) + max p_pk (l_pk + p_cm))) ≤
      max p_ld
        (l_ld +
          max (max p_s (l_s + y + p_sig))
            ((l_s + y + l_sig) + max p_pk (l_pk + p_cm))) := by
  omega

private theorem w1MaxReq_mono_aux {a b c d r_s e x y r_sig rest : Nat} (h : x ≤ y) :
    max a (max b (max c (max d (max (max r_s (max e (max x r_sig))) rest)))) ≤
      max a (max b (max c (max d (max (max r_s (max e (max y r_sig))) rest)))) := by
  omega

private theorem w1Live_le_peak_aux
    {l_ld p_ld l_s c l_sig p_s p_sig l_pk p_pk l_id p_id l_st p_st : Nat}
    (hst : l_st ≤ p_st) :
    l_ld + ((l_s + c + l_sig) + l_pk + (l_id + (l_id + l_st))) ≤
      max p_ld
        (l_ld +
          max (max p_s (l_s + c + p_sig))
            ((l_s + c + l_sig) +
              max p_pk (l_pk + max p_id (l_id + max p_id (l_id + p_st))))) := by
  omega

private theorem w1SendReal_ptext_mono
    {ptextLen deserCum deserLive deserPeak deserMaxReq : Nat}
    (hptext : ptextLen ≤ msgCapBytes) :
    w1CliOpenedTightSendCum ptextLen 9619 sessionCapBytes deserCum
      w1SigCumCap w1PkCumCap w1StoreCumCap ≤ w1SendRealCum deserCum ∧
    w1CliOpenedTightSendLive ptextLen sessionCapBytes deserLive
      w1SigLiveCap w1PkLiveCap w1StoreLiveCap ≤ w1SendRealLive deserLive ∧
    w1CliOpenedTightSendPeak ptextLen sessionCapBytes deserLive deserPeak
      w1SigLiveCap w1SigPeakCap w1PkLiveCap w1PkPeakCap w1StorePeakCap ≤
      w1SendRealPeak deserLive deserPeak ∧
    w1CliOpenedTightSendMaxReq ptextLen sessionCapBytes deserMaxReq
      w1SigReqCap w1PkReqCap w1StoreMaxReqCap ≤ w1SendRealMaxReq deserMaxReq := by
  have hct0 : (ptextLen / 16 + 1) * 16 ≤ (msgCapBytes / 16 + 1) * 16 :=
    Nat.mul_le_mul_right 16 (Nat.add_le_add_right (Nat.div_le_div_right hptext) 1)
  have hct : (ptextLen / 16 + 1) * 16 ≤ w1CtLenCap := hct0
  have hsm :
      tryCloneSmallDelta fineCostModel ((ptextLen / 16 + 1) * 16) ≤
        122 + w1SmallCtDeltaCap :=
    Nat.le_trans
      (tryCloneSmallDelta_fineCostModel_le_143484 ((ptextLen / 16 + 1) * 16))
      (by unfold w1SmallCtDeltaCap; decide)
  have hlg :
      tryCloneLargeDelta fineCostModel ((ptextLen / 16 + 1) * 16) ≤
        w1CtLenCap + 8195 :=
    tryCloneLargeDelta_fineCostModel_le_add hct
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold w1SendRealCum w1CliOpenedTightSendCum w1CliOpenedCustomSendCum
    dsimp only
    have hmax30537 :
        max 30537
          (738 + tryCloneSmallDelta fineCostModel ((ptextLen / 16 + 1) * 16) + w1SigCumCap) =
        738 + tryCloneSmallDelta fineCostModel ((ptextLen / 16 + 1) * 16) + w1SigCumCap := by
      have : 30537 ≤ w1SigCumCap := by decide
      omega
    rw [smallAllocCost_fine_24, smallAllocCost_fine_32, smallAllocCost_fine_1569, hmax30537]
    exact w1Cum_mono_aux hsm
  · unfold w1SendRealLive w1CliOpenedTightSendLive w1CliOpenedCustomSendLive
    dsimp only
    exact w1Live_mono_aux hlg
  · unfold w1SendRealPeak w1CliOpenedTightSendPeak w1CliOpenedCustomSendPeak
    dsimp only
    exact w1Peak_mono_aux hlg
  · unfold w1SendRealMaxReq w1CliOpenedTightSendMaxReq w1CliOpenedCustomSendMaxReq
    dsimp only
    exact w1MaxReq_mono_aux hct0

private theorem w1StoreLive_le_Peak :
    w1StoreLiveCap ≤ w1StorePeakCap := by
  decide

theorem w1SendReal_live_le_peak (deserLive deserPeak : Nat) :
    w1SendRealLive deserLive ≤ w1SendRealPeak deserLive deserPeak := by
  unfold w1SendRealLive w1SendRealPeak
  dsimp only
  exact w1Live_le_peak_aux w1StoreLive_le_Peak

/-! ## 5. Parametric `SingleSlotFineSpec` -/



/-- Set A `cliSendSlot*Cap` numerical check. -/
theorem w1SendReal_caps_setA :
    w1SendRealCum 20638720 ≤ cliSendSlotCumCap ∧
      w1SendRealLive 3211282 ≤ cliSendSlotLiveCap ∧
      w1SendRealPeak 3211282 5316629 ≤ cliSendSlotPeakCap ∧
      w1SendRealMaxReq 2097152 ≤ cliSendSlotReqCap ∧
      w1SendRealGrpS 371994912 ≤ cliSendSlotGrpSCap := by
  decide

/-- Set B `cliSendSlot*Cap` numerical check. -/
theorem w1SendReal_caps_setB :
    w1SendRealCum 19417728 ≤ cliSendSlotCumCap ∧
      w1SendRealLive 3211282 ≤ cliSendSlotLiveCap ∧
      w1SendRealPeak 3211282 5316629 ≤ cliSendSlotPeakCap ∧
      w1SendRealMaxReq 2097152 ≤ cliSendSlotReqCap ∧
      w1SendRealGrpS 346829088 ≤ cliSendSlotGrpSCap := by
  decide

theorem peer_and_rem_name_le_40_of_send {i : Inputs} {peerAddr : AddrV}
    {peer : AddrGhost} {x : WithStoresEncGhost}
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peerAddr))
    (hpeerVal : peer.val = addrValOf peerAddr)
    (hrem : x.rem.val = peer.val) :
    peer.name.bytes.length ≤ 40 ∧ x.rem.name.bytes.length ≤ 40 := by
  have hp40 : peerAddr.name.length ≤ 40 := parseArgs_peer_name_length_le hparse
  have hpeer : peer.name.bytes.length ≤ 40 := by
    change peer.val.name.length ≤ 40
    rw [hpeerVal]
    exact hp40
  have hremName : x.rem.name.bytes.length ≤ 40 := by
    change x.rem.val.name.length ≤ 40
    rw [hrem, hpeerVal]
    exact hp40
  exact ⟨hpeer, hremName⟩

@[expose] def w1SendRealNoDeserCum : Nat := w1SendRealCum 0

@[expose] def w1SendRealDcanCum : Nat := w1SendRealCum deserCancelFineCum

@[expose] def w1SendRealDcanLive : Nat := w1SendRealLive deserCancelFineLive

@[expose] def w1SendRealDcanPeak : Nat := w1SendRealPeak deserCancelFineLive deserCancelFinePeak

@[expose] def w1SendRealDcanMaxReq : Nat := w1SendRealMaxReq deserCancelFineMaxReq

@[expose] def w1SendRealDcanGrpS : Nat := w1SendRealGrpS deserCancelFineGrpS

theorem w1SendRealDcan_live_le_peak :
    w1SendRealDcanLive ≤ w1SendRealDcanPeak :=
  w1SendReal_live_le_peak deserCancelFineLive deserCancelFinePeak

/-- Decomposition and `cliSendSlot*Cap` check for the `RecordDeserializeCancelEnv`-wired W1 slot. -/
theorem w1SendReal_dcan_caps_le :
    deserCancelFineCum = 16890453 ∧
    w1SendRealDcanCum = w1SendRealNoDeserCum + deserCancelFineCum ∧
    w1SendRealDcanCum ≤ cliSendSlotCumCap ∧
    w1SendRealDcanLive ≤ cliSendSlotLiveCap ∧
    w1SendRealDcanPeak ≤ cliSendSlotPeakCap ∧
    w1SendRealDcanMaxReq ≤ cliSendSlotReqCap ∧
    w1SendRealDcanGrpS ≤ cliSendSlotGrpSCap := by
  decide

/-- Call-site parameter bundle for the real CLI W1 (`send`) slot. -/
structure W1SendRealParams where
  B : RunBudgets
  peer : AddrGhost
  x : WithStoresEncGhost

/-- Call-site alignment and 1 MiB plaintext bound for `W1SendRealParams` on `.send peerAddr`. -/
@[expose] def W1SendRealDom (c : CallV) (R : W1SendRealParams) : Prop :=
  ∀ peerAddr, c = .send peerAddr →
    R.peer.val = addrValOf peerAddr ∧
    R.x.rem.val = R.peer.val ∧
    R.x.ptext.length ≤ msgCapBytes



end LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot


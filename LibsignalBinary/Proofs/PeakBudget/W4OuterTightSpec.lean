/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.E2E.Seed.Defs
import LibsignalBinary.Proofs.PeakBudget.W4InnerPeakSpec

/-!
# Tight `fineCostModel` `decrypt_prekey` Slot Specification

Tight `fineCostModel` slot credit specification for `signal_session_handshake::decrypt_prekey` /
`process_prekey`:
1. Tight clone, record-serialize, and store-poll bounds (`segCloneTightCum`,
   `recordSerializeTightCum`, `sessLoadPollTightDelta*`, `sessStorePollTightDelta*`,
   `smallStorePollTightDelta*`, `w4SpqrInit32_fine_phaseCredit`) with separate
   `(sessFileCap, smallFileCap)` store caps.
2. Fresh-Bob `prev1` serialization (`FreshBobPrev1Dom`, `0` receiver chains) on Path C.
3. Split-arm slot envelopes (`W4DecryptPrekeySplitSlotEnv`, `W4DecryptPrekeySplitWideSlotEnv`)
   parameterized by black-box `PhaseCreditSpec` inputs (`TryDecEnv` vs `TryDecAC`), plus
   re-exports of `fitsEnv_fineCostModel_of_phaseCredit` and `w4SlotR3b_live_le_peak`.
-/

public section

namespace LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec

set_option autoImplicit false

open CryptoGames.LibsignalSession (SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule StoresGhost addressText keyName pathOf)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec IterSeqEnv PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (RecordSerializeCancelEnv dropClonedSessionEvents sessLoadPollTightDeltaCum
   sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak sessLoadPollTightMaxReq
   sessStorePollMaxReq sessStorePollTightDeltaCum sessStorePollTightDeltaLive
   sessStorePollTightDeltaPeak smallStorePollTightDeltaCum smallStorePollTightDeltaLive
   smallStorePollTightDeltaPeak smallStorePollTightMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (FreshBobCloneDom SessionCloneDom phaseCreditSpec_fromFEnv_fine_488
   phaseCreditSpec_fromMEnv_fine_8674 serialize_dom_phaseCredit_tight
   sessionClone_dom_phaseCredit_tight sessionClone_drop_cancel_dom_phaseCredit_tight
   sessionClone_freshBob16K_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (w2TryDecryptMaxReq w2TryDecryptTightLive w2TryDecryptTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
  (w2TryDecryptGenSeeds738Cum w2TryDecryptSeeds738Cum)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv PromoteStateArchiveEnv phaseCredit_archivedTrialLoop_le4)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BobSessionBuildEnv W4InitBobSpqrEnv W4PqxdhAcceptEnv W4StageP2OverBobEnv
   phaseCredit_w4BobSessionBuild_small phaseCredit_w4InitBob_small
   phaseCredit_w4PqxdhAccept_small phaseCredit_w4StageP2OverBob_small w4InitBobOuterCum)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
  (phaseCreditSpec_ite_nil phaseCreditSpec_or4 stringClone_phaseCredit_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4DecryptPrekeyPathAEnv W4DecryptPrekeyPathAWideEnv W4DecryptPrekeyPathBEnv
   W4DecryptPrekeyPathBWideEnv W4DecryptPrekeyPathCEnv W4DecryptPrekeyPathCWideEnv
   W4DecryptPrekeySlotEnv W4DecryptPrekeySlotParams W4DecryptPrekeySplitWideSlotEnv
   W4DecryptPrekeyWideSlotEnv W4ErrTailEnv W4ErrTailWideEnv W4InitBobSpqrWideEnv
   W4InitBobWideEnv W4SlotR3bEnv W4StageP2MatchedCheckEnv W4StageP2MatchedEnv
   W4StageP2MatchedErrStrEnv W4StageP2MatchedWideEnv W4StageP2OverBobWideEnv
   W4StageP2PathACliEnv W4StageP2PathACliWideEnv W4StageP2PathCCliEnv W4StageP2PathCCliWideEnv
   W4StageP3Env W4StageP3WideEnv W4StageP4MatchedCliWideEnv W4StageP4PathACliWideEnv
   W4StageP4PathCCliWideEnv W4TryDecryptCloneFailWideEnv phaseCredit_optStageEnv
   w4SlotR3bDeltaCum w4SlotR3bDeltaLive w4SlotR3bDeltaPeak w4SlotR3bMaxReq
   w4SlotR3b_fine_phaseCredit w4SlotR3b_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (W4SmallStoreStepEnv W4StageP1OkCliEnv W4StageP1UntrustedCliEnv W4StageP4MatchedCliEnv
   W4StageP4PathACliEnv W4StageP4PathCCliEnv opened_all_dirDomainCaps
   phaseCreditSpec_seq_freeOnly_exact w4SpqrInitCum)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (FreshBobPrev1Dom fineOptLarge optLargeCost_fine_eq promoteStateArchive_dom_fine_phaseCredit_tight
   tryDecryptCloneFail_dom_fine_cancel_phaseCredit w4ErrTail_fine_phaseCredit_tight
   w4KeyIdSmallStoreStep16_fine_phaseCredit w4PeerSmallStoreStep32_fine_phaseCredit
   w4SessLoadStep_fine_phaseCredit w4SessStorePrev1Step_freshBob_fine_phaseCredit
   w4SessStoreStep_dom_fine_phaseCredit w4SmallStoreStep16_fine_phaseCredit
   w4SmallStoreStep32_fine_phaseCredit w4SpqrInit32_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (W4TryDecryptCloneFailEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## Arithmetic Combinators -/

private theorem max_mono {a a' b b' : Nat} (ha : a ≤ a') (hb : b ≤ b') :
    max a b ≤ max a' b' :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _),
    Nat.le_trans hb (Nat.le_max_right _ _)⟩

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

private theorem fiveStepPeak_mono {p l q q' : Nat} (hq : q ≤ q') :
    max p (l + max p (l + max p (l + max p (l + q)))) ≤
      max p (l + max p (l + max p (l + max p (l + q')))) :=
  seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
    (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
      (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) hq)))

private theorem le_fiveStepPeak_inner (p l pOver tail : Nat) :
    pOver ≤ max p (l + max p (l + max p (l + max p (l + max pOver tail)))) := by
  have h1 : pOver ≤ max pOver tail := Nat.le_max_left _ _
  have h2 : pOver ≤ max p (l + max pOver tail) :=
    Nat.le_trans h1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
  have h3 : pOver ≤ max p (l + max p (l + max pOver tail)) :=
    Nat.le_trans h2 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
  have h4 : pOver ≤ max p (l + max p (l + max p (l + max pOver tail))) :=
    Nat.le_trans h3 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
  exact Nat.le_trans h4 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))

private theorem le_twoStepPeak_left (p2 l2 p3 l3 a b : Nat) :
    a ≤ max p2 (l2 + max p3 (l3 + max a b)) := by
  have h1 : a ≤ max a b := Nat.le_max_left a b
  have h2 : a ≤ max p3 (l3 + max a b) :=
    Nat.le_trans h1 (Nat.le_trans (Nat.le_add_left _ l3) (Nat.le_max_right p3 _))
  exact Nat.le_trans h2 (Nat.le_trans (Nat.le_add_left _ l2) (Nat.le_max_right p2 _))

private theorem zero_or_max4_le (x : Nat) :
    max 0 (max (max x x) (max x x)) ≤ x := by
  omega

private theorem slot_final_peak_le (rp l : Nat) :
    max 0 (max (max rp rp) (max rp rp)) ≤ max rp l :=
  Nat.le_trans (zero_or_max4_le rp) (Nat.le_max_left rp l)

/-! ## Tight `fineCostModel` Stage P1, P2, P3, & P4 `PhaseCreditSpec`s -/

theorem w4StageP1OkCli_fine_phaseCredit
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir peersDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal sessFileCap smallFileCap
     deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hSessCap : ∀ bs, rd files (pathOf sessDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ sessFileCap)
    (hPeersCap : ∀ bs, rd files (pathOf peersDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ smallFileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    let cL := 488 + sessLoadPollTightDeltaCum sCap deserCum
    let lL := sessLoadPollTightDeltaLive sCap deserLive
    let pL := sessLoadPollTightDeltaPeak sCap deserPeak
    let rL := max 24 (sessLoadPollTightMaxReq sCap deserMaxReq)
    let cT := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let lT := smallStorePollTightDeltaLive smCap maxEntries
    let pT := smallStorePollTightDeltaPeak smCap maxEntries
    let rT := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    PhaseCreditSpec fineCostModel (W4StageP1OkCliEnv rd DeserEnv files sessDir peersDir peer)
      (cL + cT) (lL + lT) (max pL (lL + pT)) (max rL rT) := by
  dsimp only
  have hLoad := w4SessLoadStep_fine_phaseCredit hdcSess hdir hpeer hSessCap hdeser
  have hTrust := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer hPeersCap
  exact hLoad.seq hTrust

theorem w4StageP1UntrustedCli_fine_phaseCredit
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir peersDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal sessFileCap smallFileCap
     deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hSessCap : ∀ bs, rd files (pathOf sessDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ sessFileCap)
    (hPeersCap : ∀ bs, rd files (pathOf peersDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ smallFileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    let cL := 488 + sessLoadPollTightDeltaCum sCap deserCum
    let lL := sessLoadPollTightDeltaLive sCap deserLive
    let pL := sessLoadPollTightDeltaPeak sCap deserPeak
    let rL := max 24 (sessLoadPollTightMaxReq sCap deserMaxReq)
    let cT := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let lT := smallStorePollTightDeltaLive smCap maxEntries
    let pT := smallStorePollTightDeltaPeak smCap maxEntries
    let rT := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP1UntrustedCliEnv rd DeserEnv files sessDir peersDir peer)
      (cL + cT + 9619)
      (lL + lT)
      (max pL (lL + max pT lT))
      (max rL (max rT 40)) := by
  dsimp only
  have hSm40 : 40 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hLoad := w4SessLoadStep_fine_phaseCredit hdcSess hdir hpeer hSessCap hdeser
  have hTrust := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer hPeersCap
  have hClone := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (stringClone_phaseCredit_small fineCostModel_modelHyps hpeer hSm40)
  have hTC := (hTrust.seq hClone).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
    (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  exact (hLoad.seq hTC).mono
    (Nat.le_of_eq (Nat.add_assoc _ _ 9619).symm)
    (Nat.le_of_eq (Nat.add_assoc _ _ 0 ▸ rfl))
    (Nat.le_refl _)
    (Nat.le_refl _)

theorem w4StageP2Matched_dom_fine_phaseCredit {α : Type}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push archPqCap archEncCap : Nat}
    {l_dec : α → Nat} {xs : List α}
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (hArchValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses)
    (hArchEnc : (encodeRecord r_arch).length ≤ archEncCap)
    (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec fineCostModel (DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel VecPushEnv c_push 0 0 r_push) :
    PhaseCreditSpec fineCostModel
      (W4StageP2MatchedEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv)
      (4 * (c_dec + c_tr) + (8420940 + c_push))
      (fineOptLarge archEncCap)
      (max (p_dec + p_tr) (1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap))
      (max (max r_dec r_tr) (max (max (max 208000 archPqCap) archEncCap) r_push)) := by
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hLoop := phaseCredit_archivedTrialLoop_le4 hlen4 hl_le_p hDec hTrial hDrop
  have hProm := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (promoteStateArchive_dom_fine_phaseCredit_tight hArchValid hArchEnc hPush)
  have hOptProm := (hFree.or hProm).mono
    (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
    (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
  have hSeq := (hLoop.seq hOptProm).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.zero_add _))
    (Nat.le_of_eq (congrArg (max _) (Nat.zero_add _))) (Nat.le_refl _)
  exact (hFree.or hSeq).mono
    (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
    (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))

private theorem p2a_tight_cum_le (a b1 b2 c : Nat) :
    a + (a + (a + (a + ((b1 + b2) + (a + c))))) ≤ 5 * a + b1 + b2 + c := by
  omega

private theorem p2a_tight_live_le (a : Nat) :
    a + (a + (a + (a + (0 + a)))) ≤ 5 * a := by
  omega

private theorem p2a_bob_maxReq_le (ikmCap : Nat) :
    max (max ikmCap 1569) (max 4224 68) ≤ max ikmCap 4224 :=
  Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨Nat.le_max_left _ _,
       Nat.le_trans (by decide : 1569 ≤ 4224) (Nat.le_max_right _ _)⟩,
     Nat.max_le.mpr ⟨Nat.le_max_right _ _,
       Nat.le_trans (by decide : 68 ≤ 4224) (Nat.le_max_right _ _)⟩⟩

private theorem p2a_tight_maxReq_le (r16 ikmCap : Nat) :
    max r16 (max r16 (max r16 (max r16 (max (max ikmCap 4224) (max r16 192))))) ≤
      max r16 (max ikmCap 4224) := by
  have hr : r16 ≤ max r16 (max ikmCap 4224) := Nat.le_max_left _ _
  have hb : max ikmCap 4224 ≤ max r16 (max ikmCap 4224) := Nat.le_max_right _ _
  have h192 : 192 ≤ max r16 (max ikmCap 4224) :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hb)
  exact Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hr,
    Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hb, Nat.max_le.mpr ⟨hr, h192⟩⟩⟩⟩⟩⟩

theorem w4StageP2PathACli_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal smallFileCap : Nat}
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hSmallCap : ∀ d ∈ [spkDir, kpkDir, opkDir, ownDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap) :
    let smCap := max maxVal smallFileCap
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP2PathACliEnv hasOpk rd files spkDir kpkDir opkDir ownDir spkId kpkId opkId
        ownKeyName ownRegName F x_res x_spqr)
      (5 * c16 + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32 + 8186)
      (5 * l16)
      (max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
        (l16 + max 0 (0 + max p16 l16))))))
      (max r16 (max ikmCap 4224)) := by
  dsimp only
  have hSpk := w4KeyIdSmallStoreStep16_fine_phaseCredit spkId hdcSpk hdir
    (fun bs hr => hSmallCap spkDir (by simp) _ bs hr)
  have hKpk := w4KeyIdSmallStoreStep16_fine_phaseCredit kpkId hdcKpk hdir
    (fun bs hr => hSmallCap kpkDir (by simp) _ bs hr)
  have hOptPk := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
      (fun bs hr => hSmallCap opkDir (by simp) _ bs hr)
  have hKp := w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hkeyName
    (fun bs hr => hSmallCap ownDir (by simp) _ bs hr)
  have hSpqr := w4SpqrInit32_fine_phaseCredit F x_spqr hspqrKey
  have hBob : PhaseCreditSpec fineCostModel (W4InitBobSpqrEnv F x_res hasOpk x_spqr)
      (w4InitBobOuterCum ikmCap + w4SpqrInitCum 32) 0 0 (max ikmCap 4224) :=
    (phaseCredit_w4InitBob_small fineCostModel_modelHyps (hasOpk := hasOpk)
      hold hnew hSmall hSpqr).mono
      (Nat.le_refl _) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_refl 0, Nat.le_refl 0⟩)
      (p2a_bob_maxReq_le ikmCap)
  have hReg := w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hregName
    (fun bs hr => hSmallCap ownDir (by simp) _ bs hr)
  have hTail := w4ErrTail_fine_phaseCredit_tight
  have h67 := (hReg.seq hTail).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
    (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  have h57 := hBob.seq h67
  have h47 := hKp.seq h57
  have h37 := hOptPk.seq h47
  have h27 := hKpk.seq h37
  exact (hSpk.seq h27).mono
    (p2a_tight_cum_le _ _ _ _)
    (p2a_tight_live_le _)
    (Nat.le_refl _)
    (p2a_tight_maxReq_le _ _)

private theorem p2c_tight_cum_le (cCur cLoop c16 cOver cTail : Nat) :
    cCur + (cLoop + (c16 + (c16 + (c16 + (c16 + (cOver + (c16 + cTail))))))) ≤
      cCur + cLoop + 5 * c16 + cOver + cTail := by
  omega

private theorem p2c_tight_live_le (l16 lOver : Nat) :
    0 + (0 + (l16 + (l16 + (l16 + (l16 + (lOver + l16)))))) ≤ 5 * l16 + lOver := by
  omega

private theorem p2c_tight_maxReq_le (rCurAll rDec rTr rSerAll r16 ikmCap : Nat) :
    max (max rCurAll 192)
      (max (max rDec rTr)
        (max r16 (max r16 (max r16 (max r16
          (max (max rSerAll (max ikmCap 4224)) (max r16 192))))))) ≤
    max (max rCurAll (max rDec rTr))
      (max rSerAll (max r16 (max ikmCap 4224))) := by
  let T := max (max rCurAll (max rDec rTr))
    (max rSerAll (max r16 (max ikmCap 4224)))
  have hL : max rCurAll (max rDec rTr) ≤ T := Nat.le_max_left _ _
  have hR : max rSerAll (max r16 (max ikmCap 4224)) ≤ T := Nat.le_max_right _ _
  have h1 : rCurAll ≤ T := Nat.le_trans (Nat.le_max_left _ _) hL
  have h2 : max rDec rTr ≤ T := Nat.le_trans (Nat.le_max_right _ _) hL
  have h3 : rSerAll ≤ T := Nat.le_trans (Nat.le_max_left _ _) hR
  have h4 : max r16 (max ikmCap 4224) ≤ T := Nat.le_trans (Nat.le_max_right _ _) hR
  have hr16 : r16 ≤ T := Nat.le_trans (Nat.le_max_left _ _) h4
  have hikm : max ikmCap 4224 ≤ T := Nat.le_trans (Nat.le_max_right _ _) h4
  have h192 : 192 ≤ T :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hikm)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨h1, h192⟩,
     Nat.max_le.mpr ⟨h2,
       Nat.max_le.mpr ⟨hr16, Nat.max_le.mpr ⟨hr16, Nat.max_le.mpr ⟨hr16,
         Nat.max_le.mpr ⟨hr16, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨h3, hikm⟩,
           Nat.max_le.mpr ⟨hr16, h192⟩⟩⟩⟩⟩⟩⟩⟩

theorem w4StageP2PathCCli_dom_fine_phaseCredit {α : Type}
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    {CurTrialFailEnv : List AllocEvent → Prop} {curPqCap c_cur p_cur r_cur : Nat}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push archPqCap archEncCap : Nat}
    {l_dec : α → Nat} {xs : List α}
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal smallFileCap : Nat}
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = st_cur ∧ SessionGhostValid G_cur ses_cur ∧
          SessionCloneDom curPqCap ses_cur)
    (hCurTrial : PhaseCreditSpec fineCostModel CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hArchValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses)
    (hArchEnc : (encodeRecord r_arch).length ≤ archEncCap)
    (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec fineCostModel (DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel VecPushEnv c_push 0 0 r_push)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hSmallCap : ∀ d ∈ [spkDir, kpkDir, opkDir, ownDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap) :
    let smCap := max maxVal smallFileCap
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let lOver := fineOptLarge archEncCap
    let pOver := 1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap
    let pRest := max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
      (l16 + max pOver (lOver + max p16 l16)))))
    PhaseCreditSpec fineCostModel
      (W4StageP2PathCCliEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      ((8277456 + c_cur + 8186) + 4 * (c_dec + c_tr) +
        5 * c16 + (8420940 + c_push + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32) + 8186)
      (5 * l16 + lOver)
      (max (1080975 + fineOptLarge curPqCap + p_cur) (max (p_dec + p_tr) pRest))
      (max (max (max (max 208000 curPqCap) r_cur) (max r_dec r_tr))
        (max (max (max (max 208000 archPqCap) archEncCap) r_push)
          (max r16 (max ikmCap 4224)))) := by
  dsimp only
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hCur : PhaseCreditSpec fineCostModel
      (fun e1 => FreeOnlyEvs e1 ∨
        W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
          (· = dropClonedSessionEvents G_cur st_cur) e1)
      (8277456 + c_cur + 8186) 0
      (1080975 + fineOptLarge curPqCap + p_cur)
      (max (max (max 208000 curPqCap) r_cur) 192) :=
    (hFree.or (tryDecryptCloneFail_dom_fine_cancel_phaseCredit hCurDom hCurTrial)).mono
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
  have hLoop : PhaseCreditSpec fineCostModel
      (fun e2 => FreeOnlyEvs e2 ∨
        IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs e2)
      (4 * (c_dec + c_tr)) 0 (p_dec + p_tr) (max r_dec r_tr) :=
    (hFree.or (phaseCredit_archivedTrialLoop_le4 hlen4 hl_le_p hDec hTrial hDrop)).mono
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
  have hSpk := w4KeyIdSmallStoreStep16_fine_phaseCredit spkId hdcSpk hdir
    (fun bs hr => hSmallCap spkDir (by simp) _ bs hr)
  have hKpk := w4KeyIdSmallStoreStep16_fine_phaseCredit kpkId hdcKpk hdir
    (fun bs hr => hSmallCap kpkDir (by simp) _ bs hr)
  have hOptPk := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
      (fun bs hr => hSmallCap opkDir (by simp) _ bs hr)
  have hKp := w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hkeyName
    (fun bs hr => hSmallCap ownDir (by simp) _ bs hr)
  have hSer := serialize_dom_phaseCredit_tight hArchValid hArchEnc
  rw [optLargeCost_fine_eq archPqCap, optLargeCost_fine_eq archEncCap] at hSer
  have hSpqr := w4SpqrInit32_fine_phaseCredit F x_spqr hspqrKey
  have hOver : PhaseCreditSpec fineCostModel
      (W4StageP2OverBobEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv
        x_res hasOpk (InitialStateEnv F x_spqr))
      (8420940 + c_push + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32)
      (fineOptLarge archEncCap)
      (1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap)
      (max (max (max (max 208000 archPqCap) archEncCap) r_push) (max ikmCap 4224)) := by
    have h0 := phaseCredit_w4StageP2OverBob_small fineCostModel_modelHyps (hasOpk := hasOpk)
      hSer hPush hold hnew hSmall hSpqr
    have hle : fineOptLarge archEncCap ≤
        1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap :=
      Nat.le_add_left _ _
    exact h0.mono
      (Nat.le_refl _)
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.max_le.mpr
        ⟨Nat.le_refl _,
         by simp only [Nat.max_self, Nat.add_zero]; exact hle⟩)
      (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans (p2a_bob_maxReq_le ikmCap) (Nat.le_max_right _ _)⟩)
  have hReg := w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hregName
    (fun bs hr => hSmallCap ownDir (by simp) _ bs hr)
  have hTail := w4ErrTail_fine_phaseCredit_tight
  have h89 := (hReg.seq hTail).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
    (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  have h79 := hOver.seq h89
  have h69 := hKp.seq h79
  have h59 := hOptPk.seq h69
  have h49 := hKpk.seq h59
  have h39 := hSpk.seq h49
  have h29 := hLoop.seq h39
  exact (hCur.seq h29).mono
    (p2c_tight_cum_le _ _ _ _ _)
    (p2c_tight_live_le _ _)
    (by simp only [Nat.zero_add]; exact Nat.le_refl _)
    (p2c_tight_maxReq_le _ _ _ _ _ _)

theorem w4StageP3_fine_phaseCredit_tight
    {TryDecEnv : List AllocEvent → Prop} {c l p r : Nat}
    (hTd : PhaseCreditSpec fineCostModel TryDecEnv c l p r) :
    PhaseCreditSpec fineCostModel (W4StageP3Env TryDecEnv)
      (c + 8186) l (max p l) (max r 192) :=
  (hTd.seq w4ErrTail_fine_phaseCredit_tight).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero l))
    (Nat.le_of_eq (congrArg (max p) (Nat.add_zero l))) (Nat.le_refl _)

theorem w4StageP4MatchedCli_dom_fine_phaseCredit
    {rd : ReadRule} {files : FsFiles}
    {peersDir sessDir : DirGhost} {peer : AddrGhost}
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal smallFileCap pqCap encCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hPeersCap : ∀ bs, rd files (pathOf peersDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ smallFileCap)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r_rec).length ≤ encCap) :
    let smCap := max maxVal smallFileCap
    let c32 := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let l32 := smallStorePollTightDeltaLive smCap maxEntries
    let p32 := smallStorePollTightDeltaPeak smCap maxEntries
    let r32 := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
    let lSt0 := sessStorePollTightDeltaLive (fineOptLarge encCap) maxEntries
    let pSt0 := sessStorePollTightDeltaPeak
      (1080975 + fineOptLarge pqCap + fineOptLarge encCap) maxEntries
    let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries)
    PhaseCreditSpec fineCostModel (W4StageP4MatchedCliEnv rd files peersDir sessDir peer g_rec r_rec)
      (c32 + cSt0) (l32 + lSt0) (max p32 (l32 + pSt0)) (max r32 rSt0) := by
  dsimp only
  have hSave := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer hPeersCap
  have hStore := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (w4SessStoreStep_dom_fine_phaseCredit hdcSess hpeer hValid hEnc)
  exact hSave.seq hStore

private theorem p4_maxReq_le (r32 r16 rSt : Nat) :
    max r32 (max r32 (max r16 rSt)) ≤ max (max r32 r32) (max r16 rSt) := by
  have hr32 : r32 ≤ max (max r32 r32) (max r16 rSt) :=
    Nat.le_trans (Nat.le_max_left r32 r32) (Nat.le_max_left _ _)
  exact Nat.max_le.mpr ⟨hr32, Nat.max_le.mpr ⟨hr32, Nat.le_max_right _ _⟩⟩

theorem w4StageP4PathACli_dom_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal smallFileCap pqCap encCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hSmallCap : ∀ d ∈ [peersDir, kpkDir, opkDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r_rec).length ≤ encCap) :
    let smCap := max maxVal smallFileCap
    let c32 := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let l32 := smallStorePollTightDeltaLive smCap maxEntries
    let p32 := smallStorePollTightDeltaPeak smCap maxEntries
    let r32 := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
    let lSt0 := sessStorePollTightDeltaLive (fineOptLarge encCap) maxEntries
    let pSt0 := sessStorePollTightDeltaPeak
      (1080975 + fineOptLarge pqCap + fineOptLarge encCap) maxEntries
    let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP4PathACliEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        g_rec r_rec)
      (c32 + c32 + c16 + cSt0)
      (l32 + l32 + l16 + lSt0)
      (max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt0))))
      (max (max r32 r32) (max r16 rSt0)) := by
  dsimp only
  have hSave := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer
    (fun bs hr => hSmallCap peersDir (by simp) _ bs hr)
  have hMark := w4SmallStoreStep32_fine_phaseCredit hdcKpk hdir hkpkName
    (fun bs hr => hSmallCap kpkDir (by simp) _ bs hr)
  have hRem := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
      (fun bs hr => hSmallCap opkDir (by simp) _ bs hr)
  have hStore := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (w4SessStoreStep_dom_fine_phaseCredit hdcSess hpeer hValid hEnc)
  have h34 := hRem.seq hStore
  have h24 := hMark.seq h34
  exact (hSave.seq h24).mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _)
    (p4_maxReq_le _ _ _)

theorem w4StageP4PathCCli_freshBob_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    {maxDir maxEntries maxVal smallFileCap bobPqCap prevEncCap totalPrev1Cap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hSmallCap : ∀ d ∈ [peersDir, kpkDir, opkDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G sess enc) :
    let smCap := max maxVal smallFileCap
    let c32 := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let l32 := smallStorePollTightDeltaLive smCap maxEntries
    let p32 := smallStorePollTightDeltaPeak smCap maxEntries
    let r32 := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt1 := 738 + sessStorePollTightDeltaCum 1184912 maxEntries
    let lSt1 := sessStorePollTightDeltaLive (fineOptLarge totalPrev1Cap) maxEntries
    let pSt1 := sessStorePollTightDeltaPeak
      (fineOptLarge bobPqCap + fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap) maxEntries
    let rSt1 := max 32
      (sessStorePollMaxReq
        (max (max 208000 bobPqCap) (max (max 24 prevEncCap) totalPrev1Cap)) maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP4PathCCliEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        G sess enc)
      (c32 + c32 + c16 + cSt1)
      (l32 + l32 + l16 + lSt1)
      (max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt1))))
      (max (max r32 r32) (max r16 rSt1)) := by
  dsimp only
  have hSave := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer
    (fun bs hr => hSmallCap peersDir (by simp) _ bs hr)
  have hMark := w4SmallStoreStep32_fine_phaseCredit hdcKpk hdir hkpkName
    (fun bs hr => hSmallCap kpkDir (by simp) _ bs hr)
  have hRem := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
      (fun bs hr => hSmallCap opkDir (by simp) _ bs hr)
  have hStore := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (w4SessStorePrev1Step_freshBob_fine_phaseCredit hdcSess hpeer hbob)
  have h34 := hRem.seq hStore
  have h24 := hMark.seq h34
  exact (hSave.seq h24).mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _)
    (p4_maxReq_le _ _ _)

/-! ## Closed-Form Tight Slot Formulas & `W4DecryptPrekeySplitSlotEnv` -/

/-- Split-arm `decrypt_prekey` slot envelope allowing Path A and Path C (fresh Bob responder
sessions) to carry a sharper Stage P3 `TryDecAC` envelope than Path B (`TryDecEnv`).
At `TryDecAC := P.TryDecEnv`, `W4DecryptPrekeySplitSlotEnv P P.TryDecEnv = W4DecryptPrekeySlotEnv P`
definitionally (`rfl`). -/
@[expose] def W4DecryptPrekeySplitSlotEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (TryDecAC : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
      W4DecryptPrekeyPathBEnv P e ∨
      W4DecryptPrekeyPathAEnv ({ P with TryDecEnv := TryDecAC }) e ∨
      W4DecryptPrekeyPathCEnv ({ P with TryDecEnv := TryDecAC }) e)
    FreeOnlyEvs evs

theorem w4DecryptPrekeySplitSlotEnv_self {α : Type} (P : W4DecryptPrekeySlotParams α) :
    W4DecryptPrekeySplitSlotEnv P P.TryDecEnv = W4DecryptPrekeySlotEnv P :=
  rfl

/-- Domain bundle for `W4DecryptPrekeySplitSlotEnv` and `W4DecryptPrekeySlotEnv`. -/
structure W4DecryptPrekeyTightDom {α : Type} (P : W4DecryptPrekeySlotParams α)
    (sessFileCap smallFileCap curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap : Nat) : Prop where
  peer_len : P.peer.name.bytes.length ≤ 40
  ownKey_len : P.ownKeyName.length ≤ 64
  ownReg_len : P.ownRegName.length ≤ 64
  kpkMark_len : P.kpkMarkName.length ≤ 64
  res_old : P.x_res.cap.toNat ≤ ikmCap
  res_new : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap
  ikm_small : max ikmCap 1569 ≤ 135167
  spqr_key : P.x_spqr.p.authKey.length ≤ 32
  sess_cap : ∀ bs, P.rd P.files (pathOf P.sessDir.path (addressText P.peer.val)) = .ok bs →
    bs.length ≤ sessFileCap
  small_cap : ∀ d ∈ [P.ownDir, P.peersDir, P.spkDir, P.kpkDir, P.opkDir],
    ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap
  cur_dom : (∀ evs, ¬ P.CurTrialFailEnv evs) ∨
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = P.st_cur ∧ SessionGhostValid P.G_cur ses_cur ∧
        SessionCloneDom curPqCap ses_cur
  arch_valid : ∀ G ses, P.g_arch.cur = some G → P.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses
  arch_enc : (encodeRecord P.r_arch).length ≤ archEncCap
  out0_valid : ∀ G ses, P.g_out0.cur = some G → P.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom out0PqCap ses
  out0_enc : (encodeRecord P.r_out0).length ≤ out0EncCap
  out1_freshBob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap P.G_out1 P.sess_out1 P.enc_prev1
  trials_len4 : P.archivedTrials.length ≤ 4

/-- Closed `Nat` tight `Δcum` bound across all four arms of `W4DecryptPrekeySplitSlotEnv`
(taking `max` of Untrusted, Path B, Path A, and Path C). -/
@[expose] def w4DecryptPrekeySplitTightCum
    (sessCap smallCap maxEntries deserCum c_cur c_dec c_tr c_push
     c_tdB c_tdAC ikmCap : Nat) : Nat :=
  let cL := 488 + sessLoadPollTightDeltaCum sessCap deserCum
  let c32 := 738 + smallStorePollTightDeltaCum smallCap maxEntries
  let c16 := 488 + smallStorePollTightDeltaCum smallCap maxEntries
  let cP1Ok := cL + c32
  let cUntr := cP1Ok + 9619
  let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
  let cSt1 := 738 + sessStorePollTightDeltaCum 1184912 maxEntries
  let cPathB := cP1Ok + (4 * (c_dec + c_tr) + (8420940 + c_push)) +
    (c_tdB + 8186) + (c32 + cSt0)
  let cPathA := cP1Ok + (5 * c16 + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32 + 8186) +
    (c_tdAC + 8186) + (c32 + c32 + c16 + cSt0)
  let cPathC := cP1Ok +
    ((8277456 + c_cur + 8186) + 4 * (c_dec + c_tr) +
      5 * c16 + (8420940 + c_push + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32) + 8186) +
    (c_tdAC + 8186) + (c32 + c32 + c16 + cSt1)
  max (max cUntr cPathB) (max cPathA cPathC)

/-- Pure closed-`Nat` tight `Δlive` bound across all 4 arms of `W4DecryptPrekeySplitSlotEnv`. -/
@[expose] def w4DecryptPrekeySplitTightLive
    (sessCap smallCap maxEntries deserLive archEncCap out0EncCap totalPrev1Cap
     l_tdB l_tdAC : Nat) : Nat :=
  let lL := sessLoadPollTightDeltaLive sessCap deserLive
  let l32 := smallStorePollTightDeltaLive smallCap maxEntries
  let l16 := smallStorePollTightDeltaLive smallCap maxEntries
  let lP1 := lL + l32
  let lSt0 := sessStorePollTightDeltaLive (fineOptLarge out0EncCap) maxEntries
  let lSt1 := sessStorePollTightDeltaLive (fineOptLarge totalPrev1Cap) maxEntries
  let lUntr := lP1
  let lPathB := lP1 + fineOptLarge archEncCap + l_tdB + (l32 + lSt0)
  let lPathA := lP1 + 5 * l16 + l_tdAC + (l32 + l32 + l16 + lSt0)
  let lPathC := lP1 + (5 * l16 + fineOptLarge archEncCap) + l_tdAC + (l32 + l32 + l16 + lSt1)
  max (max lUntr lPathB) (max lPathA lPathC)

/-- Pure closed-`Nat` sequential `Δpeak` bound before clamping with `Δlive`. -/
@[expose] def w4DecryptPrekeySplitTightRawPeak
    (sessCap smallCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC : Nat) : Nat :=
  let lL := sessLoadPollTightDeltaLive sessCap deserLive
  let pL := sessLoadPollTightDeltaPeak sessCap deserPeak
  let l32 := smallStorePollTightDeltaLive smallCap maxEntries
  let p32 := smallStorePollTightDeltaPeak smallCap maxEntries
  let l16 := smallStorePollTightDeltaLive smallCap maxEntries
  let p16 := smallStorePollTightDeltaPeak smallCap maxEntries
  let lP1 := lL + l32
  let pP1 := max pL (lL + max p32 l32)
  let pSt0 := sessStorePollTightDeltaPeak
    (1080975 + fineOptLarge out0PqCap + fineOptLarge out0EncCap) maxEntries
  let pSt1 := sessStorePollTightDeltaPeak
    (fineOptLarge bobPqCap + fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap) maxEntries
  let pOver := 1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap
  let lOver := fineOptLarge archEncCap
  let pPeakB :=
    let pP2B := max (p_dec + p_tr) pOver
    let pP3B := max p_tdB l_tdB
    let pP4B := max p32 (l32 + pSt0)
    max pP1 (lP1 + max pP2B (lOver + max pP3B (l_tdB + pP4B)))
  let pPeakA :=
    let pP2A := max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16 l16))))
    let pP3A := max p_tdAC l_tdAC
    let pP4A := max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt0)))
    max pP1 (lP1 + max pP2A (5 * l16 + max pP3A (l_tdAC + pP4A)))
  let pPeakC :=
    let pP2Store := max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
      (l16 + max pOver (lOver + max p16 l16)))))
    let pP2C := max (1080975 + fineOptLarge curPqCap + p_cur) (max (p_dec + p_tr) pP2Store)
    let pP3C := max p_tdAC l_tdAC
    let pP4C := max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt1)))
    max pP1 (lP1 + max pP2C ((5 * l16 + lOver) + max pP3C (l_tdAC + pP4C)))
  max (max pP1 pPeakB) (max pPeakA pPeakC)

/-- Closed `Nat` tight `Δpeak` bound (`max rawPeak live` so `live ≤ peak` holds by
`Nat.le_max_right`). -/
@[expose] def w4DecryptPrekeySplitTightPeak
    (sessCap smallCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC : Nat) : Nat :=
  max
    (w4DecryptPrekeySplitTightRawPeak sessCap smallCap maxEntries deserLive deserPeak
      curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
      p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC)
    (w4DecryptPrekeySplitTightLive sessCap smallCap maxEntries deserLive
      archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC)

/-- Pure closed-`Nat` tight `maxReq` bound across all 4 arms of `W4DecryptPrekeySplitSlotEnv`. -/
@[expose] def w4DecryptPrekeySplitTightMaxReq
    (sessCap smallCap maxEntries deserMaxReq
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     r_cur r_dec r_tr r_push r_tdB r_tdAC ikmCap : Nat) : Nat :=
  let rL := max 24 (sessLoadPollTightMaxReq sessCap deserMaxReq)
  let r32 := max 32 (smallStorePollTightMaxReq smallCap maxEntries)
  let r16 := max 16 (smallStorePollTightMaxReq smallCap maxEntries)
  let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 out0PqCap) out0EncCap) maxEntries)
  let rSt1 := max 32
    (sessStorePollMaxReq
      (max (max 208000 bobPqCap) (max (max 24 prevEncCap) totalPrev1Cap)) maxEntries)
  max (max rL (max r32 (max r16 40)))
    (max (max (max (max 208000 curPqCap) r_cur) (max r_dec r_tr))
      (max (max (max (max 208000 archPqCap) archEncCap) r_push)
        (max (max (max r_tdB r_tdAC) 192) (max (max ikmCap 4224) (max rSt0 rSt1)))))

theorem w4DecryptPrekeySplitTight_live_le_peak
    (sessCap smallCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC : Nat) :
    w4DecryptPrekeySplitTightLive sessCap smallCap maxEntries deserLive
        archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC ≤
      w4DecryptPrekeySplitTightPeak sessCap smallCap maxEntries deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC :=
  Nat.le_max_right _ _

/-! ## End-to-End Tight `PhaseCreditSpec`, `FitsEnv`, & `W4SlotR3bEnv` Theorems -/

private theorem splitMaxReq_untr_le (rL r32 r16 rRest : Nat) :
    max rL (max r32 40) ≤ max (max rL (max r32 (max r16 40))) rRest := by
  let T := max (max rL (max r32 (max r16 40))) rRest
  have hA : max rL (max r32 (max r16 40)) ≤ T := Nat.le_max_left _ _
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have h40 : 40 ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hA))
  exact Nat.max_le.mpr ⟨hrL, Nat.max_le.mpr ⟨hr32, h40⟩⟩

private theorem splitMaxReq_B_le
    (rL r32 r16 rCur r_dec r_tr rArch r_tdB r_tdAC rIkm rSt0 rSt1 : Nat) :
    max (max rL r32)
      (max (max (max r_dec r_tr) rArch)
        (max (max r_tdB 192) (max r32 rSt0))) ≤
    max (max rL (max r32 (max r16 40)))
      (max (max rCur (max r_dec r_tr))
        (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1))))) := by
  let T := max (max rL (max r32 (max r16 40)))
    (max (max rCur (max r_dec r_tr))
      (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hA : max rL (max r32 (max r16 40)) ≤ T := Nat.le_max_left _ _
  have hB : max (max rCur (max r_dec r_tr))
      (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))) ≤ T :=
    Nat.le_max_right _ _
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hdt : max r_dec r_tr ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) hB)
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hArch : rArch ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBR
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have htdAll : max (max r_tdB r_tdAC) 192 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have htdB : max r_tdB 192 ≤ T :=
    Nat.le_trans (max_mono (Nat.le_max_left r_tdB r_tdAC) (Nat.le_refl 192)) htdAll
  have hrSt0 : rSt0 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRR))
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32⟩,
     Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hdt, hArch⟩,
       Nat.max_le.mpr ⟨htdB, Nat.max_le.mpr ⟨hr32, hrSt0⟩⟩⟩⟩

private theorem splitMaxReq_A_le
    (rL r32 r16 rCurDt rArch r_tdB r_tdAC rIkm rSt0 rSt1 : Nat) :
    max (max rL r32)
      (max (max r16 rIkm)
        (max (max r_tdAC 192) (max (max r32 r32) (max r16 rSt0)))) ≤
    max (max rL (max r32 (max r16 40)))
      (max rCurDt
        (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1))))) := by
  let T := max (max rL (max r32 (max r16 40)))
    (max rCurDt
      (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hA : max rL (max r32 (max r16 40)) ≤ T := Nat.le_max_left _ _
  have hB := Nat.le_max_right (max rL (max r32 (max r16 40)))
    (max rCurDt (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hr16 : r16 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hA))
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have htdAll : max (max r_tdB r_tdAC) 192 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have htdAC : max r_tdAC 192 ≤ T :=
    Nat.le_trans (max_mono (Nat.le_max_right r_tdB r_tdAC) (Nat.le_refl 192)) htdAll
  have hBRRR := Nat.le_trans (Nat.le_max_right _ _) hBRR
  have hrIkm : rIkm ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRRR
  have hrSt0 : rSt0 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRRR)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32⟩,
     Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr16, hrIkm⟩,
       Nat.max_le.mpr ⟨htdAC,
         Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr32, hr32⟩, Nat.max_le.mpr ⟨hr16, hrSt0⟩⟩⟩⟩⟩

private theorem splitMaxReq_C_le
    (rL r32 r16 rCurDt rArch r_tdB r_tdAC rIkm rSt0 rSt1 : Nat) :
    max (max rL r32)
      (max (max rCurDt (max rArch (max r16 rIkm)))
        (max (max r_tdAC 192) (max (max r32 r32) (max r16 rSt1)))) ≤
    max (max rL (max r32 (max r16 40)))
      (max rCurDt
        (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1))))) := by
  let T := max (max rL (max r32 (max r16 40)))
    (max rCurDt
      (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hA : max rL (max r32 (max r16 40)) ≤ T := Nat.le_max_left _ _
  have hB := Nat.le_max_right (max rL (max r32 (max r16 40)))
    (max rCurDt (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hr16 : r16 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hA))
  have hCur : rCurDt ≤ T := Nat.le_trans (Nat.le_max_left _ _) hB
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hArch : rArch ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBR
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have htdAll : max (max r_tdB r_tdAC) 192 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have htdAC : max r_tdAC 192 ≤ T :=
    Nat.le_trans (max_mono (Nat.le_max_right r_tdB r_tdAC) (Nat.le_refl 192)) htdAll
  have hBRRR := Nat.le_trans (Nat.le_max_right _ _) hBRR
  have hrIkm : rIkm ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRRR
  have hrSt1 : rSt1 ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRRR)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32⟩,
     Nat.max_le.mpr
       ⟨Nat.max_le.mpr ⟨hCur, Nat.max_le.mpr ⟨hArch, Nat.max_le.mpr ⟨hr16, hrIkm⟩⟩⟩,
        Nat.max_le.mpr ⟨htdAC,
          Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr32, hr32⟩, Nat.max_le.mpr ⟨hr16, hrSt1⟩⟩⟩⟩⟩

/-- Tight `PhaseCreditSpec fineCostModel` for `W4DecryptPrekeySplitSlotEnv P TryDecAC` combining
tight clone/serialize/store bounds, `FreshBobPrev1Dom`, `w4SpqrInit32_fine_phaseCredit`
(`Δlive = 0, Δpeak = 0`), separate `(sessFileCap, smallFileCap)` store caps, and split Stage P3
(`TryDecEnv` vs `TryDecAC`) credits. -/
theorem w4DecryptPrekeySplitSlot_fine_phaseCredit {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {TryDecAC : List AllocEvent → Prop}
    {maxDir maxEntries maxVal sessFileCap smallFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_tdB l_tdB p_tdB r_tdB c_tdAC l_tdAC p_tdAC r_tdAC : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hDom : W4DecryptPrekeyTightDom P sessFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv c_tdB l_tdB p_tdB r_tdB)
    (hTdAC : PhaseCreditSpec fineCostModel TryDecAC c_tdAC l_tdAC p_tdAC r_tdAC) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    PhaseCreditSpec fineCostModel (W4DecryptPrekeySplitSlotEnv P TryDecAC)
      (w4DecryptPrekeySplitTightCum sCap smCap maxEntries deserCum
        c_cur c_dec c_tr c_push c_tdB c_tdAC ikmCap)
      (w4DecryptPrekeySplitTightLive sCap smCap maxEntries deserLive
        archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC)
      (w4DecryptPrekeySplitTightPeak sCap smCap maxEntries deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC)
      (w4DecryptPrekeySplitTightMaxReq sCap smCap maxEntries deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_tdB r_tdAC ikmCap) := by
  dsimp only
  set sCap := max maxVal sessFileCap
  set smCap := max maxVal smallFileCap
  have hPeersCap : ∀ bs, P.rd P.files (pathOf P.peersDir.path (addressText P.peer.val)) = .ok bs →
      bs.length ≤ smallFileCap :=
    fun bs hr => hDom.small_cap P.peersDir (by simp) _ bs hr
  have hSmallP2 : ∀ d ∈ [P.spkDir, P.kpkDir, P.opkDir, P.ownDir],
      ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap := by
    intro d hd n bs hr
    rcases List.mem_cons.mp hd with rfl | hd1
    · exact hDom.small_cap P.spkDir (by simp) n bs hr
    · rcases List.mem_cons.mp hd1 with rfl | hd2
      · exact hDom.small_cap P.kpkDir (by simp) n bs hr
      · rcases List.mem_cons.mp hd2 with rfl | hd3
        · exact hDom.small_cap P.opkDir (by simp) n bs hr
        · rcases List.mem_cons.mp hd3 with rfl | hd4
          · exact hDom.small_cap P.ownDir (by simp) n bs hr
          · nomatch hd4
  have hSmallP4 : ∀ d ∈ [P.peersDir, P.kpkDir, P.opkDir],
      ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap := by
    intro d hd n bs hr
    rcases List.mem_cons.mp hd with rfl | hd1
    · exact hDom.small_cap P.peersDir (by simp) n bs hr
    · rcases List.mem_cons.mp hd1 with rfl | hd2
      · exact hDom.small_cap P.kpkDir (by simp) n bs hr
      · rcases List.mem_cons.mp hd2 with rfl | hd3
        · exact hDom.small_cap P.opkDir (by simp) n bs hr
        · nomatch hd3
  have hIkmSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact hDom.ikm_small
  -- Target bounds across all 4 arms:
  set cTot := w4DecryptPrekeySplitTightCum sCap smCap maxEntries deserCum
    c_cur c_dec c_tr c_push c_tdB c_tdAC ikmCap
  set lTot := w4DecryptPrekeySplitTightLive sCap smCap maxEntries deserLive
    archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC
  set rpTot := w4DecryptPrekeySplitTightRawPeak sCap smCap maxEntries deserLive deserPeak
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC
  set rTot := w4DecryptPrekeySplitTightMaxReq sCap smCap maxEntries deserMaxReq
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    r_cur r_dec r_tr r_push r_tdB r_tdAC ikmCap
  -- Arm 1: Untrusted
  have hUntr0 := w4StageP1UntrustedCli_fine_phaseCredit hdcSess hdcPeers hdir
    hDom.peer_len hDom.sess_cap hPeersCap hdeser
  have hUntr : PhaseCreditSpec fineCostModel
      (W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      cTot lTot rpTot rTot := hUntr0.mono
    (by dsimp only [cTot, w4DecryptPrekeySplitTightCum]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (by dsimp only [lTot, w4DecryptPrekeySplitTightLive]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (by dsimp only [rpTot, w4DecryptPrekeySplitTightRawPeak]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (by dsimp only [rTot, w4DecryptPrekeySplitTightMaxReq]
        exact splitMaxReq_untr_le _ _ _ _)
  -- Arm 2: Path B
  have hP1Ok := w4StageP1OkCli_fine_phaseCredit hdcSess hdcPeers hdir
    hDom.peer_len hDom.sess_cap hPeersCap hdeser
  have hP2B := w4StageP2Matched_dom_fine_phaseCredit P.g_arch P.r_arch
    hDom.arch_valid hDom.arch_enc hDom.trials_len4 hl_le_p hDec hTrial hDrop hPush
  have hP3B := w4StageP3_fine_phaseCredit_tight hTdB
  have hP4B := w4StageP4MatchedCli_dom_fine_phaseCredit P.g_out0 P.r_out0
    hdcPeers hdcSess hdir hDom.peer_len hPeersCap hDom.out0_valid hDom.out0_enc
  have hPathB : PhaseCreditSpec fineCostModel (W4DecryptPrekeyPathBEnv P)
      cTot lTot rpTot rTot := (hP1Ok.seq (hP2B.seq (hP3B.seq hP4B))).mono
    (by
      dsimp only [cTot, w4DecryptPrekeySplitTightCum]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [lTot, w4DecryptPrekeySplitTightLive]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [rpTot, w4DecryptPrekeySplitTightRawPeak]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      exact fourStagePeak_mono
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (by dsimp only [rTot, w4DecryptPrekeySplitTightMaxReq]
        exact splitMaxReq_B_le _ _ _ _ _ _ _ _ _ _ _ _)
  -- Arm 3: Path A (with TryDecAC)
  have hP2A := w4StageP2PathACli_fine_phaseCredit P.hasOpk P.spkId P.kpkId P.opkId
    P.F P.x_spqr hdcSpk hdcKpk hdcOpk hdcOwn hdir hDom.ownKey_len hDom.ownReg_len
    hDom.res_old hDom.res_new hIkmSmall hDom.spqr_key hSmallP2
  have hP3AC := w4StageP3_fine_phaseCredit_tight hTdAC
  have hP4A := w4StageP4PathACli_dom_fine_phaseCredit P.hasOpk P.opkId P.g_out0 P.r_out0
    hdcPeers hdcKpk hdcOpk hdcSess hdir hDom.peer_len hDom.kpkMark_len hSmallP4
    hDom.out0_valid hDom.out0_enc
  have hPathA : PhaseCreditSpec fineCostModel
      (W4DecryptPrekeyPathAEnv ({ P with TryDecEnv := TryDecAC }))
      cTot lTot rpTot rTot := (hP1Ok.seq (hP2A.seq (hP3AC.seq hP4A))).mono
    (by
      dsimp only [cTot, w4DecryptPrekeySplitTightCum]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [lTot, w4DecryptPrekeySplitTightLive]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [rpTot, w4DecryptPrekeySplitTightRawPeak]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      have h0eq : max 0 (0 + max (smallStorePollTightDeltaPeak smCap maxEntries)
          (smallStorePollTightDeltaLive smCap maxEntries)) ≤
          max (smallStorePollTightDeltaPeak smCap maxEntries)
            (smallStorePollTightDeltaLive smCap maxEntries) := by
        simp only [Nat.zero_add, Nat.zero_max]
        exact Nat.le_refl _
      exact fourStagePeak_mono
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
        (Nat.le_refl _)
        (fiveStepPeak_mono h0eq)
        (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (by dsimp only [rTot, w4DecryptPrekeySplitTightMaxReq]
        exact splitMaxReq_A_le _ _ _ _ _ _ _ _ _ _)
  -- Arm 4: Path C (with TryDecAC + FreshBobPrev1Dom)
  have hP2C := w4StageP2PathCCli_dom_fine_phaseCredit P.G_cur P.st_cur P.g_arch P.r_arch
    P.hasOpk P.spkId P.kpkId P.opkId P.F P.x_spqr hDom.cur_dom hCurTrial
    hDom.arch_valid hDom.arch_enc hDom.trials_len4 hl_le_p hDec hTrial hDrop hPush
    hdcSpk hdcKpk hdcOpk hdcOwn hdir hDom.ownKey_len hDom.ownReg_len
    hDom.res_old hDom.res_new hIkmSmall hDom.spqr_key hSmallP2
  have hP4C := w4StageP4PathCCli_freshBob_fine_phaseCredit P.hasOpk P.opkId
    P.G_out1 P.sess_out1 P.enc_prev1 hdcPeers hdcKpk hdcOpk hdcSess hdir
    hDom.peer_len hDom.kpkMark_len hSmallP4 hDom.out1_freshBob
  have hPathC : PhaseCreditSpec fineCostModel
      (W4DecryptPrekeyPathCEnv ({ P with TryDecEnv := TryDecAC }))
      cTot lTot rpTot rTot := (hP1Ok.seq (hP2C.seq (hP3AC.seq hP4C))).mono
    (by
      dsimp only [cTot, w4DecryptPrekeySplitTightCum]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [lTot, w4DecryptPrekeySplitTightLive]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [rpTot, w4DecryptPrekeySplitTightRawPeak]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      exact fourStagePeak_mono
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (by dsimp only [rTot, w4DecryptPrekeySplitTightMaxReq]
        exact splitMaxReq_C_le _ _ _ _ _ _ _ _ _ _)
  have h4 := phaseCreditSpec_or4 (fun _ h => h) hUntr hPathB hPathA hPathC
  have hSeq := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps h4
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  exact (hFree.or hSeq).mono
    (zero_or_max4_le cTot)
    (zero_or_max4_le lTot)
    (slot_final_peak_le rpTot lTot)
    (zero_or_max4_le rTot)

/-- `StoresGhost.opened` (`maxDir = 26 ≤ 64`, `maxEntries = 0`, `maxVal = 0`) specialization of
`w4DecryptPrekeySplitSlot_fine_phaseCredit`. -/
theorem w4DecryptPrekeySplitSlot_opened_fine_phaseCredit {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {TryDecAC : List AllocEvent → Prop}
    {sessFileCap smallFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_tdB l_tdB p_tdB r_tdB c_tdAC l_tdAC p_tdAC r_tdAC : Nat}
    {l_dec : α → Nat}
    (hOwn : P.ownDir = StoresGhost.opened.identity.own)
    (hPeers : P.peersDir = StoresGhost.opened.identity.peers)
    (hSpk : P.spkDir = StoresGhost.opened.signed)
    (hKpk : P.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            P.kpkDir = StoresGhost.opened.kyber.lastResort)
    (hOpk : P.opkDir = StoresGhost.opened.oneTime)
    (hSess : P.sessDir = StoresGhost.opened.sessions)
    (hDom : W4DecryptPrekeyTightDom P sessFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv c_tdB l_tdB p_tdB r_tdB)
    (hTdAC : PhaseCreditSpec fineCostModel TryDecAC c_tdAC l_tdAC p_tdAC r_tdAC) :
    PhaseCreditSpec fineCostModel (W4DecryptPrekeySplitSlotEnv P TryDecAC)
      (w4DecryptPrekeySplitTightCum sessFileCap smallFileCap 0 deserCum
        c_cur c_dec c_tr c_push c_tdB c_tdAC ikmCap)
      (w4DecryptPrekeySplitTightLive sessFileCap smallFileCap 0 deserLive
        archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC)
      (w4DecryptPrekeySplitTightPeak sessFileCap smallFileCap 0 deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC)
      (w4DecryptPrekeySplitTightMaxReq sessFileCap smallFileCap 0 deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_tdB r_tdAC ikmCap) := by
  obtain ⟨hdcOwn0, hdcPeers0, hdcSpk0, hdcKot0, hdcKlr0, hdcOpk0, hdcSess0⟩ :=
    opened_all_dirDomainCaps
  have hdcOwn : DirDomainCaps 26 0 0 P.ownDir := hOwn ▸ hdcOwn0
  have hdcPeers : DirDomainCaps 26 0 0 P.peersDir := hPeers ▸ hdcPeers0
  have hdcSpk : DirDomainCaps 26 0 0 P.spkDir := hSpk ▸ hdcSpk0
  have hdcKpk : DirDomainCaps 26 0 0 P.kpkDir := by
    rcases hKpk with h1 | h2
    · exact h1 ▸ hdcKot0
    · exact h2 ▸ hdcKlr0
  have hdcOpk : DirDomainCaps 26 0 0 P.opkDir := hOpk ▸ hdcOpk0
  have hdcSess : DirDomainCaps 26 0 0 P.sessDir := hSess ▸ hdcSess0
  have h := w4DecryptPrekeySplitSlot_fine_phaseCredit P
    hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk hdcSess (by decide)
    hDom hdeser hCurTrial hl_le_p hDec hTrial hDrop hPush hTdB hTdAC
  simpa only [Nat.zero_max] using h

export LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fitsEnv_fineCostModel_of_phaseCredit)
export LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (w4SlotR3b_live_le_peak)

/-! ## Widened Binary-Complete Tight `fineCostModel` `PhaseCreditSpec`s

Tight `PhaseCreditSpec fineCostModel` bounds for the widened Stage P2, P3, P4, and 4-arm slot
envelopes in `W4OuterPeakSpec` (`W4DecryptPrekeySplitWideSlotEnv`), supporting both per-directory
`(smallFileCap, kpkFileCap)` caps and uniform `smallFileCap` (`kpkFileCap := smallFileCap`), while
splitting Stage P3 `SegCloneEnv` between `CloneB` (Path B) and `CloneAC` (Paths A & C, `0` live /
`0` peak under `FreshBobCloneDom bobPqCap` with `bobPqCap ≤ 16,384`). -/

section WidenedBinaryCompleteTightSpecs

/-! ### Widened Error Tail, Path B Match/Mismatch Prefix, & Failed-Trial Bounds -/

theorem w4ErrTailWide_fine_phaseCredit_tight :
    PhaseCreditSpec fineCostModel W4ErrTailWideEnv 8674 0 0 192 :=
  (w4ErrTail_fine_phaseCredit_tight.or
    (phaseCreditSpec_fromFEnv_fine_488.or phaseCreditSpec_fromMEnv_fine_8674)).mono
    (by decide) (by decide) (by decide) (by decide)

theorem w4StageP2MatchedErrStr_fine_phaseCredit :
    PhaseCreditSpec fineCostModel W4StageP2MatchedErrStrEnv 1607 0 0 70 := by
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have ha70 := (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 70) (al := 1)
    (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by change fineSmallAllocCost 70 ≤ 1607; decide)
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 70)
  have h70 := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps ha70
  have ha14 := (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 14) (al := 1)
    (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by change fineSmallAllocCost 14 ≤ 1607; decide)
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 14)
  have h14 := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps ha14
  exact (hFree.or (h70.or h14)).mono (by decide) (by decide) (by decide) (by decide)

theorem w4StageP2MatchedCheck_fine_phaseCredit :
    PhaseCreditSpec fineCostModel W4StageP2MatchedCheckEnv 2345 0 0 70 := by
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have ha33 := (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 33) (al := 1)
    (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by change fineSmallAllocCost 33 ≤ 738; decide)
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)
  have hd33 := PhaseCreditSpec.rustDealloc_align16 fineCostModel (req := 33) (al := 1) (by decide)
  have hSeq := ha33.seq (hd33.seq w4StageP2MatchedErrStr_fine_phaseCredit)
  exact (hFree.or hSeq).mono (by decide) (by decide) (by decide) (by decide)

theorem sessionClone_dom_fine_phaseCredit_tight {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseCreditSpec fineCostModel (SegCloneEnv G ses.state)
      8277456
      (1080975 + fineOptLarge pqCap)
      (1080975 + fineOptLarge pqCap)
      (max 208000 pqCap) := by
  have h := sessionClone_dom_phaseCredit_tight hgv hdom
  rwa [optLargeCost_fine_eq pqCap] at h

theorem w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit
    {curPqCap c_cur p_cur r_cur : Nat}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop}
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = st_cur ∧ SessionGhostValid G_cur ses_cur ∧
          SessionCloneDom curPqCap ses_cur)
    (hCurTrial : PhaseCreditSpec fineCostModel CurTrialFailEnv c_cur 0 p_cur r_cur) :
    PhaseCreditSpec fineCostModel
      (W4TryDecryptCloneFailWideEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
        (· = dropClonedSessionEvents G_cur st_cur))
      (8277456 + c_cur + 8674)
      0
      (1080975 + fineOptLarge curPqCap + p_cur)
      (max (max (max 208000 curPqCap) r_cur) 192) := by
  rcases hCurDom with hNo | ⟨ses_cur, hst_eq, hgv, hdom⟩
  · refine (PhaseCreditSpec.empty fineCostModel).congr_mono ?_
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    intro evs hE
    rcases hE with h1 | ⟨a, _, _, h1, _⟩
    · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
      exact hNo e2 htf
    · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
      exact hNo e2 htf
  · subst hst_eq
    have hCancel := sessionClone_drop_cancel_dom_phaseCredit_tight hgv hdom hCurTrial
    rw [optLargeCost_fine_eq curPqCap] at hCancel
    exact (hCancel.seq w4ErrTailWide_fine_phaseCredit_tight).mono
      (Nat.le_refl _)
      (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)
      (Nat.le_refl _)

/-! ### Widened Stage P2 (`Matched`, `InitBob`, `OverBob`, `PathA`, `PathC`) Bounds -/

private theorem p2a_split_cum_le (cs ck b1 b2 c : Nat) :
    cs + (ck + (cs + (cs + ((b1 + b2) + (cs + c))))) ≤ (4 * cs + ck) + b1 + b2 + c := by
  omega

private theorem p2a_split_live_le (ls lk : Nat) :
    ls + (lk + (ls + (ls + ls))) ≤ 4 * ls + lk := by
  omega

private theorem p2a_split_maxReq_le (rs rk ikmCap : Nat) :
    max rs (max rk (max rs (max rs (max (max ikmCap 4224) (max rs 192))))) ≤
      max (max rs rk) (max ikmCap 4224) := by
  let T := max (max rs rk) (max ikmCap 4224)
  have hsm : max rs rk ≤ T := Nat.le_max_left _ _
  have hrs : rs ≤ T := Nat.le_trans (Nat.le_max_left _ _) hsm
  have hrk : rk ≤ T := Nat.le_trans (Nat.le_max_right _ _) hsm
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
  have hsm : max rs rk ≤ T := Nat.le_trans (Nat.le_max_left _ _) h4
  have hrs : rs ≤ T := Nat.le_trans (Nat.le_max_left _ _) hsm
  have hrk : rk ≤ T := Nat.le_trans (Nat.le_max_right _ _) hsm
  have hikm : max ikmCap 4224 ≤ T := Nat.le_trans (Nat.le_max_right _ _) h4
  have h192 : 192 ≤ T :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hikm)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨h1, h192⟩,
     Nat.max_le.mpr ⟨h2,
       Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨hrk, Nat.max_le.mpr ⟨hrs,
         Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨h3, hikm⟩,
           Nat.max_le.mpr ⟨hrs, h192⟩⟩⟩⟩⟩⟩⟩⟩

/-! ### Widened Stage P3 (`CloneEnv → OptStageEnv TryDecEnv → W4ErrTailWideEnv`) Bounds -/

theorem w4StageP3Wide_fine_phaseCredit_tight
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {c_cl l_cl p_cl r_cl c_td l_td p_td r_td : Nat}
    (hClone : PhaseCreditSpec fineCostModel CloneEnv c_cl l_cl p_cl r_cl)
    (hTd : PhaseCreditSpec fineCostModel TryDecEnv c_td l_td p_td r_td) :
    PhaseCreditSpec fineCostModel (W4StageP3WideEnv CloneEnv TryDecEnv)
      (c_cl + c_td + 8674)
      (l_cl + l_td)
      (max p_cl (l_cl + max p_td l_td))
      (max r_cl (max r_td 192)) := by
  have hOptTd := phaseCredit_optStageEnv fineCostModel_modelHyps hTd
  have hTdTail := (hOptTd.seq w4ErrTailWide_fine_phaseCredit_tight).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero l_td))
    (Nat.le_of_eq (congrArg (max p_td) (Nat.add_zero l_td))) (Nat.le_refl _)
  exact (hClone.seq hTdTail).mono
    (Nat.le_of_eq (Nat.add_assoc c_cl c_td 8674).symm)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

theorem w4StageP3Wide_zeroLive_fine_phaseCredit_tight
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {c_cl r_cl c_td l_td p_td r_td : Nat}
    (hClone : PhaseCreditSpec fineCostModel CloneEnv c_cl 0 0 r_cl)
    (hTd : PhaseCreditSpec fineCostModel TryDecEnv c_td l_td p_td r_td) :
    PhaseCreditSpec fineCostModel (W4StageP3WideEnv CloneEnv TryDecEnv)
      (c_cl + c_td + 8674)
      l_td
      (max p_td l_td)
      (max r_cl (max r_td 192)) :=
  (w4StageP3Wide_fine_phaseCredit_tight hClone hTd).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add l_td))
    (by simp only [Nat.zero_add, Nat.zero_max]; exact Nat.le_refl _)
    (Nat.le_refl _)

/-! ### Widened Stage P4 (`Matched`, `PathA`, `PathC`) Early-Reject Bounds -/

private theorem p4_split_maxReq_le (r32s r32k r16s rSt : Nat) :
    max r32s (max r32k (max r16s rSt)) ≤ max (max r32s r32k) (max r16s rSt) := by
  have hsm : max r32s r32k ≤ max (max r32s r32k) (max r16s rSt) := Nat.le_max_left _ _
  exact Nat.max_le.mpr
    ⟨Nat.le_trans (Nat.le_max_left _ _) hsm,
     Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_right _ _) hsm, Nat.le_max_right _ _⟩⟩

/-! ### Closed-Form Widened 4-Arm Slot Formulas & `PhaseCreditSpec`s -/

/-- Per-directory domain bundle (`[ownDir, peersDir, spkDir, opkDir] ≤ smallFileCap` vs
`kpkDir ≤ kpkFileCap`) for `W4DecryptPrekeySplitWideSlotEnv`. -/
structure W4DecryptPrekeySplitWideDirDom {α : Type} (P : W4DecryptPrekeySlotParams α)
    (sessFileCap smallFileCap kpkFileCap curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap : Nat) : Prop where
  peer_len : P.peer.name.bytes.length ≤ 40
  ownKey_len : P.ownKeyName.length ≤ 64
  ownReg_len : P.ownRegName.length ≤ 64
  kpkMark_len : P.kpkMarkName.length ≤ 64
  res_old : P.x_res.cap.toNat ≤ ikmCap
  res_new : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap
  ikm_small : max ikmCap 1569 ≤ 135167
  spqr_key : P.x_spqr.p.authKey.length ≤ 32
  sess_cap : ∀ bs, P.rd P.files (pathOf P.sessDir.path (addressText P.peer.val)) = .ok bs →
    bs.length ≤ sessFileCap
  small_cap : ∀ d ∈ [P.ownDir, P.peersDir, P.spkDir, P.opkDir],
    ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap
  kpk_cap : ∀ n bs, P.rd P.files (pathOf P.kpkDir.path n) = .ok bs → bs.length ≤ kpkFileCap
  cur_dom : (∀ evs, ¬ P.CurTrialFailEnv evs) ∨
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = P.st_cur ∧ SessionGhostValid P.G_cur ses_cur ∧
        SessionCloneDom curPqCap ses_cur
  arch_valid : ∀ G ses, P.g_arch.cur = some G → P.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses
  arch_enc : (encodeRecord P.r_arch).length ≤ archEncCap
  out0_valid : ∀ G ses, P.g_out0.cur = some G → P.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom out0PqCap ses
  out0_enc : (encodeRecord P.r_out0).length ≤ out0EncCap
  out1_freshBob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap P.G_out1 P.sess_out1 P.enc_prev1
  trials_len4 : P.archivedTrials.length ≤ 4

end WidenedBinaryCompleteTightSpecs

end LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec

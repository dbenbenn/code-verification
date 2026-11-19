/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptCalleesPeak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Peak Live-Heap Interface for W1 `message_encrypt`

Top-level interface for the W1 `message_encrypt` slot, re-exporting `W1EncryptSegments`,
`W1EncryptCalleesPeak`, and `W1EncryptSlotPeak`, wiring in `SpqrSendPeakSpec` (`spqr::send`), and
establishing `Δlive ≤ Δpeak` for `CliRunSlotCalleeSpecs`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec

open VerifiedLibraries.Mallocng.Proofs (sizeToClassUnits sizeToClass_spec)
open CryptoGames.LibsignalSession (Crypto OutgoingTripleRatchet SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord execOk)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (PreKeyMsgNewCall WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1IdKit w1SessKit)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent)
open LibsignalBinary.Heap.Fine
  (FineScale MmapThresholdReq coarseGrpWtS coarseSlotWt declCost63 fineCostModel fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_largeCost_eq fineCostModel_largeMetaCost_eq fineCostModel_smallMaxReq_eq
   smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (PeerSpqrValid)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSmallStorePollEnv
   sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
   smallStorePollDeltaCum smallStorePollDeltaLive smallStorePollDeltaPeak smallStorePollMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrLowInterceptHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
  (SpqrSendCappedEnv SpqrSendEnv SpqrSendTightEnv spqrSendCapped_phaseCreditSpec spqrSendDeltaCum
   spqrSendDeltaLive spqrSendDeltaPeak spqrSendMaxReq spqrSend_phaseCreditSpec_tight640
   spqrSend_phaseCreditSpec_valid)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (PeerSpqrTightValid640 ValidChainParams ValidEncoderPts640 spqrEncTightPtsCap)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
  (tryCloneLargeDelta tryCloneSmallDelta)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv preKeyMsgNewDeltaCum preKeyMsgNewDeltaLive preKeyMsgNewDeltaPeak
   preKeyMsgNewMaxReq signalMessageNewDeltaCum signalMessageNewDeltaLive signalMessageNewDeltaPeak
   signalMessageNewMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
  (KyberOptStepEnv OtrApplyEnvTight OtrEncryptStepEnv
   boxAlloc_creditSpec_tight boxPollDrop_creditSpec_tight kyberOpt_creditSpec_eq_tight
   otrApply_creditSpec_tight otrEncryptStep_creditSpec otrEncryptStep_creditSpec_small32
   otrEncryptStep_creditSpec_tight rustAlloc_pos_creditSpec_tight
   stringCloneFree_creditSpec_tight stringClone_creditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptCalleesPeak (fromKeyWithPksm_capped_tight otrEncryptWithSigNew_capped_small32 otrEncryptWithSigNew_capped_tight otrEncryptWithSigNew_creditSpec otrEncryptWithSigNew_creditSpec_small32 otrEncryptWithSigNew_creditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak (FromApplyTightEnv FromCmTightEnv FromOtrTightEnv FromSaveTightEnv WithStoresEncTightEnv cliSessStorePoll_exists_capped fromCmTight_creditSpec_aff fromCmTight_creditSpec_small fromCmTight_creditSpec_tight otrAfterNone otrAfterSome w1_peer_addressText_le_64 withStoresEncTight_creditSpec_aff withStoresEncTight_creditSpec_small withStoresEncTight_creditSpec_tight)

/-! ## 1. Re-Exports -/

export W1EncryptSegments (KyberOptStepEnv OtrApplyEnvTight OtrEncryptStepEnv)
export W1EncryptSegments (otrEncryptStep_creditSpec otrEncryptStep_creditSpec_small32)
export W1EncryptSegments (rustAlloc_pos_creditSpec_tight boxAlloc_creditSpec_tight)
export W1EncryptSegments (stringClone_creditSpec_tight stringCloneFree_creditSpec_tight)
export W1EncryptSegments (kyberOpt_creditSpec_eq_tight boxPollDrop_creditSpec_tight)
export W1EncryptSegments (otrApply_creditSpec_tight otrEncryptStep_creditSpec_tight)
export W1EncryptCalleesPeak (otrEncryptWithSigNew_creditSpec otrEncryptWithSigNew_creditSpec_small32)
export W1EncryptCalleesPeak (otrEncryptWithSigNew_creditSpec_tight otrEncryptWithSigNew_capped_tight)
export W1EncryptSlotPeak (FromApplyTightEnv FromSaveTightEnv FromCmTightEnv)
export W1EncryptSlotPeak (FromOtrTightEnv WithStoresEncTightEnv)
export W1EncryptSlotPeak (fromCmTight_creditSpec_aff fromCmTight_creditSpec_small)
export W1EncryptSlotPeak (withStoresEncTight_creditSpec_aff withStoresEncTight_creditSpec_small)
/-- `l_st ≤ p_st` on the trailing `store_session` step implies `Δlive ≤ Δpeak` across `w1CliEncryptSlot_creditSpec_small`.
-/
theorem w1SlotLive_le_w1SlotPeak
    (ptextLen l_s p_s l_sig p_sig l_pk p_pk l_ld p_ld l_id p_id l_st p_st : Nat)
    (hlp_st : l_st ≤ p_st) :
    let ctLen := (ptextLen / 16 + 1) * 16
    let l_otr := l_s + (ctLen + 8195) + l_sig
    let p_otr := max p_s (l_s + (ctLen + 8195) + p_sig)
    let l_cm := l_id + (l_id + l_st)
    let p_cm := max p_id (l_id + max p_id (l_id + p_st))
    let l_fo := (1569 + 8195) + l_otr + l_pk + l_cm
    let p_fo := (1569 + 8195) + max p_otr (l_otr + max p_pk (l_pk + p_cm))
    l_ld + l_fo ≤ max p_ld (l_ld + p_fo) := by
  intro ctLen l_otr p_otr l_cm p_cm l_fo p_fo
  have h1 : l_id + l_st ≤ max p_id (l_id + p_st) :=
    Nat.le_trans (Nat.add_le_add_left hlp_st l_id) (Nat.le_max_right p_id (l_id + p_st))
  have hcm : l_cm ≤ p_cm :=
    Nat.le_trans (Nat.add_le_add_left h1 l_id) (Nat.le_max_right p_id _)
  have h2 : l_pk + l_cm ≤ max p_pk (l_pk + p_cm) :=
    Nat.le_trans (Nat.add_le_add_left hcm l_pk) (Nat.le_max_right p_pk (l_pk + p_cm))
  have h3 : l_otr + (l_pk + l_cm) ≤ max p_otr (l_otr + max p_pk (l_pk + p_cm)) :=
    Nat.le_trans (Nat.add_le_add_left h2 l_otr) (Nat.le_max_right p_otr _)
  have hfo : l_fo ≤ p_fo := by omega
  exact Nat.le_trans (Nat.add_le_add_left hfo l_ld) (Nat.le_max_right p_ld (l_ld + p_fo))

/-! ## 3. End-to-End W1 Slot with `SpqrSendPeakSpec` -/


/-! ## 4. Tight `Δlive ≤ Δpeak` and `max nameCum` Elimination -/

/-- `l_st ≤ p_st` on the trailing `store_session` step implies `Δlive ≤ Δpeak` across `w1CliEncryptSlot_*_creditSpec_tight`.
-/
theorem w1SlotLive_le_w1SlotPeak_tight
    (ctLarge l_s p_s l_sig p_sig l_pk p_pk l_ld p_ld l_id p_id l_st p_st : Nat)
    (hlp_st : l_st ≤ p_st) :
    let l_otr := l_s + ctLarge + l_sig
    let p_otr := max p_s (l_s + ctLarge + p_sig)
    let l_cm := l_id + (l_id + l_st)
    let p_cm := max p_id (l_id + max p_id (l_id + p_st))
    let l_fo := l_otr + l_pk + l_cm
    let p_fo := max p_otr (l_otr + max p_pk (l_pk + p_cm))
    l_ld + l_fo ≤ max p_ld (l_ld + p_fo) := by
  intro l_otr p_otr l_cm p_cm l_fo p_fo
  have h1 : l_id + l_st ≤ max p_id (l_id + p_st) :=
    Nat.le_trans (Nat.add_le_add_left hlp_st l_id) (Nat.le_max_right p_id (l_id + p_st))
  have hcm : l_cm ≤ p_cm :=
    Nat.le_trans (Nat.add_le_add_left h1 l_id) (Nat.le_max_right p_id _)
  have h2 : l_pk + l_cm ≤ max p_pk (l_pk + p_cm) :=
    Nat.le_trans (Nat.add_le_add_left hcm l_pk) (Nat.le_max_right p_pk (l_pk + p_cm))
  have hfo : l_fo ≤ p_fo := by
    dsimp only [l_fo]
    rw [Nat.add_assoc]
    exact Nat.le_trans (Nat.add_le_add_left h2 l_otr) (Nat.le_max_right p_otr _)
  exact Nat.le_trans (Nat.add_le_add_left hfo l_ld) (Nat.le_max_right p_ld (l_ld + p_fo))

/-- Collapses the `max nameCum` error-branch joins in `w1CliEncryptSlot_*_creditSpec_tight` when `nameCum ≤ 3 * s32`.
-/
theorem w1SlotCum_noMax_eq
    (s24 s32 s1569 nameCum c_ld c_otr c_pk c_id c_st : Nat)
    (h : nameCum ≤ 3 * s32) :
    let c_ap := s32 + s32 + c_st
    let c_save := (s32 + c_id) + c_ap
    let c_cm := (s32 + c_id) + max nameCum c_save
    let c_fo := max nameCum (s1569 + c_otr + c_pk + c_cm)
    (s24 + c_ld) + max nameCum c_fo =
      (s24 + c_ld) +
        (s1569 + c_otr + c_pk +
          ((s32 + c_id) + ((s32 + c_id) + (s32 + s32 + c_st)))) := by
  dsimp only
  omega

/-! ## 5. Concrete `fineCostModel` Caps -/

theorem fine_le_smallMaxReq_1569 :
    1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  decide

theorem fine_nameCum_le_738 :
    ∀ n, 0 < n → n ≤ 40 → HasFineReallocCredit.smallAllocCost fineCostModel n ≤ 738 :=
  fun _ _ hn => smallAllocCost_le_738_of_le_44 (Nat.le_trans hn (by decide))

private def w1SmallPoints : List (Nat × Nat) :=
  [(24, 488), (32, 738), (40, 738), (1569, 2792)]

private def checkW1SmallPoints : Bool :=
  w1SmallPoints.all fun (req, expected) => fineSmallAllocCost req == expected

private theorem checkW1SmallPoints_true : checkW1SmallPoints = true := by
  decide +kernel

private theorem extractW1SmallPoint {req expected : Nat}
    (hmem : (req, expected) ∈ w1SmallPoints) :
    HasFineReallocCredit.smallAllocCost fineCostModel req = expected := by
  change fineSmallAllocCost req = expected
  exact of_decide_eq_true (List.all_eq_true.mp checkW1SmallPoints_true (req, expected) hmem)

theorem smallAllocCost_fine_24 :
    HasFineReallocCredit.smallAllocCost fineCostModel 24 = 488 :=
  extractW1SmallPoint (by decide)

theorem smallAllocCost_fine_32 :
    HasFineReallocCredit.smallAllocCost fineCostModel 32 = 738 :=
  extractW1SmallPoint (by decide)

theorem smallAllocCost_fine_40 :
    HasFineReallocCredit.smallAllocCost fineCostModel 40 = 738 :=
  extractW1SmallPoint (by decide)

theorem smallAllocCost_fine_1569 :
    HasFineReallocCredit.smallAllocCost fineCostModel 1569 = 2792 :=
  extractW1SmallPoint (by decide)

theorem fine_nameCum_le_three_mul_32 :
    738 ≤ 3 * HasFineReallocCredit.smallAllocCost fineCostModel 32 := by
  rw [smallAllocCost_fine_32]
  decide

private def checkW1ClassAllocWtLe : Bool :=
  (List.range 48).all fun sc =>
    decide (coarseSlotWt sc + (122 * coarseGrpWtS sc + FineScale - 1) / FineScale ≤ 143484)

private theorem checkW1ClassAllocWtLe_true : checkW1ClassAllocWtLe = true := by
  decide +kernel

/-- Upper bound `smallAllocCost fineCostModel n ≤ 143,484` across `n ≤ smallMaxReq fineCostModel = 135,167`.
-/
theorem smallAllocCost_fineCostModel_le_143484 {n : Nat}
    (hSm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel) :
    HasFineReallocCredit.smallAllocCost fineCostModel n ≤ 143484 := by
  rw [fineCostModel_smallMaxReq_eq] at hSm
  change fineSmallAllocCost n ≤ 143484
  unfold fineSmallAllocCost
  by_cases hle : n ≤ MmapThresholdReq
  · simp only [hle, ↓reduceIte]
    have hsc : sizeToClassUnits ((n + 3) / 16) < 48 :=
      (sizeToClass_spec (req := n) (by unfold MmapThresholdReq at hle; exact hle)).1
    have hcell := List.all_eq_true.mp checkW1ClassAllocWtLe_true _ (List.mem_range.mpr hsc)
    exact of_decide_eq_true hcell
  · simp only [hle, ↓reduceIte]
    have hlg : declCost63 n 16 = n + 8195 := fineCostModel_largeCost_eq n
    rw [hlg, Nat.add_assoc]
    exact Nat.le_trans (Nat.add_le_add_right hSm (8195 + 122)) (by decide)

/-- Global upper bound `tryCloneSmallDelta fineCostModel n ≤ 143,484` for all `n : Nat`. -/
theorem tryCloneSmallDelta_fineCostModel_le_143484 (n : Nat) :
    tryCloneSmallDelta fineCostModel n ≤ 143484 := by
  unfold tryCloneSmallDelta
  by_cases h0 : n = 0
  · simp only [h0, ↓reduceIte]
    decide
  · simp only [h0, ↓reduceIte]
    by_cases hSm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel
    · simp only [hSm, ↓reduceIte]
      exact smallAllocCost_fineCostModel_le_143484 hSm
    · simp only [hSm, ↓reduceIte, fineCostModel_largeMetaCost_eq]
      decide

theorem tryCloneLargeDelta_fineCostModel_le {n cap : Nat} (hle : n ≤ cap) :
    tryCloneLargeDelta fineCostModel n ≤ HasFineReallocCredit.largeCost fineCostModel cap := by
  unfold tryCloneLargeDelta
  by_cases hSm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel
  · simp only [hSm, ↓reduceIte]
    exact Nat.zero_le _
  · simp only [hSm, ↓reduceIte, fineCostModel_largeCost_eq]
    exact Nat.add_le_add_right hle 8195

theorem tryCloneLargeDelta_fineCostModel_le_add {n cap : Nat} (hle : n ≤ cap) :
    tryCloneLargeDelta fineCostModel n ≤ cap + 8195 := by
  simpa only [fineCostModel_largeCost_eq] using tryCloneLargeDelta_fineCostModel_le hle

/-! ## 6. Tight and `PeerSpqrTightValid640` End-to-End W1 Slot Instantiations -/

theorem spqrSend_phaseCreditSpec_tight640_valid {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {stBytes ptext : List (BitVec 8)}
    (hPts : ValidEncoderPts640 stBytes) (_hCp : ValidChainParams stBytes)
    (hlt : stBytes.length < 2 ^ 31) :
    PhaseCreditSpec M (SpqrSendTightEnv stBytes ptext)
      (spqrSendDeltaCum 2147483647 ptext.length spqrEncTightPtsCap)
      (spqrSendDeltaLive 2147483647 ptext.length spqrEncTightPtsCap)
      (spqrSendDeltaPeak 2147483647 ptext.length spqrEncTightPtsCap)
      (spqrSendMaxReq 2147483647 ptext.length spqrEncTightPtsCap) := by
  rw [show (2 : Nat) ^ 31 = 2147483647 + 1 by decide] at hlt
  exact spqrSend_phaseCreditSpec_tight640 hM hLow hPts
    (Nat.le_of_lt_succ hlt) (Nat.le_refl ptext.length)



end LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec

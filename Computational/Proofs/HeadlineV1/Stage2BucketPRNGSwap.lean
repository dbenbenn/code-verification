/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.DeliverForgeDir2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECell -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgBucketBounds -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperBucketPRNG -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperSim
import Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper
import Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapShifted
import Computational.Proofs.CryptoGames.CKA.DHProof
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS2 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDir2 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedCKA
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedPRNG3
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGEval
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS
import Computational.Proofs.ReductionDsl.SM.DeliverForgeBucketSimEval
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.SessionCostedFig8.BundlesEval
import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators ENNReal
open OracleSpec OracleComp
open CryptoGames.PRFPRNG (prngIface)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic atomicShortPubB
  fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv ckaAdvantage_congr prngAdvantage_congr)

open scoped MeasureTheory
open Computational.Proofs.SessionCostedFig8.Bundles (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesEval (compilePrngDFAtomic_coinSimEquiv fsAtomicB_receive_rsReach)
open Computational.Proofs.SessionCostedFig8.FsAtomicBSwap (HooksLocalFsAgree vRecv_localFs_eq vSend_localFs_eq)
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme dhScheme_correct)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lAead lChainPRG lFS lFig8 lPubOf)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open CryptoGames.SM (Config admissibleLastLeakGuesses lastLeakGuessAdmissible)
open CryptoGames.SM.Construction (Header PartyState healEpoch mkParties redPRNGAuthDFPaperBucketHybridProg redPRNGAuthDFPaperBucketHybridProg_advantage_vr_impl)
open CryptoGames.SM.Engine (Ctx EState Hooks HooksVRInv RSReach SMEngineInv SMVRInv VP abortE coinsE commitE deliverE implEDFPaperBucketRaw_inv implEDFPaperBucketRaw_vrInv injectE noDoomPolicy run_liftH_bind transmitEBucket_eq_transmitE)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge (DdhRoleOk badSendMsg_transmit_false commitE_localCKA_eq dhSchemeFb_receive_of_roleOk dhSchemeFb_send_of_roleOk implE_localCKA_eq localPartyInv_mkParties vRecv_localCKA_eq)
open CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF badSendMsgDF)
open ReductionDsl (CostedReduction)

namespace Computational.Proofs.HeadlineV1.Stage2BucketPRNGSwap

public section

theorem hB1_hops12 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Z : Crypto) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (ht2 : 2 ≤ t)
    (dfAdv : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) :
    let challAdvDF := CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageShiftedDir2Paper
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT idOf 25000 lam)
        (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (t - 1) t challAdvDF ≤
      CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch (some (t - 2)))
        (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedDir2Paper (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT idOf 25000) lam (qep + 1) (t - 1) t challAdvDF) +
      CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
        (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedDir2Paper (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT idOf 25000) lam (qep + 1) (t - 1) t challAdvDF) +
      𝒟[CryptoGames.SM.Construction.DeliverForge.localAuthDFShiftedDir2Paper (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT idOf 25000) lam 0 (qep + 1) (t - 1)
          (some ((t - 1) - 1)) t challAdvDF] {true} := by
  intro challAdvDF
  let cka := dhScheme Dh
  let prng := rootPRNG Z.F encPt
  let fs := lFS Z protoSignalCodec ℓ encT idOf 25000
  have hc : cka.Correct := dhScheme_correct Dh hDh
  have hnb : CryptoGames.SM.Construction.AuthL9DFDir2.NoBadCoinsDF challAdvDF :=
    CryptoGames.SM.Construction.DeliverForge.noBadCoinsDF_challSimDF'Paper (2 + 1) (qep + 1) dfAdv
  change CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageShiftedDir2Paper
      (CryptoGames.SM.Construction.scheme cka prng fs lam)
      (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (t - 1) t challAdvDF ≤
    CryptoGames.CKA.advantage cka 1 (healEpoch (some (t - 2)))
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedDir2Paper cka prng fs lam (qep + 1) (t - 1) t challAdvDF) +
    CryptoGames.PRFPRNG.advantage prng
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedDir2Paper cka prng fs lam (qep + 1) (t - 1) t challAdvDF) +
    𝒟[CryptoGames.SM.Construction.DeliverForge.localAuthDFShiftedDir2Paper cka prng fs lam 0 (qep + 1) (t - 1)
        (some ((t - 1) - 1)) t challAdvDF] {true}
  rw [CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.PRFPRNG.advantage_eq_boolDist]
  set cT := 𝒟[CryptoGames.CKA.branch cka 1 (healEpoch (some (t - 2))) true
    (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedDir2Paper cka prng fs lam (qep + 1) (t - 1) t challAdvDF)]
  set cF := 𝒟[CryptoGames.CKA.branch cka 1 (healEpoch (some (t - 2))) false
    (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedDir2Paper cka prng fs lam (qep + 1) (t - 1) t challAdvDF)]
  set pT := 𝒟[CryptoGames.PRFPRNG.branch prng true
    (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedDir2Paper cka prng fs lam (qep + 1) (t - 1) t challAdvDF)]
  set pF := 𝒟[CryptoGames.PRFPRNG.branch prng false
    (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedDir2Paper cka prng fs lam (qep + 1) (t - 1) t challAdvDF)]
  have hl1 : 1 ≤ t - 1 := by omega
  have ht_eq : (t - 1) + 1 = t := by omega
  have hheal : healEpoch (some (t - 2)) = (t - 1) + 1 := by
    simp only [healEpoch]; omega
  have h9 : CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageShiftedDir2Paper
      (CryptoGames.SM.Construction.scheme cka prng fs lam) (qep + 1)
      CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (t - 1) t challAdvDF ≤ cF {true} := by
    dsimp only [cF]
    rw [hheal, ← ht_eq]
    exact CryptoGames.SM.Construction.DeliverForge.lemma9_df_shifted_dir2_paper cka prng fs lam (qep + 1) (t - 1) hc hl1 challAdvDF hnb
  have h10 : cT {true} ≤ pF {true} := by
    dsimp only [cT, pF]
    rw [hheal]
    exact CryptoGames.SM.Construction.DeliverForge.lemma10_df_shifted_dir2_paper cka prng fs lam (qep + 1) (t - 1) t hl1 challAdvDF
  have h11 : pT {true} ≤
      𝒟[CryptoGames.SM.Construction.DeliverForge.localAuthDFShiftedDir2Paper cka prng fs lam 0 (qep + 1) (t - 1)
          (some ((t - 1) - 1)) t challAdvDF] {true} :=
    CryptoGames.SM.Construction.DeliverForge.branch_redPRNGAuthDFShiftedDir2Paper_le_localAuthDFShiftedDir2Paper
      cka prng fs lam (qep + 1) (t - 1) t challAdvDF
  have hc' : cF {true} ≤ cT {true} + cT.boolDist cF := by
    rw [MeasureTheory.Measure.boolDist_comm]; exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _
  have hp' : pF {true} ≤ pT {true} + pT.boolDist pF := by
    rw [MeasureTheory.Measure.boolDist_comm]; exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _
  calc CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageShiftedDir2Paper
          (CryptoGames.SM.Construction.scheme cka prng fs lam) (qep + 1)
          CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (t - 1) t challAdvDF
      ≤ cF {true} := h9
    _ ≤ cT {true} + cT.boolDist cF := hc'
    _ ≤ (pT {true} + pT.boolDist pF) + cT.boolDist cF := add_le_add (h10.trans hp') le_rfl
    _ ≤ (𝒟[CryptoGames.SM.Construction.DeliverForge.localAuthDFShiftedDir2Paper cka prng fs lam 0 (qep + 1) (t - 1)
            (some ((t - 1) - 1)) t challAdvDF] {true} + pT.boolDist pF) + cT.boolDist cF :=
        add_le_add (add_le_add h11 le_rfl) le_rfl
    _ = _ := by ac_rfl

theorem hB2_hops12 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Z : Crypto) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (ht3 : 3 ≤ t)
    (dfAdv : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) :
    let challAdvDF := CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageShiftedPaper
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT idOf 25000 lam)
        (2 + 1) (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (t - 2) t challAdvDF ≤
      CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch (some (t - 3)))
        (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedPaper (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT idOf 25000) lam 1 (qep + 1) (t - 2) t challAdvDF) +
      CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
        (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaper (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT idOf 25000) lam 1 (qep + 1) (t - 2) t challAdvDF) +
      𝒟[CryptoGames.SM.Construction.DeliverForge.localAuthDFShiftedPaper (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT idOf 25000) lam 1 (qep + 1) (t - 2)
          (some ((t - 2) - 1)) t challAdvDF] {true} := by
  intro challAdvDF
  let cka := dhScheme Dh
  let prng := rootPRNG Z.F encPt
  let fs := lFS Z protoSignalCodec ℓ encT idOf 25000
  have hc : cka.Correct := dhScheme_correct Dh hDh
  have hnb : CryptoGames.SM.Construction.AuthL9DFDir2.NoBadCoinsDF challAdvDF :=
    CryptoGames.SM.Construction.DeliverForge.noBadCoinsDF_challSimDF'Paper (2 + 1) (qep + 1) dfAdv
  change CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageShiftedPaper
      (CryptoGames.SM.Construction.scheme cka prng fs lam)
      (2 + 1) (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (t - 2) t challAdvDF ≤
    CryptoGames.CKA.advantage cka 1 (healEpoch (some (t - 3)))
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedPaper cka prng fs lam 1 (qep + 1) (t - 2) t challAdvDF) +
    CryptoGames.PRFPRNG.advantage prng
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaper cka prng fs lam 1 (qep + 1) (t - 2) t challAdvDF) +
    𝒟[CryptoGames.SM.Construction.DeliverForge.localAuthDFShiftedPaper cka prng fs lam 1 (qep + 1) (t - 2)
        (some ((t - 2) - 1)) t challAdvDF] {true}
  rw [CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.PRFPRNG.advantage_eq_boolDist]
  set cT := 𝒟[CryptoGames.CKA.branch cka 1 (healEpoch (some (t - 3))) true
    (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedPaper cka prng fs lam 1 (qep + 1) (t - 2) t challAdvDF)]
  set cF := 𝒟[CryptoGames.CKA.branch cka 1 (healEpoch (some (t - 3))) false
    (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedPaper cka prng fs lam 1 (qep + 1) (t - 2) t challAdvDF)]
  set pT := 𝒟[CryptoGames.PRFPRNG.branch prng true
    (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaper cka prng fs lam 1 (qep + 1) (t - 2) t challAdvDF)]
  set pF := 𝒟[CryptoGames.PRFPRNG.branch prng false
    (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaper cka prng fs lam 1 (qep + 1) (t - 2) t challAdvDF)]
  have hl1 : 1 ≤ t - 2 := by omega
  have hheal : healEpoch (some (t - 3)) = (t - 2) + 1 := by
    simp only [healEpoch]; omega
  have h9 : CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageShiftedPaper
      (CryptoGames.SM.Construction.scheme cka prng fs lam) (2 + 1) (qep + 1)
      CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (t - 2) t challAdvDF ≤ cF {true} := by
    dsimp only [cF]
    rw [hheal]
    exact CryptoGames.SM.Construction.DeliverForge.lemma9_df_shifted_paper cka prng fs lam (qep + 1) (t - 2) t hc hl1 challAdvDF hnb
  have h10 : cT {true} ≤ pF {true} := by
    dsimp only [cT, pF]
    rw [hheal]
    exact CryptoGames.SM.Construction.DeliverForge.lemma10_df_shifted_paper cka prng fs lam 1 (qep + 1) (t - 2) t hl1 challAdvDF
  have h11 : pT {true} ≤
      𝒟[CryptoGames.SM.Construction.DeliverForge.localAuthDFShiftedPaper cka prng fs lam 1 (qep + 1) (t - 2)
          (some ((t - 2) - 1)) t challAdvDF] {true} :=
    CryptoGames.SM.Construction.DeliverForge.branch_redPRNGAuthDFShiftedPaper_le_localAuthDFShiftedPaper
      cka prng fs lam 1 (qep + 1) (t - 2) t challAdvDF
  have hc' : cF {true} ≤ cT {true} + cT.boolDist cF := by
    rw [MeasureTheory.Measure.boolDist_comm]; exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _
  have hp' : pF {true} ≤ pT {true} + pT.boolDist pF := by
    rw [MeasureTheory.Measure.boolDist_comm]; exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _
  calc CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageShiftedPaper
          (CryptoGames.SM.Construction.scheme cka prng fs lam) (2 + 1) (qep + 1)
          CryptoGames.SM.Construction.DeliverForge.sameHdrScheme (t - 2) t challAdvDF
      ≤ cF {true} := h9
    _ ≤ cT {true} + cT.boolDist cF := hc'
    _ ≤ (pT {true} + pT.boolDist pF) + cT.boolDist cF := add_le_add (h10.trans hp') le_rfl
    _ ≤ (𝒟[CryptoGames.SM.Construction.DeliverForge.localAuthDFShiftedPaper cka prng fs lam 1 (qep + 1) (t - 2)
            (some ((t - 2) - 1)) t challAdvDF] {true} + pT.boolDist pF) + cT.boolDist cF :=
        add_le_add (add_le_add h11 le_rfl) le_rfl
    _ = _ := by ac_rfl

theorem admissibleLastLeakGuesses_four_healEpoch_le {qep : ℕ} {tL : Option ℕ}
    (htL : tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1)) :
    healEpoch tL ≤ qep + 2 := by
  simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at htL
  rcases htL with rfl | ⟨l, hl, rfl⟩
  · simp [healEpoch]
  · simp only [healEpoch]
    omega

private lemma hooksPRNGBucketHybridGen_startRecv_rs' {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    {VROk : RS → Prop}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (tn0 : T)
    (h : CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T Sig K I) (res : _)
    (hmem : res ∈ support (((CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).startRecv
      ctx P t0 γ0 σv0 tn0).run h))
    (γ' : Γ) (σ' : Option Sig) (rs : RS) (hEq : res.1 = some (some (γ', σ', rs))) :
    VROk rs := by
  dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hmem
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have hTail :
      res ∈ support ((do
        if !(qep + 1 < t0) && (lastLeakGuessAdmissible Δbucket tL t0 &&
            (CryptoGames.SM.Construction.DeliverForge.partyPar (CryptoGames.Party.senderOf t0) == par)) then
          if tL.isSome && t0 = healEpoch tL then
            return none
          else if CryptoGames.SM.Construction.DeliverForge.postLeak tL ctx || h.corrRoot.isSome || t < t0 then
            match CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with
            | none => return none
            | some σ =>
              let kk := cka.receive γ0 tn0
              let p := prng.up σ kk.2
              return some (some (kk.1, some p.1, fs.initReceiver p.2))
          else if t0 = t then
            let kk := cka.receive γ0 tn0
            match ← CryptoGames.SM.Construction.DeliverForge.liftPBucket (CryptoGames.PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) kk.2) with
            | none => return none
            | some (σOut, kOut) =>
              return some (some (kk.1, some σOut, fs.initReceiver kOut))
          else if !(t0 < healEpoch tL) then
            let kk := cka.receive γ0 tn0
            let kOut ← CryptoGames.SM.Construction.DeliverForge.lookupPRNGBucketF t0 kk.2
            return some (some (kk.1, none, fs.initReceiver kOut))
          else
            return some none
        else
          return some none).run h) → VROk rs := by
    intro hmem'
    split_ifs at hmem'
    · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
      subst hmem'; simp at hEq
    · rcases hres : CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with _ | σ
      · rw [hres, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
        subst hmem'; simp at hEq
      · rw [hres, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
        subst hmem'; rcases Option.some.inj (Option.some.inj hEq) with ⟨_, _, rfl⟩
        exact hInitR _
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem'
      obtain ⟨⟨o, h₁⟩, _, hmem'⟩ := hmem'
      rcases o with _ | ⟨σOut, kOut⟩
      · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
        subst hmem'; simp at hEq
      · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
        subst hmem'; rcases Option.some.inj (Option.some.inj hEq) with ⟨_, _, rfl⟩
        exact hInitR _
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem'
      obtain ⟨⟨kOut, h₁⟩, _, hmem'⟩ := hmem'
      rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
      subst hmem'; rcases Option.some.inj (Option.some.inj hEq) with ⟨_, _, rfl⟩
      exact hInitR _
    · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
      subst hmem'; simp at hEq
    · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
      subst hmem'; simp at hEq
  rcases hc : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
  · simp only [hc] at hmem; exact hTail hmem
  · by_cases hEqT : tCached = tn0
    · simp only [hc, hEqT, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; rcases Option.some.inj (Option.some.inj hEq) with ⟨_, _, rfl⟩
      exact hInitR _
    · simp only [hc, hEqT, ↓reduceIte] at hmem; exact hTail hmem

local instance {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

private lemma badSendMsgDF_query_bind_step' {St Msg Coins C α : Type} (Pmsg : Msg → Bool)
    (qy : (unifSpec + CryptoGames.SM.specDF St Msg Coins C).Domain)
    (mx : (unifSpec + CryptoGames.SM.specDF St Msg Coins C).Range qy →
      CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF St Msg Coins C α)
    (h : IsQueryBoundP
      ((liftM (OracleSpec.query qy) : OracleComp (unifSpec + CryptoGames.SM.specDF St Msg Coins C) _) >>= mx)
      (fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg t = true) 0) :
    badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg qy = false ∧
      ∀ u, IsQueryBoundP (mx u)
        (fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg t = true) 0 := by
  rw [isQueryBoundP_query_bind_iff] at h
  rcases h with ⟨hq0, hmx⟩
  have hbf : badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg qy = false :=
    Bool.eq_false_iff.mpr (hq0.resolve_right (by omega))
  refine ⟨hbf, fun u => ?_⟩
  have hu := hmx u; simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hu; exact hu

private lemma badSendMsgDF_inl_to_badSendMsg' {St Msg Coins C : Type} (Pmsg : Msg → Bool)
    (t5 : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (h : badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg (.inr (.inl t5)) = false) :
    CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) Pmsg (.inr t5) = false := by
  rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P <;> exact h

private theorem implEDFPaperBucketRaw_localFs_eq {Pt ι : Type} [DecidableEq Pt] {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV : Type} {ℓ B0 B_q q' Δ qep : ℕ} {cfg : Config (LibsignalMsgPublicPart × Plain ℓ)}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) CCoins γV σV
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂) (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP γV Pt σV (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (t_sm : (CryptoGames.SM.Construction.DeliverForge.specDF (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (hBad : badSendMsgDF
      (St := PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) (.inr t_sm) = false)
    (hVR : SMVRInv (RSReachB maxForwardJumps) B_q (q' + 1) es.g) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ Δ qep maxForwardJumps cfg (.inr t_sm)).run es =
      (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ Δ qep maxForwardJumps cfg (.inr t_sm)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  rcases t_sm with t5 | ⟨P, c, c'⟩
  · have hBad5 := badSendMsgDF_inl_to_badSendMsg' (fun m => atomicShortPubB m.1) t5 hBad
    rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · change (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₁ Δ qep (P, m, r)).run es =
        (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₂ Δ qep (P, m, r)).run es
      unfold CryptoGames.SM.Construction.DeliverForge.transmitEBucket
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win) = true
      · simp [hab]
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases es.g.epMgmt Δ qep P r.isSome with _ | s₁
        · rfl
        · have hm : atomicShortPubB m.1 = true :=
            badSendMsg_transmit_false
              (ok := fun (x : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB x.1) hBad5
          simp only [run_liftH_bind]
          exact congrArg (· >>= _) (vSend_localFs_eq hAg s₁ P (s₁.st P) m none r hm es.h)
    · rfl
    · change (deliverE hk₁ maxForwardJumps cfg (P, c)).run es =
        (deliverE hk₂ maxForwardJumps cfg (P, c)).run es
      have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
      unfold deliverE
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win) = true
      · simp [hab]
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases es.g.inTransit P.other c with _ | r
        · rfl
        · simp only [run_liftH_bind,
            vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c (some r) es.h (hVR P), hCommit]
    · change (injectE hk₁ Δ qep cfg (P, c)).run es =
        (injectE hk₂ Δ qep cfg (P, c)).run es
      have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
      unfold injectE
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases href :
          (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ)) = true
      · simp [href]
      · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c none es.h (hVR P), hCommit]
    · change (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₁ P).run es =
        (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₂ P).run es
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket; rw [hAg.reveal_eq]
  · change (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₁ Δ qep cfg (P, c, c')).run es =
      (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es
    have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · dsimp only; split_ifs
        · rfl
        · simp only [run_liftH_bind,
            vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c' none es.h (hVR P), hCommit]

private theorem simulateQ_implEDFPaperBucket_localFs_eq {Pt ι : Type} [DecidableEq Pt] {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV α : Type} {ℓ L B0 B_q q Δ qep : ℕ}
    {cfg : Config (LibsignalMsgPublicPart × Plain ℓ)}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) CCoins γV σV
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂) (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) α}
    (hoa : oa.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) q)
    (hSendOk : IsQueryBoundP oa (fun t => badSendMsgDF
      (St := PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP γV Pt σV (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (winEp : Option ℕ)
    (hInv : SMEngineInv L B_q q es.g) (hVR : SMVRInv (RSReachB maxForwardJumps) B_q q es.g) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket hk₁ Δ qep maxForwardJumps cfg) oa).run (es, winEp) =
      (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket hk₂ Δ qep maxForwardJumps cfg) oa).run (es, winEp) := by
  have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
      (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
  induction oa using OracleComp.inductionOn generalizing q es winEp with
  | pure _ => rfl
  | query_bind qy mx ih =>
    obtain ⟨hBadQ, hBadMx⟩ := badSendMsgDF_query_bind_step' (fun m => atomicShortPubB m.1) qy mx hSendOk
    rw [isQueryBoundP_query_bind_iff] at hoa
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind, hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    unfold CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket CryptoGames.SM.Construction.DeliverForge.withWinEpDF
    dsimp only [StateT.run_mk]
    simp only [bind_assoc]
    rcases qy with n | t_sm
    · have hq0 : ¬ ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
          (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256)))
          (LibsignalMsgPublicPart × Plain ℓ) CCoins
          (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) (Sum.inl n) := by
        simp [ReductionDsl.isGameQuery]
      have hmx : ∀ u, (mx u).IsQueryBoundP _ q := fun u => by
        have hu := hoa.2 u; simp only [hq0, ↓reduceIte] at hu; exact hu
      have hInl₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ Δ qep maxForwardJumps cfg (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ Δ qep maxForwardJumps cfg (.inl n)).run es =
          (coinsE n).run es := rfl
      rw [hInl₁, hInl₂]
      simp only [coinsE, StateT.run_lift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u (hmx u) (hBadMx u) es _ hInv hVR
    · have hq1 : ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
          (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256)))
          (LibsignalMsgPublicPart × Plain ℓ) CCoins
          (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) (Sum.inr t_sm) := by
        simp [ReductionDsl.isGameQuery]
      rcases q with _ | q'
      · exact absurd (hoa.1.resolve_left (not_not.mpr hq1)) (by omega)
      have hmx : ∀ u, (mx u).IsQueryBoundP _ q' := fun u => by
        have hu := hoa.2 u; simp only [hq1, ↓reduceIte] at hu; exact hu
      rw [implEDFPaperBucketRaw_localFs_eq hAg hVRHk hB0 es t_sm hBadQ hVR]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hr => ?_
      simp only [pure_bind]
      exact ih u (hmx u) (hBadMx u) es' _
        (implEDFPaperBucketRaw_inv hk₂ cfg es t_sm hInv (u, es') hr)
        (implEDFPaperBucketRaw_vrInv hk₂ hVRHk cfg es t_sm hInv hVR (u, es') hr)

end

end Computational.Proofs.HeadlineV1.Stage2BucketPRNGSwap

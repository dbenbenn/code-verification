/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthWireEnd
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD
import Computational.Proofs.CryptoGames.SM.Theorem1.Queries
import Computational.Proofs.E2E.SpkHop2A
import Computational.Proofs.ReductionDsl.SM.Theorem1
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow

/-!
# Multi-Session Ideal-Cutoff (`multiSessEndWinProb = 0`) Proofs for `DeliverForgePaper`

Proves that at the ideal FS-AEAD hopping endpoint (`Thm5.hp cut cut la`, with
`cut = authHopCutoff maxForwardJumps qR la` and `2 * q ≤ qR`), all three
multi-session Stage-2 `DeliverForgePaper` FS-AEAD reductions output `true` with probability `0`:
1. `multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero` (`B1` and `B2`)
2. `multiSessEndWinProb_redFSAuthDFPaperMulti_eq_zero` (single-epoch Stage-2)
3. `multiSessEndWinProb_redFSAuthDFPaperMultiBucket_eq_zero` (`(tL, par)`-bucket Stage-2, `2 ≤ Δbucket`)-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEnd

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party AEADScheme)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.SM.Construction (
  redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF MakesAtMostQueriesDF)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessPubFsAdv multiSessPubToAD)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_isQueryBoundP_sessQueryAt)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessEndWinProb)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMultiGen)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (
  fwd lazyInit lazyInit_run_none' lazyInit_run_some'
  sessLift sessLift_inl sessLift_inr sessLiftCore multiSessSpec)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoGames.SM.Construction (
  Header Mode FSMultiState FSMultiDFBucketState FSMultiBook
  liftFSMulti liftFSMultiDFBucket lookupMultiF lookupMultiDFBucketF
  regSessMulti regSessOptMulti regSessMultiDFBucket regSessOptMultiDFBucket
  rootFSMulti rootFSMultiDFBucketPaper hooksFSMulti hooksFSMultiDFBucketPaper
  initFSMultiRaw initFSMultiDFBucketPaper runFSMultiDFPaper
  inStage2BucketGen bucketAuthCfgGen postLeakDFBucket)
open _root_.CryptoGames.SM.Engine (
  VP EState Hooks liftH abortE vSend vRecv commitE
  transmitE challE deliverE injectE coinsE authOut)
open _root_.CryptoGames.SM.Construction.DeliverForge (
  deliverForgeE corrEPaper corrEPaperBucket corrEShiftedPaper
  transmitEBucket challEBucket implEDFPaper implEDFShiftedPaperGen
  implEDFPaperBucketRaw implEDFPaperBucket engRunDFPaperBucket withWinEpDF authOutBucket)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  runFSMultiDFShiftedPaper)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec fsInit fsImpl)
open _root_.CryptoVerification.E2E.Signed.SessionWire (
  hpIdeal kind_hpIdeal sessQueryAt allSessions_hp_eq_hpIdeal_main allSessions_hp_eq_hpIdeal_la)
open _root_.CryptoGames.Ratchet.LibsignalInst (
  LibsignalCiphertextWithSalt32 lIdeal lAeadR lChainPRG lPubOf)
open _root_.CryptoGames.FSAEAD.Thm5 (
  HState HSt DG decIdx encIdxWith genUpTo receiveH
  transmitHWith challengeHWith corruptSenderH corruptReceiverH deliverH injectH
  getH getH_run onH modifyH modifyH_run hInit)
open _root_.CryptoGames.FSAEAD.Thm5.Ends (
  mem_support_genUpTo mem_support_encIdx mem_support_senderKey
  mem_support_receiveH_none mem_support_receiveH_some)
open _root_.CryptoGames.SM.Construction.AuthL11 (evalDist_bind_eq_zero)

theorem decIdx_hpIdeal_none {CK MK AD M C : Type}
    [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (N : ℕ) (la : Bool) (i : ℕ) (a : AD) (e : C)
    (s : HSt CK MK AD M C) (hc : s.1.isCompromised i = false) :
    (decIdx ae (hpIdeal N la) (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp))
      none i a e).run s = pure (none, s) := by
  have hk : _root_.CryptoGames.FSAEAD.Thm5.kind (hpIdeal N la)
      (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) s.1 i = .ideal := by
    simp [_root_.CryptoGames.FSAEAD.Thm5.kind, hpIdeal, hc]
  simp [decIdx, getH, onH, hk]

theorem isCompromised_of_senderCorruptedAt_none {CK MK AD M C : Type}
    (st : HState CK MK AD M C) (h : st.senderCorruptedAt = none) (i : ℕ) :
    st.isCompromised i = false := by
  simp [HState.isCompromised, h]

theorem injectH_hpIdeal_uncorr_not_accepted {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip N : ℕ) (la : Bool) (q : AD × (ℕ × C))
    (s s' : HSt CK MK AD M C) (hcorr : s.1.senderCorruptedAt = none)
    {res : Option (_root_.CryptoGames.FSAEAD.ReceiveResult M)}
    (hmem : (res, s') ∈ support
      ((injectH ae G maxSkip (hpIdeal N la) (DG G)
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) q).run s)) :
    s'.1.senderCorruptedAt = none ∧ ∀ i mo', res ≠ some (.accepted i mo') := by
  rcases q with ⟨a, i, e⟩
  unfold injectH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
    rcases hmem with ⟨rfl, hs'1, _⟩
    rw [hs'1]
    exact ⟨hcorr, fun _ _ h => nomatch h⟩
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨r, s₁⟩, hr₁, hr₂⟩
    have hc0 : s.1.isCompromised i = false := isCompromised_of_senderCorruptedAt_none s.1 hcorr i
    have hr_none : r = none ∧ s₁.1.senderCorruptedAt = none := by
      unfold receiveH at hr₁
      simp only [StateT.run_bind, getH_run, pure_bind] at hr₁
      split at hr₁
      · rw [StateT.run_bind, decIdx_hpIdeal_none ae N la i a e s hc0, pure_bind] at hr₁
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₁
        exact ⟨hr₁.1, by rw [hr₁.2.1]; exact hcorr⟩
      · split at hr₁
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₁
          exact ⟨hr₁.1, by rw [hr₁.2.1]; exact hcorr⟩
        · split at hr₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₁
            exact ⟨hr₁.1, by rw [hr₁.2.1]; exact hcorr⟩
          · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hr₁
            rcases hr₁ with ⟨⟨_, s₂⟩, hg, hr₁⟩
            rcases mem_support_genUpTo G hg with ⟨ks, hks⟩
            have hcorr₂ : s₂.1.senderCorruptedAt = none := by rw [hks]; exact hcorr
            have hc₂ : s₂.1.isCompromised i = false :=
              isCompromised_of_senderCorruptedAt_none s₂.1 hcorr₂ i
            rw [StateT.run_bind, decIdx_hpIdeal_none ae N la i a e s₂ hc₂, pure_bind] at hr₁
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₁
            exact ⟨hr₁.1, by rw [hr₁.2.1]; exact hcorr₂⟩
    rcases hr_none with ⟨rfl, hcorr₁⟩
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₂
    rcases hr₂ with ⟨rfl, hs'1, _⟩
    rw [hs'1]
    exact ⟨hcorr₁, fun _ _ h => nomatch h⟩

theorem receiveH_preserves_senderCorruptedAt {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip : ℕ) (P : _root_.CryptoGames.FSAEAD.Thm5.Params)
    (hint : Option M) (a : AD) (c : ℕ × C)
    (s s' : HSt CK MK AD M C) {r : Option (ℕ × M)}
    (hmem : (r, s') ∈ support
      ((receiveH ae G maxSkip P (DG G)
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) hint a c).run s)) :
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt := by
  rcases c with ⟨i, e⟩
  unfold receiveH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨m?, s₁⟩, hd, hm⟩
    have hs₁ := (_root_.CryptoGames.FSAEAD.Thm5.Ends.mem_support_decIdx ae hd).1
    rw [hs₁] at hm
    cases m? with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hm
      rw [hm.2.1]
    | some msg =>
      simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff] at hm
      rw [hm.2.1]
  · split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]
    · split at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2.1]
      · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨⟨_, s₁⟩, hg, hmem⟩
        rcases mem_support_genUpTo G hg with ⟨ks, hks⟩
        rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨⟨m?, s₂⟩, hd, hm⟩
        have hs₂ := (_root_.CryptoGames.FSAEAD.Thm5.Ends.mem_support_decIdx ae hd).1
        rw [hs₂] at hm
        cases m? with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hm
          rw [hm.2.1, hks]
        | some msg =>
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at hm
          rw [hm.2.1, hks]

theorem fsImpl_hpIdeal_true_step {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C)
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip N : ℕ) (q : (fsSpec CK MK AD M C).Domain)
    (s s' : HSt CK MK AD M C) (hcorr : s.1.senderCorruptedAt = none)
    {r : (fsSpec CK MK AD M C).Range q}
    (hmem : (r, s') ∈ support ((fsImpl ideal ae G maxSkip (hpIdeal N true) q).run s)) :
    s'.1.senderCorruptedAt = none := by
  unfold fsImpl _root_.CryptoGames.FSAEAD.Thm5.oraclesWith at hmem
  rcases q with ((((q_tr | q_ch) | q_cs) | q_cr) | q_dl) | q_ij
  · change (r, s') ∈ support
        ((transmitHWith ideal ae G (hpIdeal N true) (DG G) none q_tr).run s) at hmem
    unfold transmitHWith at hmem
    simp only [StateT.run_bind, getH_run, pure_bind] at hmem
    split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]; exact hcorr
    · simp only [StateT.run_bind, MonadAttach.mem_support_bind, modifyH_run, pure_bind,
        StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rcases hmem with ⟨⟨_, s₁⟩, h₁, ⟨_, s₂⟩, h₂, _, hs'1, _⟩
      rcases mem_support_genUpTo G h₁ with ⟨ks, hks⟩
      have hs₂ := mem_support_encIdx ideal ae h₂
      rw [hs₂, hks] at hs'1
      rw [hs'1]; exact hcorr
  · change (r, s') ∈ support
        ((challengeHWith ideal ae G (hpIdeal N true) (DG G) none q_ch).run s) at hmem
    unfold challengeHWith at hmem
    simp only [StateT.run_bind, getH_run, pure_bind] at hmem
    split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]; exact hcorr
    · simp only [StateT.run_bind, MonadAttach.mem_support_bind, modifyH_run, pure_bind,
        StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rcases hmem with ⟨⟨_, s₁⟩, h₁, ⟨_, s₂⟩, h₂, _, hs'1, _⟩
      rcases mem_support_genUpTo G h₁ with ⟨ks, hks⟩
      have hs₂ := mem_support_encIdx ideal ae h₂
      rw [hs₂, hks] at hs'1
      rw [hs'1]; exact hcorr
  · change (r, s') ∈ support
        ((corruptSenderH G (hpIdeal N true) q_cs).run s) at hmem
    unfold corruptSenderH at hmem
    simp only [StateT.run_bind, getH_run, pure_bind] at hmem
    split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]; exact hcorr
    · simp only [_root_.CryptoVerification.E2E.Signed.SessionWire.hpIdeal_la, ↓reduceIte,
        StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]; exact hcorr
  · change (r, s') ∈ support
        ((corruptReceiverH G (hpIdeal N true) q_cr).run s) at hmem
    unfold corruptReceiverH at hmem
    simp only [StateT.run_bind, getH_run, pure_bind] at hmem
    split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]; exact hcorr
    · simp only [_root_.CryptoVerification.E2E.Signed.SessionWire.hpIdeal_la, ↓reduceIte,
        StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]; exact hcorr
  · change (r, s') ∈ support
        ((deliverH ae G maxSkip (hpIdeal N true) (DG G) none q_dl).run s) at hmem
    unfold deliverH at hmem
    simp only [StateT.run_bind, getH_run, pure_bind] at hmem
    split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]; exact hcorr
    · cases hfind : s.1.inTransit.find? (fun rec => rec.ad == q_dl.1 && rec.ct == q_dl.2) with
      | none =>
        simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2.1]; exact hcorr
      | some rec =>
        simp only [hfind] at hmem
        rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨⟨ro, s₁⟩, hr₁, hr₂⟩
        have hcorr₁ := receiveH_preserves_senderCorruptedAt ae G maxSkip (hpIdeal N true)
          (some rec.msg) q_dl.1 q_dl.2 s s₁ hr₁
        cases ro with
        | none =>
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at hr₂
          rw [hr₂.2.1]; exact hcorr₁.trans hcorr
        | some im =>
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff, HState.removeFromTransit] at hr₂
          rw [hr₂.2.1]; exact hcorr₁.trans hcorr
  · change (r, s') ∈ support
        ((injectH ae G maxSkip (hpIdeal N true) (DG G) none q_ij).run s) at hmem
    exact (injectH_hpIdeal_uncorr_not_accepted ae G maxSkip N true q_ij s s' hcorr hmem).1

theorem evalDist_fst_eq_zero_of_support_false {β : Type} {m : ProbComp (Bool × β)}
    (h : ∀ z ∈ support m, z.1 = false) :
    𝒟[Prod.fst <$> m] {true} = 0 := by
  rw [map_eq_bind_pure_comp]
  exact evalDist_bind_eq_zero m (fun z => pure z.1) fun z hz => by
    simp [h z hz]

theorem multiSessEndWinProb_eq_zero_of_hpIdeal_gen
    {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B qR : ℕ) (AdvPub : Bool → MultiSessPubFsAdv Pt ℓ) (la : Bool)
    (hqb : ∀ la' s,
      (AdvPub la').IsQueryBoundP (fun t => sessQueryAt s t = true) B)
    (hqR : B ≤ qR)
    (hsupp : ∀ z ∈ support
      ((simulateQ (sessLift (lazyInit fsInit (fsImpl
          (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf)
          (lChainPRG C.F) maxForwardJumps
          (hpIdeal (authHopCutoff maxForwardJumps qR la) la))))
        (multiSessPubToAD protoSignalCodec (AdvPub la))).run (fun _ => none)),
      z.1 = false) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' => multiSessPubToAD protoSignalCodec (AdvPub la')) la = 0 := by
  unfold multiSessEndWinProb
  dsimp only
  have hqbAd : ∀ s,
      (multiSessPubToAD protoSignalCodec (AdvPub la)).IsQueryBoundP
        (fun t => sessQueryAt s t = true) B :=
    fun s => multiSessPubToAD_isQueryBoundP_sessQueryAt protoSignalCodec (AdvPub la)
      s B (hqb la s)
  cases la with
  | false =>
    have hCut : ∀ (_ : ℕ), B ≤ authHopCutoff maxForwardJumps qR false := by
      intro _; simpa [authHopCutoff] using hqR
    have hEq := (allSessions_hp_eq_hpIdeal_main
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps
      (multiSessPubToAD protoSignalCodec (AdvPub false))
      (fun _ => B) hqbAd hCut).1
    rw [hEq]
    exact evalDist_fst_eq_zero_of_support_false hsupp
  | true =>
    have hCut : ∀ (_ : ℕ),
        B + (maxForwardJumps + 1) ≤ authHopCutoff maxForwardJumps qR true := by
      intro _; simp only [authHopCutoff, ↓reduceIte]; omega
    have hEq := (allSessions_hp_eq_hpIdeal_la
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps
      (multiSessPubToAD protoSignalCodec (AdvPub true))
      (fun _ => B) hqbAd hCut).1
    rw [hEq]
    exact evalDist_fst_eq_zero_of_support_false hsupp

theorem multiSessEndWinProb_eq_zero_of_hpIdeal
    {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q qR : ℕ) (AdvPub : Bool → MultiSessPubFsAdv Pt ℓ) (la : Bool)
    (hqb : ∀ la' s,
      (AdvPub la').IsQueryBoundP (fun t => sessQueryAt s t = true) (2 * q))
    (hqR : 2 * q ≤ qR)
    (hsupp : ∀ z ∈ support
      ((simulateQ (sessLift (lazyInit fsInit (fsImpl
          (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf)
          (lChainPRG C.F) maxForwardJumps
          (hpIdeal (authHopCutoff maxForwardJumps qR la) la))))
        (multiSessPubToAD protoSignalCodec (AdvPub la))).run (fun _ => none)),
      z.1 = false) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' => multiSessPubToAD protoSignalCodec (AdvPub la')) la = 0 :=
  multiSessEndWinProb_eq_zero_of_hpIdeal_gen C ℓ encT idOf (2 * q) qR AdvPub la hqb hqR hsupp

section IdealPubRunner

abbrev IdealHSt (Pt : Type) (ℓ : ℕ) :=
  HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
    (Plain ℓ) LibsignalCiphertextWithSalt32

abbrev PubMultiSpec (Pt : Type) (ℓ : ℕ) :=
  unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
    (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32)

@[expose] def pubMultiTag {Pt : Type} {ℓ : ℕ} (s : ℕ) : QueryImpl
    (unifSpec + fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)))
  | .inl n => query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inl n)
  | .inr q => query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inr ⟨s, q⟩)

@[expose] def pubMultiImpl {Pt : Type} {ℓ : ℕ} : QueryImpl
    (PubMultiSpec Pt ℓ)
    (StateT (ℕ → Bool) (OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32))))
  | .inl n => StateT.lift (query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inl n))
  | .inr ⟨s, q⟩ => StateT.mk fun st => do
      let r ← simulateQ (pubMultiTag s)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2) (.inr q)).run (st s))
      return (r.1, Function.update st s r.2)

abbrev idealSessImpl {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) :=
  sessLift (lazyInit fsInit (fsImpl
    (lIdeal C protoSignalCodec ℓ encT)
    (lAeadR C protoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) maxForwardJumps
    (hpIdeal N la)))

abbrev runPubIdeal {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) {α : Type}
    (x : OracleComp (PubMultiSpec Pt ℓ) α)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ProbComp ((α × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ))) :=
  (simulateQ (idealSessImpl C ℓ encT idOf N la)
    ((simulateQ pubMultiImpl x).run rc)).run σ

theorem multiSessPubToAD_support_of_runPubIdeal {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (AdvPub : MultiSessPubFsAdv Pt ℓ)
    (h : ∀ w ∈ support (runPubIdeal C ℓ encT idOf N la AdvPub (fun _ => false) (fun _ => none)),
      w.1.1 = false) :
    ∀ z ∈ support
      ((simulateQ (idealSessImpl C ℓ encT idOf N la)
        (multiSessPubToAD protoSignalCodec AdvPub)).run (fun _ => none)),
      z.1 = false := by
  intro z hz
  change z ∈ support
    ((simulateQ (idealSessImpl C ℓ encT idOf N la)
      ((simulateQ pubMultiImpl AdvPub).run' (fun _ => false))).run
      (fun _ => none)) at hz
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, map_eq_bind_pure_comp,
    MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hzw⟩
  simp only [Function.comp, support_pure, Set.mem_singleton_iff] at hzw
  subst hzw
  exact h w hw

@[expose] def LaRouterInv {Pt : Type} {ℓ : ℕ} (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  ∀ s st, σ s = some st → st.1.senderCorruptedAt = none

@[expose] def PubLaSafe {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    {α : Type} (P : α → Prop) (x : OracleComp (PubMultiSpec Pt ℓ) α) : Prop :=
  ∀ rc σ, LaRouterInv σ →
    ∀ z ∈ support (runPubIdeal C ℓ encT idOf N true x rc σ),
      P z.1.1 ∧ LaRouterInv z.2

theorem PubLaSafe.pure {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {α : Type} {P : α → Prop} {a : α} (ha : P a) :
    PubLaSafe C ℓ encT idOf N P (pure a) := by
  intro rc σ hσ z hz
  simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨ha, hσ⟩

theorem PubLaSafe.mono {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {α : Type} {P Q : α → Prop} {x : OracleComp (PubMultiSpec Pt ℓ) α}
    (hx : PubLaSafe C ℓ encT idOf N P x) (hPQ : ∀ a, P a → Q a) :
    PubLaSafe C ℓ encT idOf N Q x :=
  fun rc σ hσ z hz => ⟨hPQ z.1.1 (hx rc σ hσ z hz).1, (hx rc σ hσ z hz).2⟩

theorem PubLaSafe.bind {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {α β : Type} {P : α → Prop} {Q : β → Prop}
    {x : OracleComp (PubMultiSpec Pt ℓ) α} {f : α → OracleComp (PubMultiSpec Pt ℓ) β}
    (hx : PubLaSafe C ℓ encT idOf N P x)
    (hf : ∀ a, P a → PubLaSafe C ℓ encT idOf N Q (f a)) :
    PubLaSafe C ℓ encT idOf N Q (x >>= f) := by
  intro rc σ hσ z hz
  simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hzw⟩
  rcases hx rc σ hσ w hw with ⟨hwa, hwσ⟩
  exact hf w.1.1 hwa w.1.2 w.2 hwσ z hzw

theorem lazyInit_hpIdeal_true_step {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N s₀ : ℕ)
    (q : (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (σ : ℕ → Option (IdealHSt Pt ℓ)) (hσ : LaRouterInv σ)
    {w : (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32).Range q × Option (IdealHSt Pt ℓ)}
    (hw : w ∈ support
      ((lazyInit fsInit (fsImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps
        (hpIdeal N true)) q).run (σ s₀))) :
    LaRouterInv (Function.update σ s₀ w.2) := by
  intro s st hst
  by_cases hss : s = s₀
  · subst hss
    rw [Function.update_self] at hst
    cases hσ0 : σ s with
    | none =>
      rw [hσ0] at hw
      simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hw
      rcases hw with ⟨b, _, z, hz, rfl⟩
      injection hst with hst_eq
      subst hst_eq
      exact fsImpl_hpIdeal_true_step _ _ _ maxForwardJumps N q
        (hInit b .unknown) z.2 rfl hz
      | some st₀ =>
      rw [hσ0] at hw
      rw [lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hw
      rcases hw with ⟨z, hz, hzw⟩
      rw [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hzw
      subst hzw
      injection hst with hst_eq
      subst hst_eq
      exact fsImpl_hpIdeal_true_step _ _ _ maxForwardJumps N q
        st₀ z.2 (hσ s st₀ hσ0) hz
  · rw [Function.update_of_ne hss] at hst
    exact hσ s st hst

abbrev idealLazyImpl {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) :=
  lazyInit fsInit (fsImpl
    (lIdeal C protoSignalCodec ℓ encT)
    (lAeadR C protoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) maxForwardJumps
    (hpIdeal N la))

theorem lift_inr_query_eq {ι₁ ι₂ : Type}
    {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} (q₀ : s₂.Domain) :
    (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₂.Range q₀)) =
      liftM (OracleSpec.query (spec := s₁ + s₂) (Sum.inr q₀)) := rfl

theorem liftFSMulti_run_query_eq {Pt Sig K I : Type} {ℓ : ℕ} (sIdx : ℕ)
    (q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (h : FSMultiState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32)) :
    ((liftFSMulti
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
      (E := ℕ × LibsignalCiphertextWithSalt32)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
    (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
  rw [lift_inr_query_eq]
  simp [liftFSMulti, StateT.run_lift]

theorem liftFSMultiDFBucket_run_query_eq {Pt Sig K I : Type} {ℓ : ℕ} (sIdx : ℕ)
    (q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (h : FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32)) :
    ((liftFSMultiDFBucket
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
      (E := ℕ × LibsignalCiphertextWithSalt32)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
    (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
  rw [lift_inr_query_eq]
  simp [liftFSMultiDFBucket, StateT.run_lift]

theorem run_idealSessImpl_pubMultiTag_inr {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (s₀ : ℕ)
    (q : (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    (simulateQ (idealSessImpl C ℓ encT idOf N la) (pubMultiTag s₀ (.inr q))).run σ =
    ((fun r => (r.1, Function.update σ s₀ r.2)) <$>
      (idealLazyImpl C ℓ encT idOf N la q).run (σ s₀)) := by
  dsimp only [pubMultiTag, idealSessImpl, idealLazyImpl]
  erw [query_eq_liftM, OracleSpec.query_def, simulateQ_query]
  change ((sessLift (idealLazyImpl C ℓ encT idOf N la) (Sum.inr ⟨s₀, q⟩)).run σ >>=
    pure ∘ fun a => (a.1, a.2)) = _
  simp [idealLazyImpl, sessLift_inr, sessLiftCore, map_eq_bind_pure_comp]

theorem runPubIdeal_query_inr_eq {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (sIdx : ℕ)
    (q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    {HS : Type} (hs : HS) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    runPubIdeal C ℓ encT idOf N la
      (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, hs)) rc σ =
    (((simulateQ (idealSessImpl C ℓ encT idOf N la)
        (simulateQ (pubMultiTag sIdx)
          ((_root_.CryptoGames.FSAEAD.pubRedImpl
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (AD := Header Pt) (M := Plain ℓ)
            (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
            (.inr q₀)).run (rc sIdx)))).run σ) >>= fun v =>
      pure (((v.1.1, hs), Function.update rc sIdx v.1.2), v.2)) := by
  unfold runPubIdeal
  rw [query_eq_liftM, simulateQ_query_bind]
  dsimp only [pubMultiImpl, OracleQuery.input_query, OracleQuery.cont_query]
  simp [StateT.run_mk, map_eq_bind_pure_comp]

theorem pubTag_tr_eq {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (s₀ : ℕ) (hdr : Header Pt)
    (pm : LibsignalMsgPublicPart × Plain ℓ) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la)
      (simulateQ (pubMultiTag s₀)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
          (.inr (.inl (.inl (.inl (.inl (.inl (hdr, pm)))))))).run b))).run σ) =
    (((idealLazyImpl C ℓ encT idOf N la
      (.inl (.inl (.inl (.inl (.inl ((hdr, pm.1), pm.2))))))).run (σ s₀)) >>= fun w =>
      pure ((w.1, b), Function.update σ s₀ w.2)) := by
  simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.transmitQuery,
    StateT.run_lift, map_eq_bind_pure_comp]
  erw [run_idealSessImpl_pubMultiTag_inr]
  simp [map_eq_bind_pure_comp]

theorem pubTag_ch_eq {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (s₀ : ℕ) (hdr : Header Pt)
    (pm₀ pm₁ : LibsignalMsgPublicPart × Plain ℓ) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la)
      (simulateQ (pubMultiTag s₀)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
          (.inr (.inl (.inl (.inl (.inl (.inr (hdr, pm₀, pm₁)))))))).run b))).run σ) =
    (((idealLazyImpl C ℓ encT idOf N la
      (.inl (.inl (.inl (.inl (.inr ((hdr, pm₀.1), pm₀.2, pm₁.2))))))).run (σ s₀)) >>= fun w =>
      pure ((w.1, b), Function.update σ s₀ w.2)) := by
  simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.challengeQuery,
    StateT.run_lift, map_eq_bind_pure_comp]
  erw [run_idealSessImpl_pubMultiTag_inr]
  simp [map_eq_bind_pure_comp]

theorem pubTag_cs_eq {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (s₀ : ℕ) (u : Unit) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la)
      (simulateQ (pubMultiTag s₀)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
          (.inr (.inl (.inl (.inl (.inr u)))))).run b))).run σ) =
    (((idealLazyImpl C ℓ encT idOf N la
      (.inl (.inl (.inl (.inr ()))))).run (σ s₀)) >>= fun w =>
      pure ((w.1, b), Function.update σ s₀ w.2)) := by
  simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.corruptSenderQuery,
    StateT.run_lift, map_eq_bind_pure_comp]
  erw [run_idealSessImpl_pubMultiTag_inr]
  simp [map_eq_bind_pure_comp]

theorem pubTag_cr_eq {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (s₀ : ℕ) (u : Unit) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la)
      (simulateQ (pubMultiTag s₀)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
          (.inr (.inl (.inl (.inr u))))).run b))).run σ) =
    (((idealLazyImpl C ℓ encT idOf N la
      (.inl (.inl (.inr ())))).run (σ s₀)) >>= fun w =>
      pure ((w.1, if w.1.isSome then true else b), Function.update σ s₀ w.2)) := by
  simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.corruptReceiverQuery,
    StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp]
  erw [run_idealSessImpl_pubMultiTag_inr]
  simp [map_eq_bind_pure_comp]
  refine bind_congr fun ⟨w₁, w₂⟩ => ?_
  change Option _ at w₁
  cases w₁ <;> simp [StateT.run_set]

theorem pubTag_dl_eq {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (s₀ : ℕ) (hdr : Header Pt)
    (e : ℕ × LibsignalCiphertextWithSalt32) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la)
      (simulateQ (pubMultiTag s₀)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
          (.inr (.inl (.inr (hdr, e))))).run b))).run σ) =
    match lPubOf protoSignalCodec e.2 with
    | none => pure ((none, b), σ)
    | some p =>
      (((idealLazyImpl C ℓ encT idOf N la (.inl (.inr ((hdr, p), e)))).run (σ s₀)) >>= fun w =>
        pure ((w.1.map (_root_.CryptoGames.FSAEAD.withPub p), b), Function.update σ s₀ w.2)) := by
  cases hpub : lPubOf protoSignalCodec e.2
  · simp [_root_.CryptoGames.FSAEAD.pubRedImpl, hpub]
  · simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.deliverQuery, hpub,
      StateT.run_lift, map_eq_bind_pure_comp]
    erw [run_idealSessImpl_pubMultiTag_inr]
    simp [map_eq_bind_pure_comp]

theorem pubTag_ij_eq {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (s₀ : ℕ) (hdr : Header Pt)
    (e : ℕ × LibsignalCiphertextWithSalt32) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la)
      (simulateQ (pubMultiTag s₀)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
          (.inr (.inr (hdr, e)))).run b))).run σ) =
    match lPubOf protoSignalCodec e.2 with
    | none => pure (((if b then none else some .rejected), b), σ)
    | some p =>
      (((idealLazyImpl C ℓ encT idOf N la (.inr ((hdr, p), e))).run (σ s₀)) >>= fun w =>
        pure ((w.1.map (_root_.CryptoGames.FSAEAD.withPub p), b), Function.update σ s₀ w.2)) := by
  cases hpub : lPubOf protoSignalCodec e.2
  · simp [_root_.CryptoGames.FSAEAD.pubRedImpl, hpub, StateT.run_map, StateT.run_get]
  · simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.injectQuery, hpub,
      StateT.run_lift, map_eq_bind_pure_comp]
    erw [run_idealSessImpl_pubMultiTag_inr]
    simp [map_eq_bind_pure_comp]

theorem pubStep_la_preserves {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N s₀ : ℕ)
    (q : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) (hσ : LaRouterInv σ)
    {v : ((fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Range q × Bool) ×
      (ℕ → Option (IdealHSt Pt ℓ))}
    (hv : v ∈ support ((simulateQ (idealSessImpl C ℓ encT idOf N true)
      (simulateQ (pubMultiTag s₀)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
          (.inr q)).run b))).run σ)) :
    LaRouterInv v.2 := by
  rcases q with ((((⟨hdr, pm⟩ | ⟨hdr, pm₀, pm₁⟩) | u) | u) | ⟨hdr, e⟩) | ⟨hdr, e⟩
  · rw [pubTag_tr_eq] at hv
    rw [MonadAttach.mem_support_bind] at hv
    rcases hv with ⟨w, hw, hvw⟩
    rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
    exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_ch_eq] at hv
    rw [MonadAttach.mem_support_bind] at hv
    rcases hv with ⟨w, hw, hvw⟩
    rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
    exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_cs_eq] at hv
    rw [MonadAttach.mem_support_bind] at hv
    rcases hv with ⟨w, hw, hvw⟩
    rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
    exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_cr_eq] at hv
    rw [MonadAttach.mem_support_bind] at hv
    rcases hv with ⟨w, hw, hvw⟩
    rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
    exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_dl_eq] at hv
    cases hpub : lPubOf protoSignalCodec e.2 with
    | none =>
      rw [hpub, support_pure, Set.mem_singleton_iff] at hv; subst hv; exact hσ
    | some p =>
      rw [hpub, MonadAttach.mem_support_bind] at hv
      rcases hv with ⟨w, hw, hvw⟩
      rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
      exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_ij_eq] at hv
    cases hpub : lPubOf protoSignalCodec e.2 with
    | none =>
      rw [hpub, support_pure, Set.mem_singleton_iff] at hv; subst hv; exact hσ
    | some p =>
      rw [hpub, MonadAttach.mem_support_bind] at hv
      rcases hv with ⟨w, hw, hvw⟩
      rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
      exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw

theorem PubLaSafe.any {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    {α : Type} (x : OracleComp (PubMultiSpec Pt ℓ) α) :
    PubLaSafe C ℓ encT idOf N (fun _ => True) x := by
  induction x using OracleComp.inductionOn with
  | pure a => exact PubLaSafe.pure trivial
  | query_bind t r ih =>
    intro rc σ hσ z hz
    rcases t with n | ⟨s₀, q⟩
    · simp only [runPubIdeal, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, pubMultiImpl, StateT.run_bind, stateT_lift_run,
        simulateQ_HasQuery_query, idealSessImpl, sessLift_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨u, _, hzu⟩
      exact ih u rc σ hσ z hzu
    · simp only [runPubIdeal, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, pubMultiImpl, StateT.run_bind, StateT.run_mk] at hz
      simp only [simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨v, hv, hzv⟩
      have hσ' := pubStep_la_preserves C ℓ encT idOf N s₀ q (rc s₀) σ hσ hv
      exact ih v.1.1 (Function.update rc s₀ v.1.2) v.2 hσ' z hzv

theorem pubQuery_inject_not_accepted_la {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N sIdx : ℕ)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32) {HS : Type} (hs : HS) :
    PubLaSafe C ℓ encT idOf N
      (fun p => p.2 = hs ∧ ∀ i mo', p.1 ≠ some (.accepted i mo'))
      (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, .inr (hdr, e)⟩) >>=
        fun a => pure (a, hs)) := by
  intro rc σ hσ z hz
  erw [runPubIdeal_query_inr_eq, pubTag_ij_eq] at hz
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    erw [hpub, pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨⟨rfl, fun i mo' hacc => ?_⟩, hσ⟩
    cases rc sIdx <;> simp at hacc
  | some p =>
    erw [hpub, bind_assoc, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨w, hw, hzw⟩
    erw [pure_bind, support_pure, Set.mem_singleton_iff] at hzw
    subst hzw
    have hσ' := lazyInit_hpIdeal_true_step C ℓ encT idOf N sIdx (.inr ((hdr, p), e)) σ hσ hw
    have hnotacc : ∀ i mo₀, w.1 ≠ some (.accepted i mo₀) := by
      cases hσ0 : σ sIdx with
      | none =>
        rw [hσ0] at hw
        simp only [idealLazyImpl, lazyInit_run_none', fsInit, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hw
        rcases hw with ⟨b, _, u, hu, rfl⟩
        change (u.1, u.2) ∈ support
          ((injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hpIdeal N true) (DG (lChainPRG C.F)) none ((hdr, p), e)).run (hInit b .unknown)) at hu
        exact (injectH_hpIdeal_uncorr_not_accepted _ _ maxForwardJumps N true
          ((hdr, p), e) (hInit b .unknown) u.2 rfl hu).2
      | some st₀ =>
        rw [hσ0] at hw
        rw [idealLazyImpl, lazyInit_run_some', map_eq_bind_pure_comp,
          MonadAttach.mem_support_bind] at hw
        rcases hw with ⟨u, hu, hwu⟩
        rw [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hwu
        subst hwu
        change (u.1, u.2) ∈ support
          ((injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hpIdeal N true) (DG (lChainPRG C.F)) none ((hdr, p), e)).run st₀) at hu
        exact (injectH_hpIdeal_uncorr_not_accepted _ _ maxForwardJumps N true
          ((hdr, p), e) st₀ u.2 (hσ sIdx st₀ hσ0) hu).2
    refine ⟨⟨rfl, fun i mo' hacc => ?_⟩, hσ'⟩
    cases hw1 : w.1 with
    | none => simp [hw1] at hacc
    | some rr =>
      cases rr with
      | rejected => simp [hw1, _root_.CryptoGames.FSAEAD.withPub] at hacc
      | accepted idx mo0 => exact hnotacc idx mo0 hw1

end IdealPubRunner


end

end Computational.Proofs.E2E.SessionAuthMultiEnd

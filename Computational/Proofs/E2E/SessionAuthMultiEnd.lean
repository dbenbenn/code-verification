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
public import Computational.Proofs.E2E.SessionAuthMultiEndBase -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiEndPaper -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiEndBucket -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthMultiPot
import Computational.Proofs.E2E.SessionAuthWireEnd
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions

/-!
# Multi-Session Ideal-Cutoff (`multiSessEndWinProb = 0`) Proofs for `DeliverForgePaper`

Proves that at the ideal FS-AEAD hopping endpoint (`Thm5.hp cut cut la`, with
`cut = authHopCutoff maxForwardJumps qR la` and `min (2 * q) (q + 2) ≤ qR`), all three
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
open Computational.Proofs.E2E.SessionAuthMultiPot (
  redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP
  redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP_min
  redFSAuthDFPaperMulti_sess_isQueryBoundP
  redFSAuthDFPaperMultiBucket_sess_isQueryBoundP)
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


open _root_.CryptoGames.FSAEAD (ReceiveResult withPub)
open _root_.CryptoGames.FSAEAD.Thm5 (Slot)
open _root_.CryptoGames.SM (Config GameState Pos Record healedBy)
open _root_.CryptoGames.SM.Construction (PartyState mkParties)
open _root_.CryptoGames.SM.Engine (Ctx Policy)
set_option linter.unusedSimpArgs false

section SharedIdealStepLemmas

private theorem senderKey_fst_eq {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    (G : ℕ → PRGScheme CK (CK × MK))
    (s s' : HSt CK MK AD M C) {w : CK}
    (hmem : (w, s') ∈ support
      ((_root_.CryptoGames.FSAEAD.Thm5.senderKey G : StateT (HSt CK MK AD M C) ProbComp CK).run s)) :
    s'.1 = s.1 :=
  mem_support_senderKey G hmem

private theorem receiveH_hpIdeal_main_props {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip N : ℕ) (hint : Option M) (a : AD) (c : ℕ × C)
    (s s' : HSt CK MK AD M C) {r : Option (ℕ × M)}
    (hmem : (r, s') ∈ support
      ((receiveH ae G maxSkip (hpIdeal N false) (DG G)
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp))
        hint a c).run s)) :
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
    (∀ i' m', r = some (i', m') →
      i' = c.1 ∧ (hint = none → ∃ c₀, s.1.senderCorruptedAt = some c₀ ∧ c₀ < i')) := by
  rcases c with ⟨i, e⟩
  unfold receiveH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨m?, s₁⟩, hd, hm⟩
    have hs₁ := (_root_.CryptoGames.FSAEAD.Thm5.Ends.mem_support_decIdx ae hd).1
    cases m? with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hm
      rcases hm with ⟨rfl, hs'1, _⟩
      rw [hs'1, hs₁]
      exact ⟨rfl, rfl, fun _ _ h => nomatch h⟩
    | some msg =>
      simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff] at hm
      rcases hm with ⟨hr, hs'1, _⟩
      refine ⟨by rw [hs'1, hs₁], by rw [hs'1, hs₁], fun i' m' hEq => ?_⟩
      rw [hr] at hEq
      injection hEq with hEq'
      injection hEq' with hi' _
      subst hi'
      refine ⟨rfl, fun hhint => ?_⟩
      subst hhint
      cases hc : s.1.isCompromised i with
      | false =>
        rw [decIdx_hpIdeal_none ae N false i a e s hc, support_pure,
          Set.mem_singleton_iff, Prod.ext_iff] at hd
        exact nomatch hd.1
      | true =>
        cases hsc : s.1.senderCorruptedAt with
        | none => simp [HState.isCompromised, hsc] at hc
        | some c₀ =>
          simp only [HState.isCompromised, hsc, decide_eq_true_eq] at hc
          exact ⟨c₀, rfl, hc⟩
  · split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rcases hmem with ⟨rfl, hs'1, _⟩
      rw [hs'1]
      exact ⟨rfl, rfl, fun _ _ h => nomatch h⟩
    · split at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rcases hmem with ⟨rfl, hs'1, _⟩
        rw [hs'1]
        exact ⟨rfl, rfl, fun _ _ h => nomatch h⟩
      · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨⟨_, s₁⟩, hg, hmem⟩
        rcases mem_support_genUpTo G hg with ⟨ks, hks⟩
        rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨⟨m?, s₂⟩, hd, hm⟩
        have hs₂ := (_root_.CryptoGames.FSAEAD.Thm5.Ends.mem_support_decIdx ae hd).1
        cases m? with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hm
          rcases hm with ⟨rfl, hs'1, _⟩
          rw [hs'1, hs₂, hks]
          exact ⟨rfl, rfl, fun _ _ h => nomatch h⟩
        | some msg =>
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at hm
          rcases hm with ⟨hr, hs'1, _⟩
          refine ⟨by rw [hs'1, hs₂, hks], by rw [hs'1, hs₂, hks], fun i' m' hEq => ?_⟩
          rw [hr] at hEq
          injection hEq with hEq'
          injection hEq' with hi' _
          subst hi'
          refine ⟨rfl, fun hhint => ?_⟩
          subst hhint
          cases hc : s.1.isCompromised i with
          | false =>
            have hc₁ : s₁.1.isCompromised i = false := by
              rw [hks]; simpa [HState.isCompromised] using hc
            rw [decIdx_hpIdeal_none ae N false i a e s₁ hc₁, support_pure,
              Set.mem_singleton_iff, Prod.ext_iff] at hd
            exact nomatch hd.1
          | true =>
            cases hsc : s.1.senderCorruptedAt with
            | none => simp [HState.isCompromised, hsc] at hc
            | some c₀ =>
              simp only [HState.isCompromised, hsc, decide_eq_true_eq] at hc
              exact ⟨c₀, rfl, hc⟩

private theorem transmitHWith_hpIdeal_main_props {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C)
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK))
    (N : ℕ) (q : AD × M) (s s' : HSt CK MK AD M C) {r : Option (ℕ × C)}
    (hmem : (r, s') ∈ support
      ((transmitHWith ideal ae G (hpIdeal N false) (DG G)
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) q).run s)) :
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
    ((r = none ∧ s'.1.lastSentIdx = s.1.lastSentIdx) ∨
      (∃ e, r = some e ∧ e.1 = s.1.lastSentIdx + 1 ∧ s'.1.lastSentIdx = s.1.lastSentIdx + 1)) := by
  unfold transmitHWith at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
    rcases hmem with ⟨rfl, hs'1, _⟩
    rw [hs'1]
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · simp only [StateT.run_bind, MonadAttach.mem_support_bind, modifyH_run, pure_bind,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
    rcases hmem with ⟨⟨_, s₁⟩, h₁, ⟨e_raw, s₂⟩, h₂, hr, hs'1, _⟩
    rcases mem_support_genUpTo G h₁ with ⟨ks, hks⟩
    have hs₂ := mem_support_encIdx ideal ae h₂
    refine ⟨by rw [hs'1, hs₂, hks], Or.inr ⟨(s.1.lastSentIdx + 1, e_raw), hr, rfl, ?_⟩⟩
    rw [hs'1]

private theorem corruptSenderH_hpIdeal_main_props {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (G : ℕ → PRGScheme CK (CK × MK))
    (N : ℕ) (u : Unit) (s s' : HSt CK MK AD M C)
    {r : Option (RatchetSenderState CK)}
    (hmem : (r, s') ∈ support
      ((corruptSenderH G (hpIdeal N false) u : StateT (HSt CK MK AD M C) ProbComp _).run s)) :
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    ((r = none ∧ s'.1.senderCorruptedAt = s.1.senderCorruptedAt) ∨
      (∃ ss, r = some ss ∧
        s'.1.senderCorruptedAt = some (s.1.senderCorruptedAt.getD s.1.lastSentIdx))) := by
  unfold corruptSenderH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
    rcases hmem with ⟨rfl, hs'1, _⟩
    rw [hs'1]
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · have hla : (hpIdeal N false).la = false := by simp [hpIdeal]
    simp only [hla, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      MonadAttach.mem_support_bind, modifyH_run, pure_bind, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
    rcases hmem with ⟨⟨w, s₁⟩, hw, hr, hs'1, _⟩
    have hs₁ := senderKey_fst_eq G s s₁ hw
    refine ⟨by rw [hs'1, hs₁], Or.inr ⟨⟨w, s.1.lastSentIdx⟩, hr, ?_⟩⟩
    rw [hs'1]

private theorem deliverH_hpIdeal_main_props {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip N : ℕ) (q : AD × (ℕ × C)) (s s' : HSt CK MK AD M C)
    {r : Option (_root_.CryptoGames.FSAEAD.ReceiveResult M)}
    (hmem : (r, s') ∈ support
      ((deliverH ae G maxSkip (hpIdeal N false) (DG G)
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) q).run s)) :
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
    (∀ i' mo', r = some (.accepted i' mo') → i' = q.2.1) := by
  unfold deliverH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
    rcases hmem with ⟨rfl, hs'1, _⟩
    rw [hs'1]
    exact ⟨rfl, rfl, fun _ _ h => nomatch h⟩
  · cases hfind : s.1.inTransit.find? (fun rec => rec.ad == q.1 && rec.ct == q.2) with
    | none =>
      simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rcases hmem with ⟨rfl, hs'1, _⟩
      rw [hs'1]
      exact ⟨rfl, rfl, fun _ _ h => nomatch h⟩
    | some rec =>
      simp only [hfind, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨⟨ro, s₁⟩, hr₁, hr₂⟩
      rcases receiveH_hpIdeal_main_props ae G maxSkip N (some rec.msg) q.1 q.2 s s₁ hr₁ with
        ⟨hlast₁, hcorr₁, hacc₁⟩
      cases ro with
      | none =>
        simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.ext_iff] at hr₂
        rcases hr₂ with ⟨rfl, hs'1, _⟩
        rw [hs'1]
        exact ⟨hlast₁, hcorr₁, fun _ _ h => nomatch h⟩
      | some im =>
        simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.ext_iff, HState.removeFromTransit] at hr₂
        rcases hr₂ with ⟨hr, hs'1, _⟩
        refine ⟨by rw [hs'1]; exact hlast₁, by rw [hs'1]; exact hcorr₁, fun i' mo' hEq => ?_⟩
        rw [hr] at hEq
        injection hEq with hEq'
        injection hEq' with hi' _
        subst hi'
        exact (hacc₁ im.1 im.2 rfl).1

private theorem injectH_hpIdeal_main_props {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip N : ℕ) (q : AD × (ℕ × C)) (s s' : HSt CK MK AD M C)
    {r : Option (_root_.CryptoGames.FSAEAD.ReceiveResult M)}
    (hmem : (r, s') ∈ support
      ((injectH ae G maxSkip (hpIdeal N false) (DG G)
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) q).run s)) :
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
    (∀ i' mo', r = some (.accepted i' mo') →
      i' = q.2.1 ∧ ∃ c₀, s.1.senderCorruptedAt = some c₀ ∧ c₀ < i') := by
  unfold injectH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
    rcases hmem with ⟨rfl, hs'1, _⟩
    rw [hs'1]
    exact ⟨rfl, rfl, fun _ _ h => nomatch h⟩
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨ro, s₁⟩, hr₁, hr₂⟩
    rcases receiveH_hpIdeal_main_props ae G maxSkip N none q.1 q.2 s s₁ hr₁ with
      ⟨hlast₁, hcorr₁, hacc₁⟩
    cases ro with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₂
      rcases hr₂ with ⟨rfl, hs'1, _⟩
      rw [hs'1]
      exact ⟨hlast₁, hcorr₁, fun _ _ h => nomatch h⟩
    | some im =>
      simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff, HState.removeFromTransit] at hr₂
      rcases hr₂ with ⟨hr, hs'1, _⟩
      refine ⟨by rw [hs'1]; exact hlast₁, by rw [hs'1]; exact hcorr₁, fun i' mo' hEq => ?_⟩
      rw [hr] at hEq
      injection hEq with hEq'
      injection hEq' with hi' _
      subst hi'
      rcases hacc₁ im.1 im.2 rfl with ⟨him1, hcomp⟩
      exact ⟨him1, hcomp rfl⟩

private def sessLastIdx {Pt : Type} {ℓ : ℕ} (σ : ℕ → Option (IdealHSt Pt ℓ)) (sIdx : ℕ) : ℕ :=
  match σ sIdx with
  | none => 0
  | some st => st.1.lastSentIdx

private def sessCorrAt {Pt : Type} {ℓ : ℕ} (σ : ℕ → Option (IdealHSt Pt ℓ)) (sIdx : ℕ) :
    Option ℕ :=
  match σ sIdx with
  | none => none
  | some st => st.1.senderCorruptedAt

private theorem pubQuery_transmit_main {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N sIdx : ℕ)
    (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ) {HS : Type} (hs : HS)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    {z : (((Option (ℕ × LibsignalCiphertextWithSalt32)) × HS) × (ℕ → Bool)) ×
      (ℕ → Option (IdealHSt Pt ℓ))}
    (hz : z ∈ support (runPubIdeal C ℓ encT idOf N false
      (query (spec := PubMultiSpec Pt ℓ)
        (Sum.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl (hdr, pm)))))⟩) >>=
        fun a => pure (a, hs)) rc σ)) :
    z.1.1.2 = hs ∧
    ∃ st', z.2 = Function.update σ sIdx (some st') ∧
      st'.1.senderCorruptedAt = sessCorrAt σ sIdx ∧
      ((z.1.1.1 = none ∧ st'.1.lastSentIdx = sessLastIdx σ sIdx) ∨
        (∃ e, z.1.1.1 = some e ∧ e.1 = sessLastIdx σ sIdx + 1 ∧
          st'.1.lastSentIdx = sessLastIdx σ sIdx + 1)) := by
  rw [runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inl (.inl (.inl (.inl (.inl (hdr, pm)))))) hs rc σ,
    pubTag_tr_eq C ℓ encT idOf N false sIdx hdr pm (rc sIdx) σ] at hz
  simp only [bind_assoc, pure_bind] at hz
  change z ∈ support _ at hz
  rw [mem_support_bind_iff] at hz
  rcases hz with ⟨w, hw, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  refine ⟨rfl, ?_⟩
  cases hσ0 : σ sIdx with
  | none =>
    rw [hσ0] at hw
    simp only [idealLazyImpl, lazyInit_run_none', fsInit, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hw
    rcases hw with ⟨b, _, u, hu, rfl⟩
    change (u.1, u.2) ∈ support
      ((transmitHWith (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) (hpIdeal N false) (DG (lChainPRG C.F)) none
        ((hdr, pm.1), pm.2)).run (hInit b .unknown)) at hu
    rcases transmitHWith_hpIdeal_main_props _ _ _ N ((hdr, pm.1), pm.2)
      (hInit b .unknown) u.2 hu with ⟨hcorr, hres⟩
    refine ⟨u.2, rfl, ?_, ?_⟩
    · simpa [sessCorrAt, hσ0, hInit] using hcorr
    · simpa [sessLastIdx, hσ0, hInit] using hres
  | some st₀ =>
    rw [hσ0] at hw
    rw [idealLazyImpl, lazyInit_run_some', map_eq_bind_pure_comp,
      MonadAttach.mem_support_bind] at hw
    rcases hw with ⟨u, hu, hwu⟩
    rw [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hwu
    subst hwu
    change (u.1, u.2) ∈ support
      ((transmitHWith (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) (hpIdeal N false) (DG (lChainPRG C.F)) none
        ((hdr, pm.1), pm.2)).run st₀) at hu
    rcases transmitHWith_hpIdeal_main_props _ _ _ N ((hdr, pm.1), pm.2) st₀ u.2 hu with
      ⟨hcorr, hres⟩
    refine ⟨u.2, rfl, ?_, ?_⟩
    · simpa [sessCorrAt, hσ0] using hcorr
    · simpa [sessLastIdx, hσ0] using hres

private theorem pubQuery_corruptSender_main {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N sIdx : ℕ)
    {HS : Type} (hs : HS) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    {z : (((Option (RatchetSenderState (BitVec 256))) × HS) × (ℕ → Bool)) ×
      (ℕ → Option (IdealHSt Pt ℓ))}
    (hz : z ∈ support (runPubIdeal C ℓ encT idOf N false
      (query (spec := PubMultiSpec Pt ℓ)
        (Sum.inr ⟨sIdx, .inl (.inl (.inl (.inr ())))⟩) >>=
        fun a => pure (a, hs)) rc σ)) :
    z.1.1.2 = hs ∧
    ∃ st', z.2 = Function.update σ sIdx (some st') ∧
      st'.1.lastSentIdx = sessLastIdx σ sIdx ∧
      ((z.1.1.1 = none ∧ st'.1.senderCorruptedAt = sessCorrAt σ sIdx) ∨
        (∃ ss, z.1.1.1 = some ss ∧
          st'.1.senderCorruptedAt = some ((sessCorrAt σ sIdx).getD (sessLastIdx σ sIdx)))) := by
  rw [runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inl (.inl (.inl (.inr ())))) hs rc σ,
    pubTag_cs_eq C ℓ encT idOf N false sIdx () (rc sIdx) σ] at hz
  simp only [bind_assoc, pure_bind] at hz
  change z ∈ support _ at hz
  rw [mem_support_bind_iff] at hz
  rcases hz with ⟨w, hw, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  refine ⟨rfl, ?_⟩
  cases hσ0 : σ sIdx with
  | none =>
    rw [hσ0] at hw
    simp only [idealLazyImpl, lazyInit_run_none', fsInit, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hw
    rcases hw with ⟨b, _, u, hu, rfl⟩
    change (u.1, u.2) ∈ support
      ((corruptSenderH (lChainPRG C.F) (hpIdeal N false) ()).run (hInit b .unknown)) at hu
    rcases corruptSenderH_hpIdeal_main_props _ N () (hInit b .unknown) u.2 hu with ⟨hlast, hres⟩
    refine ⟨u.2, rfl, ?_, ?_⟩
    · simpa [sessLastIdx, hσ0, hInit] using hlast
    · simpa [sessCorrAt, sessLastIdx, hσ0, hInit] using hres
  | some st₀ =>
    rw [hσ0] at hw
    rw [idealLazyImpl, lazyInit_run_some', map_eq_bind_pure_comp,
      MonadAttach.mem_support_bind] at hw
    rcases hw with ⟨u, hu, hwu⟩
    rw [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hwu
    subst hwu
    change (u.1, u.2) ∈ support
      ((corruptSenderH (lChainPRG C.F) (hpIdeal N false) ()).run st₀) at hu
    rcases corruptSenderH_hpIdeal_main_props _ N () st₀ u.2 hu with ⟨hlast, hres⟩
    refine ⟨u.2, rfl, ?_, ?_⟩
    · simpa [sessLastIdx, hσ0] using hlast
    · simpa [sessCorrAt, sessLastIdx, hσ0] using hres

private theorem pubQuery_deliver_main {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N sIdx : ℕ)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32) {HS : Type} (hs : HS)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    {z : (((Option (_root_.CryptoGames.FSAEAD.ReceiveResult (LibsignalMsgPublicPart × Plain ℓ))) ×
      HS) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ))}
    (hz : z ∈ support (runPubIdeal C ℓ encT idOf N false
      (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, .inl (.inr (hdr, e))⟩) >>=
        fun a => pure (a, hs)) rc σ)) :
    z.1.1.2 = hs ∧
    ((z.1.1.1 = none ∧ z.2 = σ) ∨
      (∃ st', z.2 = Function.update σ sIdx (some st') ∧
        st'.1.lastSentIdx = sessLastIdx σ sIdx ∧
        st'.1.senderCorruptedAt = sessCorrAt σ sIdx ∧
        (∀ i' mo', z.1.1.1 = some (.accepted i' mo') → i' = e.1))) := by
  rw [runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inl (.inr (hdr, e))) hs rc σ,
    pubTag_dl_eq C ℓ encT idOf N false sIdx hdr e (rc sIdx) σ] at hz
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    simp only [hpub, pure_bind] at hz
    change z ∈ support _ at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | some p =>
    simp only [hpub, bind_assoc, pure_bind] at hz
    change z ∈ support _ at hz
    rw [mem_support_bind_iff] at hz
    rcases hz with ⟨w, hw, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨rfl, Or.inr ?_⟩
    cases hσ0 : σ sIdx with
    | none =>
      rw [hσ0] at hw
      simp only [idealLazyImpl, lazyInit_run_none', fsInit, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hw
      rcases hw with ⟨b, _, u, hu, rfl⟩
      change (u.1, u.2) ∈ support
        ((deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false) (DG (lChainPRG C.F)) none ((hdr, p), e)).run (hInit b .unknown)) at hu
      rcases deliverH_hpIdeal_main_props _ _ maxForwardJumps N ((hdr, p), e)
        (hInit b .unknown) u.2 hu with ⟨hlast, hcorr, hacc⟩
      refine ⟨u.2, rfl, by simpa [sessLastIdx, hσ0, hInit] using hlast,
        by simpa [sessCorrAt, hσ0, hInit] using hcorr, fun i' mo' hEq => ?_⟩
      cases hu1 : u.1 with
      | none => simp [hu1] at hEq
      | some rr =>
        cases rr with
        | rejected => simp [hu1, _root_.CryptoGames.FSAEAD.withPub] at hEq
        | accepted idx mo0 =>
          simp only [hu1, Option.map_some, _root_.CryptoGames.FSAEAD.withPub, Option.some.injEq,
            _root_.CryptoGames.FSAEAD.ReceiveResult.accepted.injEq] at hEq
          exact hEq.1 ▸ hacc idx mo0 hu1
    | some st₀ =>
      rw [hσ0] at hw
      rw [idealLazyImpl, lazyInit_run_some', map_eq_bind_pure_comp,
        MonadAttach.mem_support_bind] at hw
      rcases hw with ⟨u, hu, hwu⟩
      rw [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hwu
      subst hwu
      change (u.1, u.2) ∈ support
        ((deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false) (DG (lChainPRG C.F)) none ((hdr, p), e)).run st₀) at hu
      rcases deliverH_hpIdeal_main_props _ _ maxForwardJumps N ((hdr, p), e) st₀ u.2 hu with
        ⟨hlast, hcorr, hacc⟩
      refine ⟨u.2, rfl, by simpa [sessLastIdx, hσ0] using hlast,
        by simpa [sessCorrAt, hσ0] using hcorr, fun i' mo' hEq => ?_⟩
      cases hu1 : u.1 with
      | none => simp [hu1] at hEq
      | some rr =>
        cases rr with
        | rejected => simp [hu1, _root_.CryptoGames.FSAEAD.withPub] at hEq
        | accepted idx mo0 =>
          simp only [hu1, Option.map_some, _root_.CryptoGames.FSAEAD.withPub, Option.some.injEq,
            _root_.CryptoGames.FSAEAD.ReceiveResult.accepted.injEq] at hEq
          exact hEq.1 ▸ hacc idx mo0 hu1

private theorem pubQuery_inject_main {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N sIdx : ℕ)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32) {HS : Type} (hs : HS)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    {z : (((Option (_root_.CryptoGames.FSAEAD.ReceiveResult (LibsignalMsgPublicPart × Plain ℓ))) ×
      HS) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ))}
    (hz : z ∈ support (runPubIdeal C ℓ encT idOf N false
      (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, .inr (hdr, e)⟩) >>=
        fun a => pure (a, hs)) rc σ)) :
    z.1.1.2 = hs ∧
    (((∀ i' mo', z.1.1.1 ≠ some (.accepted i' mo')) ∧ z.2 = σ) ∨
      (∃ st', z.2 = Function.update σ sIdx (some st') ∧
        st'.1.lastSentIdx = sessLastIdx σ sIdx ∧
        st'.1.senderCorruptedAt = sessCorrAt σ sIdx ∧
        (∀ i' mo', z.1.1.1 = some (.accepted i' mo') →
          i' = e.1 ∧ ∃ c₀, sessCorrAt σ sIdx = some c₀ ∧ c₀ < i'))) := by
  rw [runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inr (hdr, e)) hs rc σ,
    pubTag_ij_eq C ℓ encT idOf N false sIdx hdr e (rc sIdx) σ] at hz
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    simp only [hpub, pure_bind] at hz
    change z ∈ support _ at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨rfl, Or.inl ⟨fun i' mo' hacc => ?_, rfl⟩⟩
    cases rc sIdx <;> simp at hacc
  | some p =>
    simp only [hpub, bind_assoc, pure_bind] at hz
    change z ∈ support _ at hz
    rw [mem_support_bind_iff] at hz
    rcases hz with ⟨w, hw, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨rfl, Or.inr ?_⟩
    cases hσ0 : σ sIdx with
    | none =>
      rw [hσ0] at hw
      simp only [idealLazyImpl, lazyInit_run_none', fsInit, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hw
      rcases hw with ⟨b, _, u, hu, rfl⟩
      change (u.1, u.2) ∈ support
        ((injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false) (DG (lChainPRG C.F)) none ((hdr, p), e)).run (hInit b .unknown)) at hu
      rcases injectH_hpIdeal_main_props _ _ maxForwardJumps N ((hdr, p), e)
        (hInit b .unknown) u.2 hu with ⟨hlast, hcorr, hacc⟩
      refine ⟨u.2, rfl, by simpa [sessLastIdx, hσ0, hInit] using hlast,
        by simpa [sessCorrAt, hσ0, hInit] using hcorr, fun i' mo' hEq => ?_⟩
      cases hu1 : u.1 with
      | none => simp [hu1] at hEq
      | some rr =>
        cases rr with
        | rejected => simp [hu1, _root_.CryptoGames.FSAEAD.withPub] at hEq
        | accepted idx mo0 =>
          simp only [hu1, Option.map_some, _root_.CryptoGames.FSAEAD.withPub, Option.some.injEq,
            _root_.CryptoGames.FSAEAD.ReceiveResult.accepted.injEq] at hEq
          rcases hacc idx mo0 hu1 with ⟨_, c₀, hc₀, _⟩
          simp [hInit] at hc₀
    | some st₀ =>
      rw [hσ0] at hw
      rw [idealLazyImpl, lazyInit_run_some', map_eq_bind_pure_comp,
        MonadAttach.mem_support_bind] at hw
      rcases hw with ⟨u, hu, hwu⟩
      rw [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hwu
      subst hwu
      change (u.1, u.2) ∈ support
        ((injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false) (DG (lChainPRG C.F)) none ((hdr, p), e)).run st₀) at hu
      rcases injectH_hpIdeal_main_props _ _ maxForwardJumps N ((hdr, p), e) st₀ u.2 hu with
        ⟨hlast, hcorr, hacc⟩
      refine ⟨u.2, rfl, by simpa [sessLastIdx, hσ0] using hlast,
        by simpa [sessCorrAt, hσ0] using hcorr, fun i' mo' hEq => ?_⟩
      cases hu1 : u.1 with
      | none => simp [hu1] at hEq
      | some rr =>
        cases rr with
        | rejected => simp [hu1, _root_.CryptoGames.FSAEAD.withPub] at hEq
        | accepted idx mo0 =>
          simp only [hu1, Option.map_some, _root_.CryptoGames.FSAEAD.withPub, Option.some.injEq,
            _root_.CryptoGames.FSAEAD.ReceiveResult.accepted.injEq] at hEq
          rcases hacc idx mo0 hu1 with ⟨hidx, c₀, hc₀, hlt⟩
          rcases hEq with ⟨rfl, _⟩
          exact ⟨hidx, c₀, by simpa [sessCorrAt, hσ0] using hc₀, hlt⟩

end SharedIdealStepLemmas

-- ============================================================================
-- 2. Shared Lookahead (`la = true`) Proof for `hooksFSMulti` & `initFSMultiRaw`
-- ============================================================================

section HooksFSMultiLaSafe

attribute [local irreducible] PubLaSafe

private abbrev ShiftedFS (Pt : Type) [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :=
  lFS C protoSignalCodec ℓ encT idOf maxForwardJumps

private abbrev ShiftedHState (Pt RSt I : Type) :=
  FSMultiState Pt RSt (BitVec 256) I (ℕ × LibsignalCiphertextWithSalt32)

private abbrev ShiftedEState (Γ Pt RSt I : Type) (ℓ : ℕ) :=
  EState (VP Γ Pt RSt
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (LibsignalMsgPublicPart × Plain ℓ)
    (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (ShiftedHState Pt RSt I)

private theorem stateT_lift_la_safe {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    {HS β : Type} (m : OracleComp (PubMultiSpec Pt ℓ) β) (hs : HS) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2 = hs) ((StateT.lift m).run hs) := by
  rw [stateT_lift_run]
  exact (PubLaSafe.any C ℓ encT idOf N m).bind fun _ _ => PubLaSafe.pure rfl

private theorem lookupMultiF_la_safe {Pt RSt I : Type} [DecidableEq Pt] [DecidableEq I]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (Ik : I) (h : ShiftedHState Pt RSt I) (hlf : h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      ((lookupMultiF
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32) Ik).run h) := by
  unfold lookupMultiF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h.table.lookup Ik with
  | some k => exact PubLaSafe.pure hlf
  | none =>
    simp only [StateT.run_bind]
    refine (stateT_lift_la_safe C ℓ encT idOf N _ h).bind ?_
    rintro ⟨k, _⟩ rfl
    simp only [StateT.run_modify, pure_bind, StateT.run_pure]
    exact PubLaSafe.pure hlf

private theorem regSessMulti_la_safe {Pt RSt I : Type} [DecidableEq Pt] [DecidableEq I]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (Ik : I) (h : ShiftedHState Pt RSt I) (hlf : h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      ((regSessMulti
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32)
        (Sig := RSt) (K := BitVec 256) Ik).run h) := by
  unfold regSessMulti
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
    exact PubLaSafe.pure hlf

private theorem regSessOptMulti_la_safe {Pt RSt I : Type} [DecidableEq Pt] [DecidableEq I]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (sid : Option I) (h : ShiftedHState Pt RSt I) (hlf : h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      ((regSessOptMulti
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32)
        (Sig := RSt) (K := BitVec 256) sid).run h) := by
  cases sid with
  | none => exact PubLaSafe.pure hlf
  | some Ik =>
    simp only [regSessOptMulti, map_eq_bind_pure_comp]
    exact (regSessMulti_la_safe C ℓ encT idOf N Ik h hlf).bind fun p hp => PubLaSafe.pure hp

private theorem rootFSMulti_la_safe {Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType KR]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (mo : Mode) (t0 : ℕ) (Ik : I) (σr : RSt)
    (h : ShiftedHState Pt RSt I) (hlf : h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      ((rootFSMulti
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32) prng mo t0 Ik σr).run h) := by
  unfold rootFSMulti
  split_ifs
  · exact PubLaSafe.pure hlf
  · simp only [StateT.run_bind]
    refine (stateT_lift_la_safe C ℓ encT idOf N
      (_root_.CryptoGames.SM.Construction.sampleT I) h).bind ?_
    rintro ⟨Ir, h⟩ rfl
    refine (stateT_lift_la_safe C ℓ encT idOf N
      (_root_.CryptoGames.SM.Construction.sampleT (BitVec 256)) h).bind ?_
    rintro ⟨k, h⟩ rfl
    exact PubLaSafe.pure hlf
  · simp only [StateT.run_bind]
    refine (lookupMultiF_la_safe C ℓ encT idOf N Ik h hlf).bind fun ⟨k, h₁⟩ hh₁ => ?_
    exact PubLaSafe.pure hh₁
  · simp only [StateT.run_bind]
    refine (stateT_lift_la_safe C ℓ encT idOf N
      (_root_.CryptoGames.SM.Construction.sampleT I) h).bind ?_
    rintro ⟨Ir, h⟩ rfl
    exact PubLaSafe.pure hlf
  · exact PubLaSafe.pure hlf

private theorem initFSMultiRaw_la_safe {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType KR] [SampleableType KC]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (lam : I) (mo : Mode) (b : Bool) :
    PubLaSafe C ℓ encT idOf N (fun es => es.h.lfWin = false)
      (initFSMultiRaw cka prng (ShiftedFS Pt C ℓ encT idOf) lam mo b) := by
  unfold initFSMultiRaw
  refine (PubLaSafe.any C ℓ encT idOf N _).bind fun kr _ => ?_
  refine (PubLaSafe.any C ℓ encT idOf N _).bind fun kc _ => ?_
  refine (rootFSMulti_la_safe C ℓ encT idOf N prng mo 0 lam (prng.init kr) {} rfl).bind
    fun ⟨⟨σr, k, sid⟩, h₁⟩ hh₁ => ?_
  refine (regSessOptMulti_la_safe C ℓ encT idOf N sid h₁ hh₁).bind
    fun ⟨optIdx, h₂⟩ hh₂ => ?_
  exact PubLaSafe.pure hh₂

private theorem hooksFSMulti_fsRecv_la_safe {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka : ℕ) (mo : Mode) (gMain : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ Pt RSt
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (t0 : ℕ)
    (rsv : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec : Option (_root_.CryptoGames.SM.Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (h : ShiftedHState Pt RSt I) (hlf : h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      (((hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka mo gMain true).fsRecv
        ctx P t0 rsv hdr e rec).run h) := by
  dsimp only [hooksFSMulti]
  cases rsv with
  | inl rs => exact PubLaSafe.pure hlf
  | inr sIdx =>
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    generalize hm : List.find? _ _ = mf
    cases mf with
    | some x =>
      simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, pure_bind, Bool.not_true, Option.isSome_some]
      rw [show _root_.CryptoGames.FSAEAD.deliverQuery hdr e =
          liftM (OracleSpec.query (spec := fsSpec (BitVec 256) (BitVec 256) (Header Pt)
            (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32)
            (.inl (.inr (hdr, e)))) from rfl,
        liftFSMulti_run_query_eq]
      have hq : PubLaSafe C ℓ encT idOf N (fun p => p.2 = h)
          (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, .inl (.inr (hdr, e))⟩) >>=
            fun a => pure (a, h)) :=
        (PubLaSafe.any C ℓ encT idOf N _).bind fun _ _ => PubLaSafe.pure rfl
      refine hq.bind ?_
      rintro ⟨res, h⟩ rfl
      cases res with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | some rr =>
        cases rr with
        | rejected => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        | accepted i mo' =>
          simp only [StateT.run_bind, StateT.run_get, pure_bind,
            Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_modify]
          cases mo' <;> cases rec <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf)
    | none =>
      by_cases hlazy :
          (!_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t0 &&
            !(((h, h).1.book sIdx).getD {}).sCorr) = true
      · simp only [Option.isNone_none, Bool.true_and, hlazy, ↓reduceIte,
          StateT.run_pure, pure_bind, Bool.not_false]
        exact PubLaSafe.pure hlf
      · have hgf : (!_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t0 &&
            !(((h, h).1.book sIdx).getD {}).sCorr) = false := Bool.not_eq_true _ |>.mp hlazy
        simp only [Option.isNone_none, Bool.true_and, hgf, Option.isSome_none,
          Bool.false_eq_true, ↓reduceIte, StateT.run_bind, pure_bind, Bool.not_true]
        rw [show _root_.CryptoGames.FSAEAD.injectQuery hdr e =
            liftM (OracleSpec.query (spec := fsSpec (BitVec 256) (BitVec 256) (Header Pt)
              (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32)
              (.inr (hdr, e))) from rfl,
          liftFSMulti_run_query_eq]
        refine (pubQuery_inject_not_accepted_la C ℓ encT idOf N sIdx hdr e h).bind ?_
        rintro ⟨res, h⟩ ⟨rfl, hnotacc⟩
        cases res with
        | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        | some rr =>
          cases rr with
          | rejected => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
          | accepted i mo' => exact False.elim (hnotacc i mo' rfl)

private theorem vSend_hooksFSMulti_la_safe {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins] [SampleableType KR]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka : ℕ) (mo : Mode) (gMain : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ Pt RSt
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (vp : VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (m : LibsignalMsgPublicPart × Plain ℓ)
    (pair : Option ((LibsignalMsgPublicPart × Plain ℓ) × (LibsignalMsgPublicPart × Plain ℓ)))
    (r : Option CCoins)
    (h : ShiftedHState Pt RSt I) (hlf : h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      ((vSend (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka mo gMain true)
        ctx P vp m pair r).run h) := by
  have hstartSend : ∀ t0 γ σr (h₀ : ShiftedHState Pt RSt I), h₀.lfWin = false →
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka mo gMain true).startSend
          ctx P t0 γ σr r).run h₀) := by
    intro t0 γ σr h₀ hh₀
    dsimp only [hooksFSMulti]
    cases r with
    | some coins =>
      dsimp only
      simp only [pure_bind]
      rw [StateT.run_bind]
      refine (rootFSMulti_la_safe C ℓ encT idOf N prng mo t0
        (cka.send γ coins).2.2 σr h₀ hh₀).bind fun ⟨⟨σ', k, sid⟩, h₁⟩ hh₁ => ?_
      rw [StateT.run_bind]
      refine (regSessOptMulti_la_safe C ℓ encT idOf N sid h₁ hh₁).bind
        fun ⟨optIdx, h₂⟩ hh₂ => ?_
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PubLaSafe.pure hh₂
    | none =>
      dsimp only
      rw [StateT.run_bind]
      refine (stateT_lift_la_safe C ℓ encT idOf N _ h₀).bind ?_
      rintro ⟨coins, h'⟩ hEq; dsimp only at hEq; subst h'
      rw [StateT.run_bind]
      refine (rootFSMulti_la_safe C ℓ encT idOf N prng mo t0
        (cka.send γ coins).2.2 σr h₀ hh₀).bind fun ⟨⟨σ', k, sid⟩, h₁⟩ hh₁ => ?_
      rw [StateT.run_bind]
      refine (regSessOptMulti_la_safe C ℓ encT idOf N sid h₁ hh₁).bind
        fun ⟨optIdx, h₂⟩ hh₂ => ?_
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PubLaSafe.pure hh₂
  have hfsSend : ∀ t0 v hdr (h₁ : ShiftedHState Pt RSt I), h₁.lfWin = false →
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka mo gMain true).fsSend
          ctx P t0 v hdr m pair).run h₁) := by
    intro t0 v hdr h₁ hh₁
    dsimp only [hooksFSMulti]
    cases v with
    | inl ss =>
      simp only [StateT.run_pure]
      exact PubLaSafe.pure hh₁
    | inr sIdx =>
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hcond : (!(ctx.safeCh (2 + Δcka) P) && !((h₁.book sIdx).getD {}).sCorr) = true
      · simp only [hcond, ↓reduceIte, StateT.run_bind, StateT.run_pure, pure_bind, Bool.not_false]
        exact PubLaSafe.pure hh₁
      · have hcf : (!(ctx.safeCh (2 + Δcka) P) && !((h₁.book sIdx).getD {}).sCorr) = false :=
          Bool.not_eq_true _ |>.mp hcond
        simp only [hcf, Bool.false_eq_true, ↓reduceIte, Bool.not_true, StateT.run_bind,
          StateT.run_pure, pure_bind]
        cases pair with
        | none =>
          dsimp only
          rw [StateT.run_bind]
          rw [show _root_.CryptoGames.FSAEAD.transmitQuery hdr m =
              liftM (OracleSpec.query (spec := fsSpec (BitVec 256) (BitVec 256) (Header Pt)
                (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32)
                (.inl (.inl (.inl (.inl (.inl (hdr, m))))))) from rfl,
            liftFSMulti_run_query_eq]
          have hq : PubLaSafe C ℓ encT idOf N (fun p => p.2 = h₁)
              (query (spec := PubMultiSpec Pt ℓ)
                (Sum.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl (hdr, m)))))⟩) >>=
                fun a => pure (a, h₁)) :=
            (PubLaSafe.any C ℓ encT idOf N _).bind fun _ _ => PubLaSafe.pure rfl
          refine hq.bind ?_
          rintro ⟨e?, h'⟩ hEq; dsimp only at hEq; subst h'
          cases e? with
          | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hh₁
          | some e =>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PubLaSafe.pure hh₁
        | some pm =>
          rcases pm with ⟨m₀, m₁⟩
          dsimp only
          rw [StateT.run_bind]
          rw [show _root_.CryptoGames.FSAEAD.challengeQuery hdr m₀ m₁ =
              liftM (OracleSpec.query (spec := fsSpec (BitVec 256) (BitVec 256) (Header Pt)
                (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32)
                (.inl (.inl (.inl (.inl (.inr (hdr, m₀, m₁))))))) from rfl,
            liftFSMulti_run_query_eq]
          have hq : PubLaSafe C ℓ encT idOf N (fun p => p.2 = h₁)
              (query (spec := PubMultiSpec Pt ℓ)
                (Sum.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inr (hdr, m₀, m₁)))))⟩) >>=
                fun a => pure (a, h₁)) :=
            (PubLaSafe.any C ℓ encT idOf N _).bind fun _ _ => PubLaSafe.pure rfl
          refine hq.bind ?_
          rintro ⟨e?, h'⟩ hEq; dsimp only at hEq; subst h'
          cases e? with
          | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hh₁
          | some e =>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PubLaSafe.pure hh₁
  unfold vSend
  by_cases hsIn : vp.id.sendsIn (vp.tcur + 1) = true
  · simp only [hsIn, ↓reduceIte, pure_bind]
    rw [StateT.run_bind]
    refine (hstartSend (vp.tcur + 1) vp.γ vp.root h hlf).bind fun ⟨res, h₁⟩ hh₁ => ?_
    cases res with
    | none => dsimp only; simp only [StateT.run_pure]; exact PubLaSafe.pure hh₁
    | some out =>
      rcases out with ⟨γ', T', σ', ss⟩
      dsimp only
      rw [StateT.run_bind]
      refine (hfsSend (vp.tcur + 1) ss (vp.tcur + 1, some T') h₁ hh₁).bind fun ⟨res2, _⟩ hh₂ => ?_
      cases res2 <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hh₂)
  · have hsIn_f : vp.id.sendsIn (vp.tcur + 1) = false := Bool.not_eq_true _ |>.mp hsIn
    simp only [hsIn_f, Bool.false_eq_true, ↓reduceIte, pure_bind]
    cases vp.vS with
    | none => dsimp only; simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
    | some v =>
      dsimp only
      rw [StateT.run_bind]
      refine (hfsSend vp.tcur v (vp.tcur, vp.curCkaMsg) h hlf).bind fun ⟨res2, _⟩ hh₂ => ?_
      cases res2 <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hh₂)

private theorem vRecv_hooksFSMulti_la_safe {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka : ℕ) (mo : Mode) (gMain : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ Pt RSt
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (vp : VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec : Option (_root_.CryptoGames.SM.Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (h : ShiftedHState Pt RSt I) (hlf : h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      ((vRecv (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka mo gMain true)
        ctx P vp c rec).run h) := by
  unfold vRecv
  simp only [StateT.run_bind]
  by_cases hbad : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [hbad, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
  · simp only [Bool.not_eq_true _ |>.mp hbad, Bool.false_eq_true, ↓reduceIte]
    by_cases hc1 : c.1.1 = vp.tcur + 1
    · simp only [hc1, ↓reduceIte]
      cases c.1.2 with
      | none => simp only [pure_bind, StateT.run_pure]; exact PubLaSafe.pure hlf
      | some Tn =>
        have hstart : PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
            (((hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka mo gMain true).startRecv
              ctx P (vp.tcur + 1) vp.γ vp.root Tn).run h) := by
          dsimp only [hooksFSMulti]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          cases hca : h.cache (vp.tcur + 1) with
          | some q =>
            rcases q with ⟨Tc, σc, k, optIdx⟩
            by_cases hTc : Tc = Tn
            · simp only [hTc, ↓reduceIte]
              exact PubLaSafe.pure hlf
            · simp only [hTc, ↓reduceIte]
              split_ifs
              · exact PubLaSafe.pure hlf
              · exact PubLaSafe.pure hlf
              · simp only [StateT.run_bind]
                refine (lookupMultiF_la_safe C ℓ encT idOf N _ h hlf).bind fun ⟨_, h₁⟩ hh₁ => ?_
                simp only [StateT.run_bind]
                refine (regSessMulti_la_safe C ℓ encT idOf N _ h₁ hh₁).bind fun ⟨_, h₂⟩ hh₂ => ?_
                exact PubLaSafe.pure hh₂
              · exact PubLaSafe.pure hlf
          | none =>
            dsimp only
            split_ifs
            · exact PubLaSafe.pure hlf
            · exact PubLaSafe.pure hlf
            · simp only [StateT.run_bind]
              refine (lookupMultiF_la_safe C ℓ encT idOf N _ h hlf).bind fun ⟨_, h₁⟩ hh₁ => ?_
              simp only [StateT.run_bind]
              refine (regSessMulti_la_safe C ℓ encT idOf N _ h₁ hh₁).bind fun ⟨_, h₂⟩ hh₂ => ?_
              exact PubLaSafe.pure hh₂
            · exact PubLaSafe.pure hlf
        simp only [bind_assoc]
        rw [StateT.run_bind]
        refine hstart.bind fun ⟨res, h₁⟩ hh₁ => ?_
        cases res with
        | none => simp only [pure_bind, StateT.run_pure]; exact PubLaSafe.pure hh₁
        | some inner =>
          cases inner with
          | none => simp only [pure_bind, StateT.run_pure]; exact PubLaSafe.pure hh₁
          | some triple =>
            rcases triple with ⟨γ', σ', rsv⟩
            simp only [pure_bind, Function.update_self]
            rw [StateT.run_bind]
            refine (hooksFSMulti_fsRecv_la_safe C ℓ encT idOf N cka prng Δcka mo gMain
              ctx P _ rsv _ _ rec h₁ hh₁).bind fun ⟨ro, _⟩ hh₂ => ?_
            cases ro with
            | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hh₂
            | some r_in =>
              cases r_in <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hh₂)
    · simp only [hc1, ↓reduceIte, pure_bind]
      cases vp.vR c.1.1 with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | some v =>
        rw [StateT.run_bind]
        refine (hooksFSMulti_fsRecv_la_safe C ℓ encT idOf N cka prng Δcka mo gMain
          ctx P c.1.1 v c.1 c.2 rec h hlf).bind fun ⟨ro, _⟩ hh₂ => ?_
        cases ro with
        | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hh₂
        | some r_in =>
          cases r_in <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hh₂)

private theorem liftH_run_eq_la {Γ Pt RSt I α : Type} {ℓ : ℕ}
    (x : _root_.CryptoGames.SM.Engine.HM
      (_root_.CryptoGames.SM.Construction.FSMultiSpec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (ShiftedHState Pt RSt I) α)
    (es : ShiftedEState Γ Pt RSt I ℓ) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

private theorem liftH_la_safe {Γ Pt RSt I α : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (x : _root_.CryptoGames.SM.Engine.HM
      (_root_.CryptoGames.SM.Construction.FSMultiSpec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (ShiftedHState Pt RSt I) α)
    (es : ShiftedEState Γ Pt RSt I ℓ)
    (hx : PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false) (x.run es.h)) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false) ((liftH x).run es) := by
  change PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
    (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 }))
  exact hx.bind fun ⟨_, _⟩ hh' => PubLaSafe.pure hh'

private theorem implEDFShiftedPaperGen_step_la_safe {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins] [SampleableType KR]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (b1 : Bool) (l : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka qep tStar : ℕ) (mo mo' : Mode)
    (q : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
      (_root_.CryptoGames.SM.Construction.PartyState Γ Pt RSt
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (es : ShiftedEState Γ Pt RSt I ℓ) (hlf : es.h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
      ((implEDFShiftedPaperGen b1 l
        (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka mo false true)
        (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy q).run es) := by
  let hk := hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka mo false true
  rcases q with n | (((((q_tr | q_ch) | q_dl) | q_ij) | q_cr) | q_df)
  · simp only [implEDFShiftedPaperGen, QueryImpl.add_apply, coinsE]
    exact (stateT_lift_la_safe C ℓ encT idOf N _ es).mono fun _ hp => hp ▸ hlf
  · rcases q_tr with ⟨P, m, r⟩
    simp only [implEDFShiftedPaperGen, QueryImpl.add_apply, transmitE,
      StateT.run_bind, StateT.run_get, pure_bind]
    by_cases h0 : (es.abort || es.g.win) = true
    · simp only [h0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
    · simp only [Bool.not_eq_true _ |>.mp h0, Bool.false_eq_true, ↓reduceIte]
      cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | some s₁ =>
        dsimp only
        by_cases h1 : mo'.policy.leakDoom es.g s₁ = true
        · simp only [h1, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PubLaSafe.pure hlf
        · simp only [Bool.not_eq_true _ |>.mp h1, Bool.false_eq_true, ↓reduceIte]
          rw [StateT.run_bind]
          refine (liftH_la_safe C ℓ encT idOf N _ es
            (vSend_hooksFSMulti_la_safe C ℓ encT idOf N cka prng Δcka mo false
              s₁ P (s₁.st P) m none r es.h hlf)).bind fun ⟨out, es₁⟩ hes₁ => ?_
          cases out <;>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
            exact PubLaSafe.pure hes₁
  · rcases q_ch with ⟨P, m₀, m₁, r⟩
    simp only [implEDFShiftedPaperGen, QueryImpl.add_apply, challE,
      StateT.run_bind, StateT.run_get, pure_bind]
    by_cases h0 : (es.abort || es.g.win) = true
    · simp only [h0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
    · simp only [Bool.not_eq_true _ |>.mp h0, Bool.false_eq_true, ↓reduceIte]
      cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | some s₁ =>
        dsimp only
        by_cases h1 : (!s₁.safeCh (2 + Δcka) P || !(mo'.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s₁.epoch P)) = true
        · simp only [h1, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
        · simp only [Bool.not_eq_true _ |>.mp h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h2 : mo'.policy.leakDoom es.g s₁ = true
          · simp only [h2, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PubLaSafe.pure hlf
          · simp only [Bool.not_eq_true _ |>.mp h2, Bool.false_eq_true, ↓reduceIte]
            rw [StateT.run_bind]
            refine (liftH_la_safe C ℓ encT idOf N _ es
              (vSend_hooksFSMulti_la_safe C ℓ encT idOf N cka prng Δcka mo false
                s₁ P (s₁.st P) _ (some (m₀, m₁)) r es.h hlf)).bind fun ⟨out, es₁⟩ hes₁ => ?_
            cases out <;>
              simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
              exact PubLaSafe.pure hes₁
  · rcases q_dl with ⟨P, c⟩
    simp only [implEDFShiftedPaperGen, QueryImpl.add_apply, deliverE,
      StateT.run_bind, StateT.run_get, pure_bind]
    by_cases h0 : (es.abort || es.g.win) = true
    · simp only [h0, ↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure hlf
    · simp only [Bool.not_eq_true _ |>.mp h0, Bool.false_eq_true, ↓reduceIte]
      cases es.g.inTransit P.other c with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | some rec =>
        dsimp only
        rw [StateT.run_bind]
        refine (liftH_la_safe C ℓ encT idOf N _ es
          (vRecv_hooksFSMulti_la_safe C ℓ encT idOf N cka prng Δcka mo false
            es.g P (es.g.st P) c (some rec) es.h hlf)).bind fun ⟨ro, es₁⟩ hes₁ => ?_
        cases ro with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PubLaSafe.pure hes₁
        | some r_in =>
          dsimp only
          cases r_in with
          | none =>
            dsimp only
            split_ifs <;>
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
              exact PubLaSafe.pure hes₁
          | some quad =>
            rcases quad with ⟨st', t', i', m'⟩
            dsimp only
            simp only [commitE, liftH_run_eq_la, hooksFSMulti, StateT.run_bind, StateT.run_pure,
              pure_bind, StateT.run_modify]
            exact PubLaSafe.pure hes₁
  · rcases q_ij with ⟨P, c⟩
    simp only [implEDFShiftedPaperGen, QueryImpl.add_apply]
    cases b1 <;>
      simp only [_root_.CryptoGames.SM.Engine.injectEGen, ↓reduceIte, Bool.false_eq_true,
        _root_.CryptoGames.SM.Construction.DeliverForge.injectEB1, injectE,
        StateT.run_bind, StateT.run_get, pure_bind]
    all_goals
      split_ifs
      · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      · rw [StateT.run_bind]
        refine (liftH_la_safe C ℓ encT idOf N _ es
          (vRecv_hooksFSMulti_la_safe C ℓ encT idOf N cka prng Δcka mo false
            es.g P (es.g.st P) c none es.h hlf)).bind fun ⟨ro, es₁⟩ hes₁ => ?_
        cases ro with
        | none =>
          dsimp only
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PubLaSafe.pure hes₁
        | some r_in =>
          dsimp only
          cases r_in with
          | none => dsimp only; simp only [StateT.run_pure]; exact PubLaSafe.pure hes₁
          | some quad =>
            rcases quad with ⟨st', t', i', m'⟩
            dsimp only
            split_ifs <;>
              simp only [commitE, abortE, liftH_run_eq_la, hooksFSMulti,
                StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
              exact PubLaSafe.pure hes₁
  · simp only [implEDFShiftedPaperGen, QueryImpl.add_apply, corrEShiftedPaper,
      StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact PubLaSafe.pure hlf
    · rw [StateT.run_bind]
      have hrev : PubLaSafe C ℓ encT idOf N
          (fun p : Option (_root_.CryptoGames.SM.Construction.PartyState Γ Pt RSt
            (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256))) × ShiftedHState Pt RSt I =>
            p.2.lfWin = false)
          ((hk.reveal es.g q_cr (es.g.st q_cr)).run es.h) := by
        dsimp only [hk, hooksFSMulti]
        cases (es.g.st q_cr).vS with
        | none =>
          simp only [StateT.run_bind, StateT.run_pure, pure_bind]
          split_ifs <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf)
        | some v =>
          cases v <;>
            simp only [↓reduceIte, StateT.run_bind, StateT.run_pure, pure_bind] <;>
            (try split_ifs) <;> (try simp only [StateT.run_pure]) <;> exact PubLaSafe.pure hlf
      refine (liftH_la_safe C ℓ encT idOf N _ es hrev).bind fun ⟨stOpt, es₁⟩ hes₁ => ?_
      cases stOpt <;>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
        exact PubLaSafe.pure hes₁
  · rcases q_df with ⟨P, c, c'⟩
    simp only [implEDFShiftedPaperGen, QueryImpl.add_apply]
    cases b1 <;>
      simp only [_root_.CryptoGames.SM.Engine.deliverForgeEGen, ↓reduceIte, Bool.false_eq_true,
        _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind]
    all_goals
      split_ifs
      · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      · cases es.g.inTransit P.other c with
        | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        | some r_c =>
          dsimp only
          split_ifs
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
          · rw [StateT.run_bind]
            refine (liftH_la_safe C ℓ encT idOf N _ es
              (vRecv_hooksFSMulti_la_safe C ℓ encT idOf N cka prng Δcka mo false
                es.g P (es.g.st P) c' none es.h hlf)).bind fun ⟨ro, es₁⟩ hes₁ => ?_
            cases ro with
            | none =>
              dsimp only
              simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact PubLaSafe.pure hes₁
            | some r_in =>
              dsimp only
              cases r_in with
              | none => dsimp only; simp only [StateT.run_pure]; exact PubLaSafe.pure hes₁
              | some quad =>
                rcases quad with ⟨st', t', i', m'⟩
                dsimp only
                split_ifs <;>
                  simp only [commitE, abortE, liftH_run_eq_la, hooksFSMulti,
                    StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
                  exact PubLaSafe.pure hes₁

private theorem simulateQ_implEDFShiftedPaperGen_la_safe {KC Γ CCoins Pt KR RSt I α : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins] [SampleableType KR]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (b1 : Bool) (l : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka qep tStar : ℕ) (mo mo' : Mode)
    (x : OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
      (_root_.CryptoGames.SM.Construction.PartyState Γ Pt RSt
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) α)
    (es : ShiftedEState Γ Pt RSt I ℓ) (hlf : es.h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
      ((simulateQ (implEDFShiftedPaperGen b1 l
        (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka mo false true)
        (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy) x).run es) := by
  induction x using OracleComp.inductionOn generalizing es with
  | pure a => exact PubLaSafe.pure hlf
  | query_bind q r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    exact (implEDFShiftedPaperGen_step_la_safe C ℓ encT idOf N b1 l cka prng
      Δcka qep tStar mo mo' q es hlf).bind fun ⟨ans, es'⟩ hes' => ih ans es' hes'

end HooksFSMultiLaSafe

-- ============================================================================
-- 3. Pure SM Game & Party Invariant Lemmas for `la = false`
-- ============================================================================

section ShiftedMainPureLemmas

private theorem sendsIn_senderOf (t : ℕ) : (Party.senderOf t).sendsIn t = true := by
  unfold Party.senderOf
  by_cases h : t % 2 == 1
  · simp [h, Party.sendsIn]
  · have h0 : t % 2 == 0 := by
      simp only [beq_iff_eq] at h ⊢; omega
    simp [h, h0, Party.sendsIn]

private theorem sendsIn_receiverOf (t : ℕ) : (Party.receiverOf t).sendsIn t = false := by
  unfold Party.receiverOf Party.senderOf
  by_cases h : t % 2 == 1
  · simp only [h, ↓reduceIte, Party.other, Party.sendsIn, beq_eq_false_iff_ne]
    simp only [beq_iff_eq] at h; omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Party.other, Party.sendsIn, beq_eq_false_iff_ne]

private theorem eq_senderOf_of_sendsIn {P : Party} {t : ℕ} (h : P.sendsIn t = true) :
    P = Party.senderOf t := by
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht <;>
    cases P <;> simp [Party.sendsIn, Party.senderOf, ht] at h ⊢

private theorem eq_receiverOf_of_sendsIn_false {P : Party} {t : ℕ} (h : P.sendsIn t = false) :
    P = Party.receiverOf t := by
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht <;>
    cases P <;> simp [Party.sendsIn, Party.receiverOf, Party.senderOf, Party.other, ht] at h ⊢

private theorem other_receiverOf (t : ℕ) : (Party.receiverOf t).other = Party.senderOf t := by
  unfold Party.receiverOf; cases Party.senderOf t <;> rfl

private theorem sendsIn_succ (P : Party) (n : ℕ) : P.sendsIn (n + 1) = !P.sendsIn n := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hn1 : (n + 1) % 2 = 1 := by omega
    cases P <;> simp [Party.sendsIn, hn, hn1]
  · have hn1 : (n + 1) % 2 = 0 := by omega
    cases P <;> simp [Party.sendsIn, hn, hn1]

private theorem sendsIn_add_two (P : Party) (n : ℕ) : P.sendsIn (n + 2) = P.sendsIn n := by
  rw [show n + 2 = (n + 1) + 1 by omega, sendsIn_succ, sendsIn_succ, Bool.not_not]

private theorem le_maxOpt_right (o : Option ℕ) (x : ℕ) :
    x ≤ _root_.CryptoGames.SM.maxOpt o x := by
  cases o <;> simp [_root_.CryptoGames.SM.maxOpt]

private theorem le_maxOpt_of_some {o : Option ℕ} {a : ℕ} (ho : o = some a) (x : ℕ) :
    a ≤ _root_.CryptoGames.SM.maxOpt o x := by
  subst ho; simp [_root_.CryptoGames.SM.maxOpt]

private theorem leaks_ok_of_leakDoom_false {St Msg C : Type} {l t : ℕ}
    {g s₁ : _root_.CryptoGames.SM.GameState St Msg C}
    (hdoom : _root_.CryptoGames.SM.Engine.Policy.leakDoom ⟨true, some (l - 1), t⟩ g s₁ = false) :
    ∀ lk ∈ s₁.leaks, lk ≤ l - 1 ∨ t ≤ lk := by
  intro lk hlk
  unfold _root_.CryptoGames.SM.Engine.Policy.leakDoom at hdoom
  simp only [Bool.or_eq_false_iff, List.any_eq_false] at hdoom
  have h1 := hdoom.1 lk hlk
  simp only [_root_.CryptoGames.SM.ltOpt, Bool.and_eq_true, decide_eq_true_eq, not_and_or,
    not_lt] at h1
  exact h1

private theorem tL_ge_of_not_safeCh {St Msg C : Type} {Δcka l t : ℕ}
    {s₁ : _root_.CryptoGames.SM.GameState St Msg C}
    (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (hep : s₁.epoch (Party.senderOf t) = t)
    (htL : ∀ lk, s₁.tL = some lk → lk ∈ s₁.leaks)
    (hleaks : ∀ lk ∈ s₁.leaks, lk ≤ l - 1 ∨ t ≤ lk)
    (hnsafe : s₁.safeCh (2 + Δcka) (Party.senderOf t) = false) :
    ∃ lk, s₁.tL = some lk ∧ t ≤ lk := by
  unfold _root_.CryptoGames.SM.GameState.safeCh _root_.CryptoGames.SM.healedBy at hnsafe
  rw [hep] at hnsafe
  cases htL0 : s₁.tL with
  | none => simp [htL0] at hnsafe
  | some lk =>
    rw [htL0, decide_eq_false_iff_not] at hnsafe
    rcases hleaks lk (htL lk htL0) with hle | hge
    · omega
    · exact ⟨lk, rfl, hge⟩

private theorem afterCorrShifted_tL_ge_of_epoch_ge {St Msg C : Type} {Δcka l t : ℕ}
    {g : _root_.CryptoGames.SM.GameState St Msg C} {P : Party}
    (hAdm : (l - 1) + (2 + Δcka) ≤ t) (hep : t ≤ g.epoch P) :
    ∃ lk, (_root_.CryptoGames.SM.Construction.DeliverForge.afterCorrShifted l g P).tL = some lk ∧
      t ≤ lk := by
  unfold _root_.CryptoGames.SM.Construction.DeliverForge.afterCorrShifted
  have hnot_shift : ¬ (max (g.epoch .A) (g.epoch .B) = l ∧ g.epoch P + 1 ≤ l) := by
    intro ⟨_, hle⟩; omega
  simp only [hnot_shift, ↓reduceIte, _root_.CryptoGames.SM.GameState.leak]
  refine ⟨_, rfl, ?_⟩
  have hmax : g.epoch P ≤ max (g.epoch .A) (g.epoch .B) := by cases P <;> simp
  exact le_trans hep (le_trans hmax (le_maxOpt_right g.tL _))

private theorem trivial_true_of_corr_inv {St Msg C : Type} {t c₀ i' Δ₀ : ℕ}
    {s : _root_.CryptoGames.SM.GameState St Msg C}
    (hΔ₀ : 2 ≤ Δ₀)
    (htL : ∃ lk, s.tL = some lk ∧ t ≤ lk)
    (hcomp : ∀ r ∈ s.trans,
      r.pos.sender = Party.senderOf t → r.pos.epoch = t → c₀ < r.pos.idx → r.pos ∈ s.comp)
    (hlt : c₀ < i') :
    s.trivial Δ₀ ⟨Party.senderOf t, t, i'⟩ = true := by
  unfold _root_.CryptoGames.SM.GameState.trivial
  by_cases htr : (s.trans.any (fun r => r.pos == ⟨Party.senderOf t, t, i'⟩)) = true
  · rw [List.any_eq_true] at htr
    rcases htr with ⟨r, hr, hpos⟩
    rw [beq_iff_eq] at hpos
    have hmem : (⟨Party.senderOf t, t, i'⟩ : _root_.CryptoGames.SM.Pos) ∈ s.comp := by
      rw [← hpos]
      exact hcomp r hr (by rw [hpos]) (by rw [hpos]) (by rw [hpos]; exact hlt)
    simp [hmem]
  · simp only [Bool.not_eq_true] at htr
    rcases htL with ⟨lk, hlk, htle⟩
    have hnheal : _root_.CryptoGames.SM.healedBy s.tL Δ₀ t = false := by
      rw [hlk]
      simp only [_root_.CryptoGames.SM.healedBy, decide_eq_false_iff_not]
      omega
    simp [htr, hnheal]

private theorem tL_ge_of_not_healedBy {l t Δcka : ℕ} {tL : Option ℕ} {leaks : List ℕ}
    (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (htL_mem : ∀ lk, tL = some lk → lk ∈ leaks)
    (hleaks_ok : ∀ lk ∈ leaks, lk ≤ l - 1 ∨ t ≤ lk)
    (hnheal : _root_.CryptoGames.SM.healedBy tL (2 + Δcka) t = false) :
    ∃ lk, tL = some lk ∧ t ≤ lk := by
  cases htL : tL with
  | none => simp [htL, _root_.CryptoGames.SM.healedBy] at hnheal
  | some lk =>
    simp only [htL, _root_.CryptoGames.SM.healedBy, decide_eq_false_iff_not] at hnheal
    rcases hleaks_ok lk (htL_mem lk htL) with hle | hge
    · omega
    · exact ⟨lk, rfl, hge⟩

private theorem healedBy_of_safeInj_two {St Msg C : Type} {l t Δcka : ℕ} {P : Party}
    {g : _root_.CryptoGames.SM.GameState St Msg C}
    (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (htL_mem : ∀ lk, g.tL = some lk → lk ∈ g.leaks)
    (hleaks_ok : ∀ lk ∈ g.leaks, lk ≤ l - 1 ∨ t ≤ lk)
    (hep : g.epoch P + 1 = t)
    (hsafe : g.safeInj 2 = true) :
    _root_.CryptoGames.SM.healedBy g.tL (2 + Δcka) t = true := by
  unfold _root_.CryptoGames.SM.GameState.safeInj at hsafe
  cases htL : g.tL with
  | none => simp [_root_.CryptoGames.SM.healedBy]
  | some lk =>
    rw [htL] at hsafe
    simp only [_root_.CryptoGames.SM.healedBy, decide_eq_true_eq] at hsafe ⊢
    have hmin : min (g.epoch .A) (g.epoch .B) ≤ g.epoch P := by cases P <;> simp
    rcases hleaks_ok lk (htL_mem lk htL) with hle | hge <;> omega

private theorem safeInj_two_of_safeInj_add {St Msg C : Type} {Δcka : ℕ}
    {g : _root_.CryptoGames.SM.GameState St Msg C}
    (hsafe : g.safeInj (2 + Δcka) = true) :
    g.safeInj 2 = true := by
  unfold _root_.CryptoGames.SM.GameState.safeInj at hsafe ⊢
  cases htL : g.tL with
  | none => simp [_root_.CryptoGames.SM.healedBy]
  | some lk =>
    rw [htL] at hsafe
    simp only [_root_.CryptoGames.SM.healedBy, decide_eq_true_eq] at hsafe ⊢
    omega

end ShiftedMainPureLemmas

-- ============================================================================
-- 4. Main Mode (`la = false`) Joint Invariant `ShiftedSafe` & Engine Induction
-- ============================================================================

section ShiftedMainProof

private def honOpt {Pt RSt I : Type} (t : ℕ) (h : ShiftedHState Pt RSt I) : Option ℕ :=
  match h.cache t with
  | some (_, _, _, optIdx) => optIdx
  | none => none

private structure ShiftedActiveInv {Γ Pt RSt I : Type} {ℓ : ℕ}
    (l t : ℕ) (es : ShiftedEState Γ Pt RSt I ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop where
  abort_false : es.abort = false
  win_false : es.g.win = false
  st_id : ∀ P, (es.g.st P).id = P
  st_tcur : ∀ P, (es.g.st P).tcur = es.g.epoch P
  tL_mem : ∀ lk, es.g.tL = some lk → lk ∈ es.g.leaks
  leaks_ok : ∀ lk ∈ es.g.leaks, lk ≤ l - 1 ∨ t ≤ lk
  trans_hdr : ∀ r ∈ es.g.trans, r.ct.1.1 = r.pos.epoch ∧ r.pos.epoch ≤ es.g.epoch r.pos.sender
  cache_pre : es.g.epoch (Party.senderOf t) < t → es.h.cache t = none
  cache_t_some : ∀ Tc σc k optIdx, es.h.cache t = some (Tc, σc, k, optIdx) →
    ∃ sIdx, optIdx = some sIdx
  cache_other_none : ∀ t0, t0 ≠ t → ∀ Tc σc k optIdx, es.h.cache t0 = some (Tc, σc, k, optIdx) →
    optIdx = none
  vS_inr : ∀ P sIdx, (es.g.st P).vS = some (.inr sIdx) →
    P = Party.senderOf t ∧ honOpt t es.h = some sIdx ∧
      (es.g.epoch P = t ∨ es.g.epoch P = t + 1)
  sender_at_t : es.g.epoch (Party.senderOf t) = t →
    ∃ sIdx, honOpt t es.h = some sIdx ∧
      (es.g.st (Party.senderOf t)).vS = some (.inr sIdx) ∧
      es.g.idx (Party.senderOf t) = ((es.h.book sIdx).getD {}).fsCount
  sender_cka_at_t : es.g.epoch (Party.senderOf t) = t →
    ∃ Tc σc k sIdx, es.h.cache t = some (Tc, σc, k, some sIdx) ∧
      (es.g.st (Party.senderOf t)).curCkaMsg = some Tc
  trans_t_hdr : ∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
    ∃ Tc σc k sIdx, es.h.cache t = some (Tc, σc, k, some sIdx) ∧ r.ct.1 = (t, some Tc)
  vR_target : ∀ P rsv, (es.g.st P).vR t = some rsv →
    ∃ sIdx, rsv = .inr sIdx ∧ honOpt t es.h = some sIdx
  vR_other : ∀ P t0 rsv, t0 ≠ t → (es.g.st P).vR t0 = some rsv →
    ∃ rs, rsv = .inl rs
  non_hon_empty : ∀ sIdx, honOpt t es.h ≠ some sIdx →
    ((es.h.book sIdx).getD {}).fsCount = 0 ∧ ((es.h.book sIdx).getD {}).fsTrans = []
  hon_book : ∀ sIdx, honOpt t es.h = some sIdx →
    (∀ cnt hdr e, (cnt, hdr, e) ∈ ((es.h.book sIdx).getD {}).fsTrans →
      cnt = e.1 ∧ ∃ r ∈ es.g.trans, r.pos = ⟨Party.senderOf t, t, cnt⟩ ∧ r.ct = (hdr, e)) ∧
    (∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
      r.ct.2.1 = r.pos.idx ∧ r.pos.idx ≤ ((es.h.book sIdx).getD {}).fsCount)
  router_last : ∀ sIdx, sessLastIdx σ sIdx = ((es.h.book sIdx).getD {}).fsCount
  router_corr : ∀ sIdx c₀, sessCorrAt σ sIdx = some c₀ →
    honOpt t es.h = some sIdx ∧
    c₀ ≤ ((es.h.book sIdx).getD {}).fsCount ∧
    (∃ lk, es.g.tL = some lk ∧ t ≤ lk) ∧
    (∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
      c₀ < r.pos.idx → r.pos ∈ es.g.comp)

private def ShiftedSafe {Γ Pt RSt I : Type} {ℓ : ℕ}
    (l t : ℕ) (es : ShiftedEState Γ Pt RSt I ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  es.abort = true ∨ ShiftedActiveInv l t es σ

private theorem authOut_eq_false_of_shiftedSafe {Γ Pt RSt I : Type} {ℓ : ℕ}
    (Δcka l t : ℕ) (es : ShiftedEState Γ Pt RSt I ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hs : ShiftedSafe l t es σ) :
    authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy es = false := by
  rcases hs with hab | hact
  · simp [authOut, hab]
  · simp [authOut, hact.abort_false, hact.win_false]

private theorem authOut_eq_false_of_not_adm {Γ Pt RSt I : Type} {ℓ : ℕ}
    (Δcka l t : ℕ) (hnot : ¬ ((l - 1) + (2 + Δcka) ≤ t)) (es : ShiftedEState Γ Pt RSt I ℓ) :
    authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy es = false := by
  have hfalse : _root_.CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) (some (l - 1)) t = false := by
    simp [_root_.CryptoGames.SM.lastLeakGuessAdmissible, _root_.CryptoGames.SM.healedBy, hnot]
  simp [authOut, Mode.policy, _root_.CryptoGames.SM.authLosingConditionsAvoided, hfalse]

private def PubMainRel {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    {α : Type} (Pre : (ℕ → Option (IdealHSt Pt ℓ)) → Prop)
    (Post : α → (ℕ → Option (IdealHSt Pt ℓ)) → Prop)
    (x : OracleComp (PubMultiSpec Pt ℓ) α) : Prop :=
  ∀ rc σ, Pre σ →
    ∀ z ∈ support (runPubIdeal C ℓ encT idOf N false x rc σ),
      Post z.1.1 z.2

private theorem PubMainRel.pure {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {α : Type} {Pre : (ℕ → Option (IdealHSt Pt ℓ)) → Prop}
    {Post : α → (ℕ → Option (IdealHSt Pt ℓ)) → Prop} {a : α}
    (ha : ∀ σ, Pre σ → Post a σ) :
    PubMainRel C ℓ encT idOf N Pre Post (pure a) := by
  intro rc σ hσ z hz
  simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst hz
  exact ha σ hσ

private theorem PubMainRel.bind {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {α β : Type} {Pre : (ℕ → Option (IdealHSt Pt ℓ)) → Prop}
    {Mid : α → (ℕ → Option (IdealHSt Pt ℓ)) → Prop}
    {Post : β → (ℕ → Option (IdealHSt Pt ℓ)) → Prop}
    {x : OracleComp (PubMultiSpec Pt ℓ) α} {f : α → OracleComp (PubMultiSpec Pt ℓ) β}
    (hx : PubMainRel C ℓ encT idOf N Pre Mid x)
    (hf : ∀ a, PubMainRel C ℓ encT idOf N (Mid a) Post (f a)) :
    PubMainRel C ℓ encT idOf N Pre Post (x >>= f) := by
  intro rc σ hσ z hz
  simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hzw⟩
  exact hf w.1.1 w.1.2 w.2 (hx rc σ hσ w hw) z hzw

private theorem lift_inl_query_eq_main {ι₁ ι₂ : Type}
    {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} (q₀ : s₁.Domain) :
    (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₁.Range q₀)) =
      query (spec := s₁ + s₂) (Sum.inl q₀) := by
  rw [query_eq_liftM]; rfl

private theorem PubMainRel.sampleT {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    {β : Type} [SampleableType β] {Pre : (ℕ → Option (IdealHSt Pt ℓ)) → Prop} :
    PubMainRel C ℓ encT idOf N Pre (fun _ σ' => Pre σ')
      (_root_.CryptoGames.SM.Construction.sampleT β) := by
  unfold _root_.CryptoGames.SM.Construction.sampleT
  rw [← liftComp_eq_liftM]
  induction ($ᵗ β : ProbComp β) using OracleComp.inductionOn with
  | pure a =>
    intro rc σ hσ z hz
    simp only [liftComp_pure, runPubIdeal, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact hσ
  | query_bind t0 r ih =>
    intro rc σ hσ z hz
    rw [liftComp_bind, liftComp_liftM_query, lift_inl_query_eq_main] at hz
    simp only [runPubIdeal, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, pubMultiImpl, StateT.run_bind, stateT_lift_run,
      simulateQ_HasQuery_query, idealSessImpl, sessLift_inl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨u, _, hzu⟩
    exact ih u rc σ hσ z hzu

private theorem PubMainRel.stateT_lift_sampleT {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    {HS β : Type} [SampleableType β] (hs : HS)
    {Pre : (ℕ → Option (IdealHSt Pt ℓ)) → Prop} :
    PubMainRel C ℓ encT idOf N Pre (fun p σ' => p.2 = hs ∧ Pre σ')
      ((StateT.lift (_root_.CryptoGames.SM.Construction.sampleT β)).run hs) := by
  rw [stateT_lift_run]
  exact (PubMainRel.sampleT C ℓ encT idOf N).bind fun _ =>
    PubMainRel.pure fun _ hσ => ⟨rfl, hσ⟩

private theorem lookupMultiF_main_preserves {Pt RSt I : Type} [DecidableEq Pt] [DecidableEq I]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (Ik : I) (h : ShiftedHState Pt RSt I)
    {Pre : (ℕ → Option (IdealHSt Pt ℓ)) → Prop} :
    PubMainRel C ℓ encT idOf N Pre
      (fun p σ' => p.2.cache = h.cache ∧ p.2.book = h.book ∧ Pre σ')
      ((lookupMultiF
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32) Ik).run h) := by
  unfold lookupMultiF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h.table.lookup Ik with
  | some k => exact PubMainRel.pure fun _ hσ => ⟨rfl, rfl, hσ⟩
  | none =>
    simp only [StateT.run_bind]
    refine (PubMainRel.stateT_lift_sampleT C ℓ encT idOf N h).bind fun ⟨k, h₁⟩ => ?_
    intro rc σ ⟨hh₁, hσ⟩ z hz
    dsimp only at hh₁
    subst h₁
    simp only [StateT.run_modify, StateT.run_pure, pure_bind, runPubIdeal, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl, hσ⟩

private theorem regSessMulti_main_preserves {Pt RSt I : Type} [DecidableEq Pt] [DecidableEq I]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (Ik : I) (h : ShiftedHState Pt RSt I)
    {Pre : (ℕ → Option (IdealHSt Pt ℓ)) → Prop} :
    PubMainRel C ℓ encT idOf N Pre
      (fun p σ' => p.2.cache = h.cache ∧ p.2.book = h.book ∧ Pre σ')
      ((regSessMulti
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32)
        (Sig := RSt) (K := BitVec 256) Ik).run h) := by
  unfold regSessMulti
  simp only [StateT.run_map, map_eq_bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
    exact PubMainRel.pure (Pt := Pt) fun _ hσ => ⟨rfl, rfl, hσ⟩

private theorem rootFSMulti_main_preserves {Pt KR RSt I : Type} [DecidableEq Pt]
    [DecidableEq I] [SampleableType I] [SampleableType KR]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (mo : Mode) (t0 : ℕ) (Ik : I) (σr : RSt) (h : ShiftedHState Pt RSt I)
    {Pre : (ℕ → Option (IdealHSt Pt ℓ)) → Prop} :
    PubMainRel C ℓ encT idOf N Pre
      (fun p σ' =>
        p.2.cache = h.cache ∧ p.2.book = h.book ∧
        (t0 = mo.tStar → p.1.2.2.isSome = true) ∧
        (t0 ≠ mo.tStar → p.1.2.2 = none) ∧ Pre σ')
      ((rootFSMulti
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32) prng mo t0 Ik σr).run h) := by
  unfold rootFSMulti
  by_cases hgt : mo.tStar < t0
  · simp only [hgt, ↓reduceIte]
    exact PubMainRel.pure (Pt := Pt) fun _ hσ => ⟨rfl, rfl, fun heq => by omega, fun _ => rfl, hσ⟩
  · simp only [hgt, ↓reduceIte]
    by_cases heq : t0 = mo.tStar
    · simp only [heq, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind]
        refine (PubMainRel.stateT_lift_sampleT C ℓ encT idOf N h).bind fun ⟨Ir, h₁⟩ => ?_
        dsimp only
        refine (PubMainRel.stateT_lift_sampleT C ℓ encT idOf N h₁).bind fun ⟨k, h₂⟩ => ?_
        exact PubMainRel.pure (Pt := Pt) fun _ ⟨hh₂, hh₁, hσ⟩ => by
          dsimp only at hh₁ hh₂
          subst hh₁; subst hh₂
          exact ⟨rfl, rfl, fun _ => rfl, fun hne => absurd rfl hne, hσ⟩
      · simp only [StateT.run_bind]
        exact (lookupMultiF_main_preserves C ℓ encT idOf N Ik h).bind fun ⟨k, h₁⟩ =>
          PubMainRel.pure (Pt := Pt) fun _ ⟨hca, hbk, hσ⟩ =>
            ⟨hca, hbk, fun _ => rfl, fun hne => absurd rfl hne, hσ⟩
    · simp only [heq, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind]
        exact (PubMainRel.stateT_lift_sampleT C ℓ encT idOf N h).bind fun ⟨Ir, h₁⟩ =>
          PubMainRel.pure (Pt := Pt) fun _ ⟨hh₁, hσ⟩ => by
            dsimp only at hh₁
            subst h₁
            exact ⟨rfl, rfl, fun h0 => False.elim h0, fun _ => rfl, hσ⟩
      · exact PubMainRel.pure (Pt := Pt) fun _ hσ => ⟨rfl, rfl, fun h0 => False.elim h0, fun _ => rfl, hσ⟩

private theorem initFSMultiRaw_main_safe {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType KR] [SampleableType KC]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (lam : I) (l t : ℕ) (authH : Bool) (ht2 : 2 ≤ t) :
    PubMainRel C ℓ encT idOf N
      (fun σ => σ = fun _ => none)
      (fun es σ' => ShiftedSafe l t es σ')
      (initFSMultiRaw cka prng (ShiftedFS Pt C ℓ encT idOf) lam ⟨authH, some (l - 1), t⟩ false) := by
  unfold initFSMultiRaw
  refine (PubMainRel.sampleT C ℓ encT idOf N).bind fun kr => ?_
  refine (PubMainRel.sampleT C ℓ encT idOf N).bind fun kc => ?_
  refine (rootFSMulti_main_preserves C ℓ encT idOf N prng ⟨authH, some (l - 1), t⟩ 0 lam
    (prng.init kr) {}).bind fun ⟨⟨σr, k, sid⟩, h₁⟩ => ?_
  intro rc σ ⟨hca₁, hbk₁, _, hsid0, hσ0⟩ z hz
  dsimp only at hca₁ hbk₁ hsid0
  have hsid_none : sid = none := hsid0 (by dsimp; omega)
  subst sid
  simp only [regSessOptMulti, StateT.run_pure, pure_bind, runPubIdeal, simulateQ_pure,
    support_pure, Set.mem_singleton_iff] at hz
  subst hz
  right
  have hhon_none : honOpt t h₁ = none := by simp [honOpt, hca₁]
  refine
    { abort_false := rfl
      win_false := rfl
      st_id := fun P => by cases P <;> rfl
      st_tcur := fun P => by cases P <;> rfl
      tL_mem := fun _ h => nomatch h
      leaks_ok := fun _ h => nomatch h
      trans_hdr := fun _ h => nomatch h
      cache_pre := fun _ => by simp [hca₁]
      cache_t_some := fun _ _ _ _ h => by simp [hca₁] at h
      cache_other_none := fun _ _ _ _ _ _ h => by simp [hca₁] at h
      vS_inr := fun P sIdx h => by cases P <;> simp [_root_.CryptoGames.SM.Construction.mkParties] at h
      sender_at_t := fun h => by dsimp at h; omega
      sender_cka_at_t := fun h => by dsimp at h; omega
      trans_t_hdr := fun _ h => nomatch h
      vR_target := fun P rsv h => by
        cases P <;> simp [_root_.CryptoGames.SM.Construction.mkParties, show t ≠ 0 by omega] at h
      vR_other := fun P t0 rsv _ h => by
        cases P
        · simp only [_root_.CryptoGames.SM.Construction.mkParties] at h
          split_ifs at h with ht0
          · injection h with hrsv; exact ⟨_, hrsv.symm⟩
        · simp [_root_.CryptoGames.SM.Construction.mkParties] at h
      non_hon_empty := fun sIdx _ => by simp [hbk₁]
      hon_book := fun sIdx hh => by rw [hhon_none] at hh; exact nomatch hh
      router_last := fun sIdx => by subst hσ0; simp [sessLastIdx, hbk₁]
      router_corr := fun sIdx c₀ hc => by subst hσ0; simp [sessCorrAt] at hc }

-- `vRecv` on `hooksFSMulti` at `la = false` preserves book/router invariants and proves that any
-- accepted non-transit receive at target epoch `t` (`rec = none`) is at a compromised index!
private theorem fsRecv_hooksFSMulti_main_step {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (es : ShiftedEState Γ Pt RSt I ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hact : ShiftedActiveInv l t es σ)
    (P : Party) (t0 : ℕ)
    (rsv : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec : Option (_root_.CryptoGames.SM.Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (h_sIdx_hon : ∀ sIdx, rsv = .inr sIdx → t0 = t ∧ P = Party.receiverOf t ∧
      (honOpt t es.h = some sIdx ∨ _root_.CryptoGames.SM.healedBy es.g.tL (2 + Δcka) t = true))
    (h_forged_not_trans : rec = none → (es.g.inTransit P.other (hdr, e)).isSome = false)
    (h₁ : ShiftedHState Pt RSt I) (hca₁ : h₁.cache = es.h.cache) (hbk₁ : h₁.book = es.h.book) :
    PubMainRel C ℓ encT idOf N
      (fun σ₀ => σ₀ = σ)
      (fun p σ' =>
        p.1 ≠ none →
          p.2.cache = es.h.cache ∧
          (∀ sIdx, sessLastIdx σ' sIdx = ((p.2.book sIdx).getD {}).fsCount) ∧
          (∀ sIdx, ((p.2.book sIdx).getD {}).fsCount = ((es.h.book sIdx).getD {}).fsCount) ∧
          (∀ sIdx c₀, sessCorrAt σ' sIdx = some c₀ →
            honOpt t es.h = some sIdx ∧
            c₀ ≤ ((es.h.book sIdx).getD {}).fsCount ∧
            (∃ lk, es.g.tL = some lk ∧ t ≤ lk) ∧
            (∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
              c₀ < r.pos.idx → r.pos ∈ es.g.comp)) ∧
          (∀ sIdx, honOpt t es.h ≠ some sIdx → ((p.2.book sIdx).getD {}).fsTrans = []) ∧
          (p.1 = some none → ∀ sIdx, ((p.2.book sIdx).getD {}).fsTrans = ((es.h.book sIdx).getD {}).fsTrans) ∧
          (∀ rsv' i' m', p.1 = some (some (rsv', i', m')) →
            (∀ rs, rsv = .inl rs → ∃ rs', rsv' = .inl rs' ∧ p.2.book = es.h.book) ∧
            (∀ sIdx, rsv = .inr sIdx →
              rsv' = .inr sIdx ∧ honOpt t es.h = some sIdx ∧ i' = e.1 ∧
              (∀ cnt hdr₀ e₀, (cnt, hdr₀, e₀) ∈ ((p.2.book sIdx).getD {}).fsTrans →
                cnt ≠ i' ∧ (cnt, hdr₀, e₀) ∈ ((es.h.book sIdx).getD {}).fsTrans) ∧
              (∀ sIdx', sIdx' ≠ sIdx → ((p.2.book sIdx').getD {}).fsTrans = ((es.h.book sIdx').getD {}).fsTrans) ∧
              (rec = none → ∃ c₀, sessCorrAt σ' sIdx = some c₀ ∧ c₀ < i'))))
      (((hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
        ⟨authH, some (l - 1), t⟩ false false).fsRecv es.g P t0 rsv hdr e rec).run h₁) := by
  dsimp only [hooksFSMulti]
  cases rsv with
  | inl rs =>
    refine PubMainRel.pure (Pt := Pt) fun σ₀ hσ₀ _ => ?_
    subst σ₀
    refine ⟨hca₁, fun sIdx => by rw [hbk₁]; exact hact.router_last sIdx,
      fun sIdx => by rw [hbk₁], hact.router_corr,
      fun sIdx hh => by rw [hbk₁]; exact (hact.non_hon_empty sIdx hh).2,
      fun _ sIdx => by rw [hbk₁],
      fun rsv' i' m' hEq => ⟨fun _ _ => ?_, fun _ h2 => nomatch h2⟩⟩
    cases hfs : (ShiftedFS Pt C ℓ encT idOf).receive rs hdr e with
    | none => simp [hfs] at hEq
    | some o =>
      simp only [hfs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hEq
      exact ⟨o.1, hEq.1.symm, hbk₁⟩
  | inr sIdx =>
    rcases h_sIdx_hon sIdx rfl with ⟨ht0, hPR, hhon_or_heal⟩
    subst t0
    intro rc σ₀ hσ₀ z hz hne_none
    subst σ₀
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
    dsimp only at hz
    generalize hm : List.find? _ ((h₁.book sIdx).getD {}).fsTrans = mf at hz
    cases mf with
    | some x =>
      have hx_mem : x ∈ ((es.h.book sIdx).getD {}).fsTrans ∧ x.2 = (hdr, e) := by
        rw [hbk₁] at hm
        have hmem := List.mem_of_find?_eq_some hm
        have hbeq := List.find?_some hm
        simp only [beq_iff_eq] at hbeq
        exact ⟨hmem, hbeq⟩
      have hhon : honOpt t es.h = some sIdx := by
        by_contra hne
        rw [(hact.non_hon_empty sIdx hne).2] at hx_mem
        exact nomatch hx_mem.1
      have hrec_some : rec ≠ none := by
        intro hnone
        have hnot := h_forged_not_trans hnone
        rcases (hact.hon_book sIdx hhon).1 x.1 x.2.1 x.2.2 hx_mem.1 with ⟨_, r, hr, hpos, hct⟩
        have hct' : r.ct = (hdr, e) := hct.trans hx_mem.2
        have hsend : r.pos.sender == P.other := by
          rw [hPR, other_receiverOf, hpos]; simp
        have hit : (es.g.inTransit P.other (hdr, e)).isSome = true := by
          unfold _root_.CryptoGames.SM.GameState.inTransit
          rw [List.find?_isSome]
          exact ⟨r, hr, by simp [hsend, hct']⟩
        rw [hit] at hnot; exact nomatch hnot
      have hx_cnt : x.1 = e.1 := by
        rcases (hact.hon_book sIdx hhon).1 x.1 x.2.1 x.2.2 hx_mem.1 with ⟨hcnt, _⟩
        have he_eq : x.2.2 = e := congrArg Prod.snd hx_mem.2
        exact hcnt.trans (congrArg Prod.fst he_eq)
      simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        StateT.run_pure, pure_bind, Bool.not_true, Option.isSome_some, StateT.run_bind] at hz
      simp only [runPubIdeal, simulateQ_bind, StateT.run_bind] at hz
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨v, hv, hzv⟩
      erw [liftFSMulti_run_query_eq (ℓ := ℓ) sIdx (.inl (.inr (hdr, e))) h₁] at hv
      rcases pubQuery_deliver_main C ℓ encT idOf N sIdx hdr e h₁ rc σ hv with ⟨hhv, hdl⟩
      rcases v with ⟨⟨⟨res, h₁'⟩, rc₁⟩, σ₁⟩
      dsimp only at hhv hdl hzv
      subst h₁'
      have hv_sync :
          (∀ s, sessLastIdx σ₁ s = ((es.h.book s).getD {}).fsCount) ∧
          (∀ s, sessCorrAt σ₁ s = sessCorrAt σ s) := by
        rcases hdl with ⟨_, rfl⟩ | ⟨st', rfl, hlast, hcorr, _⟩
        · exact ⟨hact.router_last, fun _ => rfl⟩
        · refine ⟨fun s => ?_, fun s => ?_⟩
          · by_cases hs : s = sIdx
            · subst s; simp only [sessLastIdx, Function.update_self]; exact hlast.trans (hact.router_last _)
            · simp only [sessLastIdx, Function.update_of_ne hs]; exact hact.router_last _
          · by_cases hs : s = sIdx
            · subst s; simp [sessCorrAt, Function.update_self, hcorr]
            · simp [sessCorrAt, Function.update_of_ne hs]
      have hv_corr : ∀ s c₀, sessCorrAt σ₁ s = some c₀ →
          honOpt t es.h = some s ∧ c₀ ≤ ((es.h.book s).getD {}).fsCount ∧
          (∃ lk, es.g.tL = some lk ∧ t ≤ lk) ∧
          (∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
            c₀ < r.pos.idx → r.pos ∈ es.g.comp) :=
        fun s c₀ hc => hact.router_corr s c₀ ((hv_sync.2 s).symm.trans hc)
      cases res with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure] at hzv
        rw [support_pure, Set.mem_singleton_iff] at hzv
        subst hzv; exact absurd rfl hne_none
      | some rr =>
        cases rr with
        | rejected =>
          simp only [StateT.run_pure, simulateQ_pure] at hzv
          rw [support_pure, Set.mem_singleton_iff] at hzv
          subst hzv
          dsimp only
          exact ⟨hca₁, fun s => by rw [hbk₁]; exact hv_sync.1 s, fun s => by rw [hbk₁], hv_corr,
            fun s hh => by rw [hbk₁]; exact (hact.non_hon_empty s hh).2,
            fun _ s => by rw [hbk₁],
            fun _ _ _ h => (by cases h)⟩
        | accepted i' mo' =>
          have hi'_eq : i' = e.1 := by
            rcases hdl with ⟨hnone, _⟩ | ⟨_, _, _, _, hacc⟩
            · exact nomatch hnone
            · exact hacc i' mo' rfl
          simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.getD_some,
            StateT.run_modify] at hzv
          let b_cur := (h₁.book sIdx).getD {}
          let b_new : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
            { b_cur with fsTrans := b_cur.fsTrans.filter (·.1 != x.1) }
          have hbook_cnt : ∀ s,
              (((Function.update h₁.book sIdx (some b_new)) s).getD {}).fsCount =
                ((es.h.book s).getD {}).fsCount := by
            intro s
            by_cases hs : s = sIdx
            · subst s; simp [Function.update_self, b_new, b_cur, hbk₁]
            · simp [Function.update_of_ne hs, hbk₁]
          have hbook_non_hon : ∀ s, honOpt t es.h ≠ some s →
              (((Function.update h₁.book sIdx (some b_new)) s).getD {}).fsTrans = [] := by
            intro s hne
            have hs : s ≠ sIdx := fun heq => hne (heq ▸ hhon)
            simp [Function.update_of_ne hs, hbk₁, (hact.non_hon_empty s hne).2]
          cases mo' <;> cases rec
          all_goals
            simp only [StateT.run_pure, pure_bind, simulateQ_pure] at hzv
            rw [support_pure, Set.mem_singleton_iff] at hzv
            subst hzv
            dsimp only
          · exact absurd rfl hne_none
          · refine ⟨hca₁, fun s => (hv_sync.1 s).trans (hbook_cnt s).symm,
              hbook_cnt, hv_corr, hbook_non_hon, fun h => (by cases h),
              fun rsv' i₀ m₀ hEq => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hEq
            rcases hEq with ⟨rfl, rfl, rfl⟩
            refine ⟨fun _ h => (nomatch h), fun s hs => ?_⟩
            injection hs with hs'; subst hs'
            refine ⟨rfl, hhon, hi'_eq, fun cnt hdr₀ e₀ hmem_f => ?_,
              fun s' hs' => by simp [Function.update_of_ne hs', hbk₁],
              fun hnone => absurd hnone hrec_some⟩
            simp only [Function.update_self, Option.getD_some, b_new, hbk₁,
              List.mem_filter, bne_iff_ne] at hmem_f
            exact ⟨by rw [hi'_eq, ← hx_cnt]; exact hmem_f.2, hmem_f.1⟩
          · refine ⟨hca₁, fun s => (hv_sync.1 s).trans (hbook_cnt s).symm,
              hbook_cnt, hv_corr, hbook_non_hon, fun h => (by cases h),
              fun rsv' i₀ m₀ hEq => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hEq
            rcases hEq with ⟨rfl, rfl, rfl⟩
            refine ⟨fun _ h => (nomatch h), fun s hs => ?_⟩
            injection hs with hs'; subst hs'
            refine ⟨rfl, hhon, hi'_eq, fun cnt hdr₀ e₀ hmem_f => ?_,
              fun s' hs' => by simp [Function.update_of_ne hs', hbk₁],
              fun hnone => absurd hnone hrec_some⟩
            simp only [Function.update_self, Option.getD_some, b_new, hbk₁,
              List.mem_filter, bne_iff_ne] at hmem_f
            exact ⟨by rw [hi'_eq, ← hx_cnt]; exact hmem_f.2, hmem_f.1⟩
          · refine ⟨hca₁, fun s => (hv_sync.1 s).trans (hbook_cnt s).symm,
              hbook_cnt, hv_corr, hbook_non_hon, fun h => (by cases h),
              fun rsv' i₀ m₀ hEq => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hEq
            rcases hEq with ⟨rfl, rfl, rfl⟩
            refine ⟨fun _ h => (nomatch h), fun s hs => ?_⟩
            injection hs with hs'; subst hs'
            refine ⟨rfl, hhon, hi'_eq, fun cnt hdr₀ e₀ hmem_f => ?_,
              fun s' hs' => by simp [Function.update_of_ne hs', hbk₁],
              fun hnone => absurd hnone hrec_some⟩
            simp only [Function.update_self, Option.getD_some, b_new, hbk₁,
              List.mem_filter, bne_iff_ne] at hmem_f
            exact ⟨by rw [hi'_eq, ← hx_cnt]; exact hmem_f.2, hmem_f.1⟩
    | none =>
      let rxTail : _root_.CryptoGames.SM.Engine.HM
          (_root_.CryptoGames.SM.Construction.FSMultiSpec
            (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256))
            Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
          (ShiftedHState Pt RSt I)
          (Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
            ℕ × (LibsignalMsgPublicPart × Plain ℓ)))) := do
        let res ← liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.injectQuery hdr e)
        match res with
        | none => pure none
        | some .rejected => pure (some none)
        | some (.accepted i mo') => do
          let s1 ← get
          if (false && true && !((s1.book sIdx).getD {}).sCorr &&
              decide (((s1.book sIdx).getD {}).fsCount < i)) then do
            modify (fun (s : ShiftedHState Pt RSt I) =>
              ({ s with lfWin := true } : ShiftedHState Pt RSt I))
            pure none
          else do
            modify (fun (s : ShiftedHState Pt RSt I) =>
              let b := (s.book sIdx).getD {}
              ({ s with book :=
                  (Function.update s.book sIdx
                    (some { b with fsTrans := b.fsTrans.filter (·.1 != i) })) } :
                ShiftedHState Pt RSt I))
            match mo', rec with
            | some m, _ => pure (some (some (.inr sIdx, i, m)))
            | none, some r => pure (some (some (.inr sIdx, i, r.msg)))
            | none, none => pure none
      have hAfterOk :
          ∃ (h_m : ShiftedHState Pt RSt I) (rc_m : ℕ → Bool) (σ_m : ℕ → Option (IdealHSt Pt ℓ)),
            (h_m.cache = es.h.cache ∧
              (∀ s, ((h_m.book s).getD {}).fsCount = ((es.h.book s).getD {}).fsCount) ∧
              (∀ s, ((h_m.book s).getD {}).fsTrans = ((es.h.book s).getD {}).fsTrans) ∧
              (∀ s, sessLastIdx σ_m s = ((es.h.book s).getD {}).fsCount) ∧
              (∀ s c₀, sessCorrAt σ_m s = some c₀ →
                honOpt t es.h = some s ∧
                c₀ ≤ ((es.h.book s).getD {}).fsCount ∧
                (∃ lk, es.g.tL = some lk ∧ t ≤ lk) ∧
                (∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
                  c₀ < r.pos.idx → r.pos ∈ es.g.comp))) ∧
            z ∈ support (runPubIdeal C ℓ encT idOf N false (rxTail.run h_m) rc_m σ_m) := by
        simp only [Option.isNone, Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
          Option.map_none, Option.getD_none] at hz
        by_cases hcond : (!_root_.CryptoGames.SM.healedBy es.g.tL (2 + Δcka) t &&
            !((h₁.book sIdx).getD {}).sCorr) = true
        · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hz
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          have hhon_s : honOpt t es.h = some sIdx := by
            rcases hhon_or_heal with hh | hheal
            · exact hh
            · rw [hcond.1] at hheal; exact nomatch hheal
          have htL_ge : ∃ lk, es.g.tL = some lk ∧ t ≤ lk :=
            tL_ge_of_not_healedBy hAdm hact.tL_mem hact.leaks_ok hcond.1
          simp only [runPubIdeal, simulateQ_bind, StateT.run_bind] at hz
          rw [MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨v₀, hv₀, hzv₀⟩
          erw [liftFSMulti_run_query_eq (ℓ := ℓ) sIdx (.inl (.inl (.inl (.inr ())))) h₁] at hv₀
          rcases pubQuery_corruptSender_main C ℓ encT idOf N sIdx h₁ rc σ hv₀ with
            ⟨hhv₀, st', hσ_eq, hlast_st', hcr_cases⟩
          rcases v₀ with ⟨⟨⟨res₀, h_a⟩, rc₁⟩, σ_m⟩
          dsimp only at hhv₀ hσ_eq hlast_st' hcr_cases hzv₀
          subst h_a σ_m
          cases res₀ with
          | none =>
            simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, pure_bind, simulateQ_pure] at hzv₀
            rw [support_pure, Set.mem_singleton_iff] at hzv₀
            subst hzv₀; exact absurd rfl hne_none
          | some _ =>
            rcases hcr_cases with ⟨hnone, _⟩ | ⟨_, _, hcorr_st'⟩
            · exact nomatch hnone
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hzv₀
            let b_corr : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
              { ((h₁.book sIdx).getD {}) with sCorr := true }
            let h_corr : ShiftedHState Pt RSt I :=
              { h₁ with book := Function.update h₁.book sIdx (some b_corr) }
            refine ⟨h_corr, rc₁, Function.update σ sIdx (some st'),
              ⟨hca₁,
                fun s => by
                  by_cases hs : s = sIdx
                  · subst s; simp [h_corr, b_corr, Function.update_self, hbk₁]
                  · simp [h_corr, Function.update_of_ne hs, hbk₁],
                fun s => by
                  by_cases hs : s = sIdx
                  · subst s; simp [h_corr, b_corr, Function.update_self, hbk₁]
                  · simp [h_corr, Function.update_of_ne hs, hbk₁],
                fun s => by
                  by_cases hs : s = sIdx
                  · subst s; simp only [sessLastIdx, Function.update_self]; exact hlast_st'.trans (hact.router_last _)
                  · simp only [sessLastIdx, Function.update_of_ne hs]; exact hact.router_last _,
                fun s c₀ hc => ?_⟩, ?_⟩
            · by_cases hs : s = sIdx
              · subst s
                simp only [sessCorrAt, Function.update_self] at hc
                rw [hcorr_st', Option.some.injEq] at hc
                cases hc_old : sessCorrAt σ sIdx with
                | some c_old =>
                  rw [hc_old, Option.getD_some] at hc; subst hc
                  exact hact.router_corr sIdx c_old hc_old
                | none =>
                  rw [hc_old, Option.getD_none, hact.router_last sIdx] at hc; subst hc
                  refine ⟨hhon_s, le_rfl, htL_ge, fun r hr hrs hre hlt => ?_⟩
                  have hle := ((hact.hon_book sIdx hhon_s).2 r hr hrs hre).2
                  omega
              · simp only [sessCorrAt, Function.update_of_ne hs] at hc
                exact hact.router_corr s c₀ hc
            · suffices h_eq : rxTail.run h_corr = _ by
                dsimp only [runPubIdeal]; rw [h_eq]; exact hzv₀
              dsimp only [rxTail]
              rw [StateT.run_bind]
              congr 1; funext p
              rcases p.1 with _ | (_ | ⟨i, mo'⟩)
              · rfl
              · rfl
              · cases mo' <;> cases rec <;> rfl
        · simp only [Bool.not_eq_true _ |>.mp hcond, Bool.false_eq_true, ↓reduceIte,
            Bool.not_true, StateT.run_pure, pure_bind] at hz
          refine ⟨h₁, rc, σ, ⟨hca₁, fun s => by rw [hbk₁], fun s => by rw [hbk₁],
            hact.router_last, hact.router_corr⟩, ?_⟩
          suffices h_eq : rxTail = _ by
            rw [h_eq]; exact hz
          dsimp only [rxTail]
          congr 1; funext res
          rcases res with _ | (_ | ⟨i, mo'⟩)
          · rfl
          · rfl
          · cases mo' <;> cases rec <;> rfl
      rcases hAfterOk with ⟨h_m, rc_m, σ_m, ⟨hca_m, hcnt_m, htr_m, hlast_m, hcorr_m⟩, hzv_ok⟩
      dsimp only [rxTail] at hzv_ok
      simp only [runPubIdeal, simulateQ_bind, StateT.run_bind] at hzv_ok
      rw [MonadAttach.mem_support_bind] at hzv_ok
      rcases hzv_ok with ⟨v, hv, hzv⟩
      erw [liftFSMulti_run_query_eq (ℓ := ℓ) sIdx (.inr (hdr, e)) h_m] at hv
      rcases pubQuery_inject_main C ℓ encT idOf N sIdx hdr e h_m rc_m σ_m hv with ⟨hhv, hij⟩
      rcases v with ⟨⟨⟨res, h₁'⟩, rc₁⟩, σ₁⟩
      dsimp only at hhv hij hzv
      subst h₁'
      have hv_sync :
          (∀ s, sessLastIdx σ₁ s = ((es.h.book s).getD {}).fsCount) ∧
          (∀ s, sessCorrAt σ₁ s = sessCorrAt σ_m s) := by
        rcases hij with ⟨_, rfl⟩ | ⟨st', rfl, hlast, hcorr, _⟩
        · exact ⟨hlast_m, fun _ => rfl⟩
        · refine ⟨fun s => ?_, fun s => ?_⟩
          · by_cases hs : s = sIdx
            · subst s; simp only [sessLastIdx, Function.update_self]; exact hlast.trans (hlast_m _)
            · simp only [sessLastIdx, Function.update_of_ne hs]; exact hlast_m _
          · by_cases hs : s = sIdx
            · subst s; simp [sessCorrAt, Function.update_self, hcorr]
            · simp [sessCorrAt, Function.update_of_ne hs]
      have hv_corr : ∀ s c₀, sessCorrAt σ₁ s = some c₀ →
          honOpt t es.h = some s ∧ c₀ ≤ ((es.h.book s).getD {}).fsCount ∧
          (∃ lk, es.g.tL = some lk ∧ t ≤ lk) ∧
          (∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
            c₀ < r.pos.idx → r.pos ∈ es.g.comp) :=
        fun s c₀ hc => hcorr_m s c₀ ((hv_sync.2 s).symm.trans hc)
      cases res with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure] at hzv
        rw [support_pure, Set.mem_singleton_iff] at hzv
        subst hzv; exact absurd rfl hne_none
      | some rr =>
        cases rr with
        | rejected =>
          simp only [StateT.run_pure, simulateQ_pure] at hzv
          rw [support_pure, Set.mem_singleton_iff] at hzv
          subst hzv
          dsimp only
          exact ⟨hca_m, fun s => by rw [hcnt_m]; exact hv_sync.1 s, hcnt_m, hv_corr,
            fun s hh => (htr_m s).trans (hact.non_hon_empty s hh).2,
            fun _ => htr_m,
            fun _ _ _ h => (by cases h)⟩
        | accepted i' mo' =>
          have hacc_props : i' = e.1 ∧ ∃ c₀, sessCorrAt σ_m sIdx = some c₀ ∧ c₀ < i' := by
            rcases hij with ⟨hnotacc, _⟩ | ⟨_, _, _, _, hacc⟩
            · exact False.elim (hnotacc i' mo' rfl)
            · exact hacc i' mo' rfl
          rcases hacc_props with ⟨hi'_eq, c₀, hc₀_m, hlt⟩
          have hc₀ : sessCorrAt σ₁ sIdx = some c₀ := (hv_sync.2 sIdx).trans hc₀_m
          have hhon : honOpt t es.h = some sIdx := (hcorr_m sIdx c₀ hc₀_m).1
          simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none,
            StateT.run_modify] at hzv
          let b_cur := (h_m.book sIdx).getD {}
          let b_new : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
            { b_cur with fsTrans := b_cur.fsTrans.filter (·.1 != i') }
          have hbook_cnt : ∀ s,
              (((Function.update h_m.book sIdx (some b_new)) s).getD {}).fsCount =
                ((es.h.book s).getD {}).fsCount := by
            intro s
            by_cases hs : s = sIdx
            · subst s; simp [Function.update_self, b_new, b_cur, hcnt_m]
            · simp [Function.update_of_ne hs, hcnt_m]
          have hbook_non_hon : ∀ s, honOpt t es.h ≠ some s →
              (((Function.update h_m.book sIdx (some b_new)) s).getD {}).fsTrans = [] := by
            intro s hne
            have hs : s ≠ sIdx := fun heq => hne (heq ▸ hhon)
            simp [Function.update_of_ne hs, htr_m, (hact.non_hon_empty s hne).2]
          cases mo' <;> cases rec
          all_goals
            simp only [StateT.run_pure, pure_bind, simulateQ_pure] at hzv
            rw [support_pure, Set.mem_singleton_iff] at hzv
            subst hzv
            dsimp only
          · exact absurd rfl hne_none
          · refine ⟨hca_m, fun s => (hv_sync.1 s).trans (hbook_cnt s).symm,
              hbook_cnt, hv_corr, hbook_non_hon, fun h => (by cases h),
              fun rsv' i₀ m₀ hEq => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hEq
            rcases hEq with ⟨rfl, rfl, rfl⟩
            refine ⟨fun _ h => (nomatch h), fun s hs => ?_⟩
            injection hs with hs'; subst hs'
            refine ⟨rfl, hhon, hi'_eq, fun cnt hdr₀ e₀ hmem_f => ?_,
              fun s' hs' => by simp [Function.update_of_ne hs', htr_m],
              fun _ => ⟨c₀, hc₀, hlt⟩⟩
            simp only [Function.update_self, Option.getD_some, b_new, htr_m,
              List.mem_filter, bne_iff_ne] at hmem_f
            exact ⟨hmem_f.2, hmem_f.1⟩
          · refine ⟨hca_m, fun s => (hv_sync.1 s).trans (hbook_cnt s).symm,
              hbook_cnt, hv_corr, hbook_non_hon, fun h => (by cases h),
              fun rsv' i₀ m₀ hEq => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hEq
            rcases hEq with ⟨rfl, rfl, rfl⟩
            refine ⟨fun _ h => (nomatch h), fun s hs => ?_⟩
            injection hs with hs'; subst hs'
            refine ⟨rfl, hhon, hi'_eq, fun cnt hdr₀ e₀ hmem_f => ?_,
              fun s' hs' => by simp [Function.update_of_ne hs', htr_m],
              fun _ => ⟨c₀, hc₀, hlt⟩⟩
            simp only [Function.update_self, Option.getD_some, b_new, htr_m,
              List.mem_filter, bne_iff_ne] at hmem_f
            exact ⟨hmem_f.2, hmem_f.1⟩
          · refine ⟨hca_m, fun s => (hv_sync.1 s).trans (hbook_cnt s).symm,
              hbook_cnt, hv_corr, hbook_non_hon, fun h => (by cases h),
              fun rsv' i₀ m₀ hEq => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hEq
            rcases hEq with ⟨rfl, rfl, rfl⟩
            refine ⟨fun _ h => (nomatch h), fun s hs => ?_⟩
            injection hs with hs'; subst hs'
            refine ⟨rfl, hhon, hi'_eq, fun cnt hdr₀ e₀ hmem_f => ?_,
              fun s' hs' => by simp [Function.update_of_ne hs', htr_m],
              fun _ => ⟨c₀, hc₀, hlt⟩⟩
            simp only [Function.update_self, Option.getD_some, b_new, htr_m,
              List.mem_filter, bne_iff_ne] at hmem_f
            exact ⟨hmem_f.2, hmem_f.1⟩

private theorem shiftedActiveInv_of_book_shrink {Γ Pt RSt I : Type} {ℓ l t : ℕ}
    {es : ShiftedEState Γ Pt RSt I ℓ} {σ σ' : ℕ → Option (IdealHSt Pt ℓ)}
    (hact : ShiftedActiveInv l t es σ)
    (h' : ShiftedHState Pt RSt I)
    (hca : h'.cache = es.h.cache)
    (hlast : ∀ s, sessLastIdx σ' s = ((h'.book s).getD {}).fsCount)
    (hcnt : ∀ s, ((h'.book s).getD {}).fsCount = ((es.h.book s).getD {}).fsCount)
    (hcorr : ∀ sIdx c₀, sessCorrAt σ' sIdx = some c₀ →
      honOpt t es.h = some sIdx ∧
      c₀ ≤ ((es.h.book sIdx).getD {}).fsCount ∧
      (∃ lk, es.g.tL = some lk ∧ t ≤ lk) ∧
      (∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
        c₀ < r.pos.idx → r.pos ∈ es.g.comp))
    (hnh : ∀ s, honOpt t es.h ≠ some s → ((h'.book s).getD {}).fsTrans = [])
    (hsub : ∀ s, honOpt t es.h = some s →
      ∀ cnt hdr₀ e₀, (cnt, hdr₀, e₀) ∈ ((h'.book s).getD {}).fsTrans →
        (cnt, hdr₀, e₀) ∈ ((es.h.book s).getD {}).fsTrans) :
    ShiftedActiveInv l t { es with h := h' } σ' := by
  have hhon_eq : honOpt t h' = honOpt t es.h := by simp [honOpt, hca]
  exact
    { abort_false := hact.abort_false
      win_false := hact.win_false
      st_id := hact.st_id
      st_tcur := hact.st_tcur
      tL_mem := hact.tL_mem
      leaks_ok := hact.leaks_ok
      trans_hdr := hact.trans_hdr
      cache_pre := fun hep => by rw [hca]; exact hact.cache_pre hep
      cache_t_some := fun Tc σc k optIdx hc => hact.cache_t_some Tc σc k optIdx (hca ▸ hc)
      cache_other_none := fun t0 hne Tc σc k optIdx hc =>
        hact.cache_other_none t0 hne Tc σc k optIdx (hca ▸ hc)
      vS_inr := fun Q sIdx hv => by rw [hhon_eq]; exact hact.vS_inr Q sIdx hv
      sender_at_t := fun hep => by
        rcases hact.sender_at_t hep with ⟨sIdx, hh, hv, hi⟩
        exact ⟨sIdx, hhon_eq.trans hh, hv, hi.trans (hcnt sIdx).symm⟩
      sender_cka_at_t := fun hep => by rw [hca]; exact hact.sender_cka_at_t hep
      trans_t_hdr := fun r hr hs he => by rw [hca]; exact hact.trans_t_hdr r hr hs he
      vR_target := fun Q rsv hv => by rw [hhon_eq]; exact hact.vR_target Q rsv hv
      vR_other := hact.vR_other
      non_hon_empty := fun sIdx hh =>
        ⟨(hcnt sIdx).trans (hact.non_hon_empty sIdx (hhon_eq ▸ hh)).1,
         hnh sIdx (hhon_eq ▸ hh)⟩
      hon_book := fun sIdx hh => by
        have hh₀ := hhon_eq ▸ hh
        refine ⟨fun cnt hdr₀ e₀ hm => (hact.hon_book sIdx hh₀).1 cnt hdr₀ e₀ (hsub sIdx hh₀ cnt hdr₀ e₀ hm),
          fun r hr hs he => ?_⟩
        rcases (hact.hon_book sIdx hh₀).2 r hr hs he with ⟨h1, h2⟩
        exact ⟨h1, Nat.le_trans h2 (Nat.le_of_eq (hcnt sIdx).symm)⟩
      router_last := hlast
      router_corr := fun sIdx c₀ hc => by
        rcases hcorr sIdx c₀ hc with ⟨hh, hle, htL, hcp⟩
        exact ⟨hhon_eq.trans hh, Nat.le_trans hle (Nat.le_of_eq (hcnt sIdx).symm), htL, hcp⟩ }

-- Full `vRecv` step lemma on `ShiftedActiveInv`:
private theorem vRecv_hooksFSMulti_main_step {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (es : ShiftedEState Γ Pt RSt I ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hact : ShiftedActiveInv l t es σ)
    (P : Party) (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec : Option (_root_.CryptoGames.SM.Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (h_rogue_guard : c.1.1 = es.g.epoch P + 1 → c.1.1 = t → P.sendsIn t = false →
      (∃ r ∈ es.g.trans, r.pos.sender = P.other ∧ r.ct.1 = c.1 ∧ r.pos.epoch = t) ∨
        es.g.safeInj 2 = true)
    (h_forged_not_trans : rec = none → (es.g.inTransit P.other (c.1, c.2)).isSome = false) :
    PubMainRel C ℓ encT idOf N
      (fun σ₀ => σ₀ = σ)
      (fun p σ' =>
        (p.1 = some none → ShiftedActiveInv l t { es with h := p.2 } σ') ∧
        (∀ st' t' i' m', p.1 = some (some (st', t', i', m')) →
          t' = c.1.1 ∧ P.sendsIn t' = false ∧ t' ≤ es.g.epoch P + 1 ∧
          st'.id = P ∧ st'.tcur = max (es.g.epoch P) t' ∧
          st'.curCkaMsg = (es.g.st P).curCkaMsg ∧ st'.vS = (es.g.st P).vS ∧
          p.2.cache = es.h.cache ∧
          (∀ s, sessLastIdx σ' s = ((p.2.book s).getD {}).fsCount) ∧
          (∀ s, ((p.2.book s).getD {}).fsCount = ((es.h.book s).getD {}).fsCount) ∧
          (∀ sIdx c₀, sessCorrAt σ' sIdx = some c₀ →
            honOpt t es.h = some sIdx ∧
            c₀ ≤ ((es.h.book sIdx).getD {}).fsCount ∧
            (∃ lk, es.g.tL = some lk ∧ t ≤ lk) ∧
            (∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
              c₀ < r.pos.idx → r.pos ∈ es.g.comp)) ∧
          (∀ s, honOpt t es.h ≠ some s → ((p.2.book s).getD {}).fsTrans = []) ∧
          (∀ rsv0, st'.vR t = some rsv0 → ∃ sIdx, rsv0 = .inr sIdx ∧ honOpt t es.h = some sIdx) ∧
          (∀ t0 rsv0, t0 ≠ t → st'.vR t0 = some rsv0 → ∃ rs, rsv0 = .inl rs) ∧
          (∀ sIdx, honOpt t es.h = some sIdx →
            ∀ cnt hdr₀ e₀, (cnt, hdr₀, e₀) ∈ ((p.2.book sIdx).getD {}).fsTrans →
              (cnt, hdr₀, e₀) ∈ ((es.h.book sIdx).getD {}).fsTrans) ∧
          (t' = t → P = Party.receiverOf t ∧ i' = c.2.1 ∧
            (∃ sIdx, honOpt t es.h = some sIdx) ∧
            (∀ sIdx, honOpt t es.h = some sIdx →
              ∀ cnt hdr₀ e₀, (cnt, hdr₀, e₀) ∈ ((p.2.book sIdx).getD {}).fsTrans → cnt ≠ i') ∧
            (rec = none → ∃ sIdx c₀, honOpt t es.h = some sIdx ∧
              sessCorrAt σ' sIdx = some c₀ ∧ c₀ < i'))))
      ((vRecv (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
        ⟨authH, some (l - 1), t⟩ false false) es.g P (es.g.st P) c rec).run es.h) := by
  by_cases hbad : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true
  · unfold vRecv
    rw [hact.st_id P, hact.st_tcur P]
    simp only [hbad, ↓reduceIte, StateT.run_pure]
    refine PubMainRel.pure (Pt := Pt) fun σ₀ hσ₀ => ?_
    subst σ₀
    exact ⟨fun _ => shiftedActiveInv_of_book_shrink hact es.h rfl hact.router_last
      (fun _ => rfl) hact.router_corr (fun s hh => (hact.non_hon_empty s hh).2)
      (fun _ _ _ _ _ hm => hm),
      fun _ _ _ _ h => nomatch h⟩
  · have hbad_f : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = false :=
      Bool.not_eq_true _ |>.mp hbad
    let hk := hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
      ⟨authH, some (l - 1), t⟩ false false
    let step1 : _root_.CryptoGames.SM.Engine.HM
        (_root_.CryptoGames.SM.Construction.FSMultiSpec
          (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256))
          Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (ShiftedHState Pt RSt I)
        (Option (Option (VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
          (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)))) :=
      if c.1.1 = es.g.epoch P + 1 then
        match c.1.2 with
        | none => pure (some none)
        | some Tn => do
          match ← hk.startRecv es.g P c.1.1 (es.g.st P).γ (es.g.st P).root Tn with
          | none => pure none
          | some none => pure (some none)
          | some (some (γ', σ', rs)) =>
            pure (some (some { (es.g.st P) with tcur := c.1.1, γ := γ', root := σ',
                                                vR := Function.update (es.g.st P).vR c.1.1 (some rs) }))
      else pure (some (some (es.g.st P)))
    let step2 : Option (Option (VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
          (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))) →
        _root_.CryptoGames.SM.Engine.HM
          (_root_.CryptoGames.SM.Construction.FSMultiSpec
            (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256))
            Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
          (ShiftedHState Pt RSt I)
          (Option (Option (VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
            (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
            ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))) :=
      fun s₁? =>
        match s₁? with
        | none => pure none
        | some none => pure (some none)
        | some (some s₁) =>
          match s₁.vR c.1.1 with
          | none => pure (some none)
          | some v => do
            match ← hk.fsRecv es.g P c.1.1 v c.1 c.2 rec with
            | none => pure none
            | some none => pure (some none)
            | some (some (v', i, m)) =>
              pure (some (some ({ s₁ with vR := Function.update s₁.vR c.1.1 (some v') },
                c.1.1, i, m)))
    have hvRecvEq :
        (vRecv hk es.g P (es.g.st P) c rec).run es.h =
          (step1.run es.h >>= fun p => (step2 p.1).run p.2) := by
      unfold vRecv
      dsimp only [step1, step2]
      rw [hact.st_id P, hact.st_tcur P]
      simp only [hbad_f, Bool.false_eq_true, ↓reduceIte]
      by_cases hnew : c.1.1 = es.g.epoch P + 1
      · simp only [hnew, ↓reduceIte]
        cases hc2 : c.1.2 with
        | none => simp [StateT.run_pure, StateT.run_bind, pure_bind]
        | some Tn =>
          simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
          refine bind_congr fun ⟨x, h₁⟩ => ?_
          rcases x with _ | ⟨_ | ⟨γ', σ', rs⟩⟩
          · simp [StateT.run_pure, pure_bind]
          · simp [StateT.run_pure, pure_bind]
          · simp only [StateT.run_pure, pure_bind, Function.update_self, StateT.run_bind, bind_assoc]
            refine bind_congr fun ⟨y, h₂⟩ => ?_
            rcases y with _ | ⟨_ | ⟨v', i, m⟩⟩ <;> simp [StateT.run_pure]
      · simp only [hnew, ↓reduceIte, StateT.run_pure, pure_bind]
        cases hvR0 : (es.g.st P).vR c.1.1 with
        | none => simp [StateT.run_pure]
        | some v =>
          simp only [StateT.run_bind, bind_assoc]
          refine bind_congr fun ⟨y, h₂⟩ => ?_
          rcases y with _ | ⟨_ | ⟨v', i, m⟩⟩ <;> simp [StateT.run_pure]
    change PubMainRel C ℓ encT idOf N _ _ ((vRecv hk es.g P (es.g.st P) c rec).run es.h)
    rw [hvRecvEq]
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hbad_f
    rcases hbad_f with ⟨hnsend, hle_ep⟩
    have hStep1 :
        PubMainRel C ℓ encT idOf N
          (fun σ₀ => σ₀ = σ)
          (fun p₁ σ₁ =>
            σ₁ = σ ∧ p₁.2.cache = es.h.cache ∧ p₁.2.book = es.h.book ∧
            (∀ s₁, p₁.1 = some (some s₁) →
              s₁.id = P ∧ s₁.tcur = max (es.g.epoch P) c.1.1 ∧
              s₁.curCkaMsg = (es.g.st P).curCkaMsg ∧ s₁.vS = (es.g.st P).vS ∧
              (∀ t0, t0 ≠ c.1.1 → s₁.vR t0 = (es.g.st P).vR t0) ∧
              (c.1.1 = t → ∀ rsv, s₁.vR t = some rsv →
                ∃ sIdx, rsv = .inr sIdx ∧
                  (honOpt t es.h = some sIdx ∨
                    _root_.CryptoGames.SM.healedBy es.g.tL (2 + Δcka) t = true)) ∧
              (c.1.1 ≠ t → ∀ rsv, s₁.vR c.1.1 = some rsv → ∃ rs, rsv = .inl rs)))
          (step1.run es.h) := by
      dsimp only [step1, hk]
      split_ifs with hnew
      · cases hc2 : c.1.2 with
        | none =>
          exact PubMainRel.pure fun _ hσ₀ => ⟨hσ₀, rfl, rfl, fun _ h => nomatch h⟩
        | some Tn =>
          dsimp only [hooksFSMulti]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          cases hca0 : es.h.cache c.1.1 with
          | none =>
            dsimp only
            by_cases hct_eq : c.1.1 = t
            · have hdec_t : decide (c.1.1 = t) = true := decide_eq_true hct_eq
              simp only [Bool.false_eq_true, hdec_t, Bool.and_true, ↓reduceIte]
              split_ifs
              · simp only [StateT.run_pure, pure_bind]
                exact PubMainRel.pure fun _ hσ₀ => ⟨hσ₀, rfl, rfl, fun _ h => nomatch h⟩
              · simp only [StateT.run_bind, bind_assoc]
                refine (lookupMultiF_main_preserves C ℓ encT idOf N _ es.h).bind fun ⟨_, h_a⟩ => ?_
                refine (regSessMulti_main_preserves C ℓ encT idOf N _ h_a).bind fun ⟨sIdx, h_b⟩ => ?_
                simp only [StateT.run_pure, pure_bind]
                refine PubMainRel.pure fun _ ⟨hca_b, hbk_b, hca_a, hbk_a, hσ₀⟩ =>
                  ⟨hσ₀, hca_b.trans hca_a, hbk_b.trans hbk_a, fun s₁ hs₁ => ?_⟩
                injection hs₁ with hs₁'; injection hs₁' with hs₁''; subst hs₁''
                refine ⟨hact.st_id P, by dsimp only; omega, rfl, rfl,
                  fun t0 hne => Function.update_of_ne hne _ _,
                  fun ht rsv hrsv => ?_, fun hnt => absurd hct_eq hnt⟩
                simp only [ht, Function.update_self, Option.some.injEq] at hrsv
                refine ⟨sIdx, hrsv.symm, Or.inr ?_⟩
                rcases h_rogue_guard hnew ht (ht ▸ hnsend) with ⟨r, hr_mem, hr_send, hr_ct1, hr_ep⟩ | hsafe2
                · have hPR : P = Party.receiverOf t := eq_receiverOf_of_sendsIn_false (ht ▸ hnsend)
                  have hrs_t : r.pos.sender = Party.senderOf t := by
                    rw [hr_send, hPR, other_receiverOf]
                  rcases hact.trans_t_hdr r hr_mem hrs_t hr_ep with ⟨Tc, σc, k, sIdx₀, hca_t, hr_hdr⟩
                  rw [ht, hca_t] at hca0
                  exact nomatch hca0
                · exact healedBy_of_safeInj_two hAdm hact.tL_mem hact.leaks_ok (hnew.symm.trans ht) hsafe2
              · simp only [StateT.run_pure, pure_bind]
                exact PubMainRel.pure fun _ hσ₀ => ⟨hσ₀, rfl, rfl, fun _ h => nomatch h⟩
            · have hdec_f : decide (c.1.1 = t) = false := decide_eq_false hct_eq
              simp only [Bool.false_eq_true, hdec_f, Bool.and_false, ↓reduceIte,
                StateT.run_pure, pure_bind]
              exact PubMainRel.pure fun _ hσ₀ => ⟨hσ₀, rfl, rfl, fun _ h => nomatch h⟩
          | some q =>
            rcases q with ⟨Tc, σc, k, optIdx⟩
            by_cases hTc : Tc = Tn
            · simp only [hTc, ↓reduceIte, StateT.run_pure, pure_bind]
              refine PubMainRel.pure fun _ hσ₀ => ⟨hσ₀, rfl, rfl, fun s₁ hs₁ => ?_⟩
              injection hs₁ with hs₁'; injection hs₁' with hs₁''; subst hs₁''
              refine ⟨hact.st_id P, by dsimp only; omega, rfl, rfl,
                fun t0 hne => Function.update_of_ne hne _ _,
                fun ht rsv hrsv => ?_, fun hnt rsv hrsv => ?_⟩
              · subst ht
                rcases hact.cache_t_some Tc σc k optIdx hca0 with ⟨sIdx, rfl⟩
                simp only [Function.update_self, Option.some.injEq] at hrsv
                exact ⟨sIdx, hrsv.symm, Or.inl (by simp [honOpt, hca0])⟩
              · have hopt := hact.cache_other_none c.1.1 hnt Tc σc k optIdx hca0
                subst hopt
                simp only [Function.update_self, Option.some.injEq] at hrsv
                exact ⟨_, hrsv.symm⟩
            · simp only [hTc, ↓reduceIte]
              by_cases hct_eq : c.1.1 = t
              · have hdec_t : decide (c.1.1 = t) = true := decide_eq_true hct_eq
                simp only [Bool.false_eq_true, hdec_t, Bool.and_true, ↓reduceIte]
                split_ifs
                · simp only [StateT.run_pure, pure_bind]
                  exact PubMainRel.pure fun _ hσ₀ => ⟨hσ₀, rfl, rfl, fun _ h => nomatch h⟩
                · simp only [StateT.run_bind, bind_assoc]
                  refine (lookupMultiF_main_preserves C ℓ encT idOf N _ es.h).bind fun ⟨_, h_a⟩ => ?_
                  refine (regSessMulti_main_preserves C ℓ encT idOf N _ h_a).bind fun ⟨sIdx, h_b⟩ => ?_
                  simp only [StateT.run_pure, pure_bind]
                  refine PubMainRel.pure fun _ ⟨hca_b, hbk_b, hca_a, hbk_a, hσ₀⟩ =>
                    ⟨hσ₀, hca_b.trans hca_a, hbk_b.trans hbk_a, fun s₁ hs₁ => ?_⟩
                  injection hs₁ with hs₁'; injection hs₁' with hs₁''; subst hs₁''
                  refine ⟨hact.st_id P, by dsimp only; omega, rfl, rfl,
                    fun t0 hne => Function.update_of_ne hne _ _,
                    fun ht rsv hrsv => ?_, fun hnt => absurd hct_eq hnt⟩
                  simp only [ht, Function.update_self, Option.some.injEq] at hrsv
                  refine ⟨sIdx, hrsv.symm, Or.inr ?_⟩
                  rcases h_rogue_guard hnew ht (ht ▸ hnsend) with ⟨r, hr_mem, hr_send, hr_ct1, hr_ep⟩ | hsafe2
                  · have hPR : P = Party.receiverOf t := eq_receiverOf_of_sendsIn_false (ht ▸ hnsend)
                    have hrs_t : r.pos.sender = Party.senderOf t := by
                      rw [hr_send, hPR, other_receiverOf]
                    rcases hact.trans_t_hdr r hr_mem hrs_t hr_ep with ⟨Tc', σc', k', sIdx₀, hca_t, hr_hdr⟩
                    have hc1_eq : c.1 = (t, some Tc') := hr_ct1.symm.trans hr_hdr
                    have hTn : Tc' = Tn := by
                      have h2_eq : c.1.2 = some Tc' := congrArg Prod.snd hc1_eq
                      rw [hc2] at h2_eq
                      exact (Option.some.inj h2_eq).symm
                    rw [ht, hca_t] at hca0
                    injection hca0 with hq
                    rcases Prod.mk.inj hq with ⟨hTc_eq, _⟩
                    exact absurd (hTc_eq.symm.trans hTn) hTc
                  · exact healedBy_of_safeInj_two hAdm hact.tL_mem hact.leaks_ok (hnew.symm.trans ht) hsafe2
                · simp only [StateT.run_pure, pure_bind]
                  exact PubMainRel.pure fun _ hσ₀ => ⟨hσ₀, rfl, rfl, fun _ h => nomatch h⟩
              · have hdec_f : decide (c.1.1 = t) = false := decide_eq_false hct_eq
                simp only [Bool.false_eq_true, hdec_f, Bool.and_false, ↓reduceIte,
                  StateT.run_pure, pure_bind]
                exact PubMainRel.pure fun _ hσ₀ => ⟨hσ₀, rfl, rfl, fun _ h => nomatch h⟩
      · refine PubMainRel.pure fun _ hσ₀ => ⟨hσ₀, rfl, rfl, fun s₁ hs₁ => ?_⟩
        injection hs₁ with hs₁'; injection hs₁' with hs₁''; subst hs₁''
        have hle_cur : c.1.1 ≤ es.g.epoch P := by omega
        exact ⟨hact.st_id P, by rw [hact.st_tcur P]; omega, rfl, rfl,
          fun _ _ => rfl,
          fun ht rsv hrsv => by
            subst ht; rcases hact.vR_target P rsv hrsv with ⟨sIdx, rfl, hh⟩
            exact ⟨sIdx, rfl, Or.inl hh⟩,
          fun hnt rsv hrsv => hact.vR_other P c.1.1 rsv hnt hrsv⟩
    refine hStep1.bind fun ⟨s₁?, h₁⟩ => ?_
    dsimp only [step2, hk]
    cases s₁? with
    | none =>
      exact PubMainRel.pure fun _ _ => ⟨(fun h => nomatch h), fun _ _ _ _ h => nomatch h⟩
    | some o =>
      cases o with
      | none =>
        refine PubMainRel.pure fun σ₁ ⟨hσ₁, hca₁, hbk₁, _⟩ => ?_
        subst σ₁
        exact ⟨fun _ => shiftedActiveInv_of_book_shrink hact h₁ hca₁
          (fun s => by rw [hbk₁]; exact hact.router_last s)
          (fun s => by rw [hbk₁]) hact.router_corr
          (fun s hh => by rw [hbk₁]; exact (hact.non_hon_empty s hh).2)
          (fun s _ _ _ _ hm => by rw [hbk₁] at hm; exact hm),
          fun _ _ _ _ h => nomatch h⟩
      | some s₁ =>
        dsimp only
        have hMonoPre : ∀ {α : Type} {Post0 : α → (ℕ → Option (IdealHSt Pt ℓ)) → Prop}
            {comp : OracleComp (PubMultiSpec Pt ℓ) α},
            ((h₁.cache = es.h.cache ∧ h₁.book = es.h.book ∧
              s₁.id = P ∧ s₁.tcur = max (es.g.epoch P) c.1.1 ∧
              s₁.curCkaMsg = (es.g.st P).curCkaMsg ∧ s₁.vS = (es.g.st P).vS ∧
              (∀ t0, t0 ≠ c.1.1 → s₁.vR t0 = (es.g.st P).vR t0) ∧
              (c.1.1 = t → ∀ rsv, s₁.vR t = some rsv →
                ∃ sIdx, rsv = .inr sIdx ∧
                  (honOpt t es.h = some sIdx ∨
                    _root_.CryptoGames.SM.healedBy es.g.tL (2 + Δcka) t = true)) ∧
              (c.1.1 ≠ t → ∀ rsv, s₁.vR c.1.1 = some rsv → ∃ rs, rsv = .inl rs)) →
              PubMainRel C ℓ encT idOf N (fun σ₀ => σ₀ = σ) Post0 comp) →
            PubMainRel C ℓ encT idOf N
              (fun σ₁ => σ₁ = σ ∧ h₁.cache = es.h.cache ∧ h₁.book = es.h.book ∧
                ∀ s₁', some (some s₁) = some (some s₁') →
                  s₁'.id = P ∧ s₁'.tcur = max (es.g.epoch P) c.1.1 ∧
                  s₁'.curCkaMsg = (es.g.st P).curCkaMsg ∧ s₁'.vS = (es.g.st P).vS ∧
                  (∀ t0, t0 ≠ c.1.1 → s₁'.vR t0 = (es.g.st P).vR t0) ∧
                  (c.1.1 = t → ∀ rsv, s₁'.vR t = some rsv →
                    ∃ sIdx, rsv = .inr sIdx ∧
                      (honOpt t es.h = some sIdx ∨
                        _root_.CryptoGames.SM.healedBy es.g.tL (2 + Δcka) t = true)) ∧
                  (c.1.1 ≠ t → ∀ rsv, s₁'.vR c.1.1 = some rsv → ∃ rs, rsv = .inl rs))
              Post0 comp := by
          intro _ _ _ h rc σ₁ ⟨hσ₁, hca₁, hbk₁, hs₁_fn⟩ z hz
          exact h ⟨hca₁, hbk₁, hs₁_fn s₁ rfl⟩ rc σ₁ hσ₁ z hz
        refine hMonoPre ?_
        rintro ⟨hca₁, hbk₁, hid₁, htcur₁, hcur₁, hvS₁, hvR_ne₁, hvR_t₁, hvR_nt₁⟩
        cases hvR : s₁.vR c.1.1 with
        | none =>
          dsimp only
          refine PubMainRel.pure fun σ₀ hσ₀ => ?_
          subst σ₀
          exact ⟨fun _ => shiftedActiveInv_of_book_shrink hact h₁ hca₁
            (fun s => by rw [hbk₁]; exact hact.router_last s)
            (fun s => by rw [hbk₁]) hact.router_corr
            (fun s hh => by rw [hbk₁]; exact (hact.non_hon_empty s hh).2)
            (fun s _ _ _ _ hm => by rw [hbk₁] at hm; exact hm),
            fun _ _ _ _ h => nomatch h⟩
        | some v =>
          dsimp only
          have hv_inr_hon : ∀ sIdx, v = .inr sIdx → c.1.1 = t ∧ P = Party.receiverOf t ∧
              (honOpt t es.h = some sIdx ∨
                _root_.CryptoGames.SM.healedBy es.g.tL (2 + Δcka) t = true) := by
            intro sIdx hv_eq
            have hct : c.1.1 = t := by
              by_contra hnt
              rcases hvR_nt₁ hnt v hvR with ⟨rs, hrs⟩
              rw [hv_eq] at hrs; exact nomatch hrs
            rcases hvR_t₁ hct v (hct ▸ hvR) with ⟨sIdx', hv_eq', hdisj⟩
            rw [hv_eq] at hv_eq'
            injection hv_eq' with hs_eq; subst hs_eq
            exact ⟨hct, eq_receiverOf_of_sendsIn_false (hct ▸ hnsend), hdisj⟩
          simp only [StateT.run_bind]
          refine (fsRecv_hooksFSMulti_main_step C ℓ encT idOf N cka prng Δcka l t authH hAdm
            es σ hact P c.1.1 v c.1 c.2 rec hv_inr_hon h_forged_not_trans h₁ hca₁ hbk₁).bind
            fun ⟨ro, h₂⟩ => ?_
          cases ro with
          | none =>
            exact PubMainRel.pure fun _ _ => ⟨(fun h => nomatch h), fun _ _ _ _ h => nomatch h⟩
          | some r_in =>
            cases r_in with
            | none =>
              refine PubMainRel.pure fun σ' hpost => ?_
              rcases hpost (by simp) with ⟨hca₂, hlast₂, hcnt₂, hcorr₂, hnh₂, hbk_none, _⟩
              exact ⟨fun _ => shiftedActiveInv_of_book_shrink hact h₂ hca₂ hlast₂ hcnt₂ hcorr₂ hnh₂
                (fun s _ _ _ _ hm => by rw [hbk_none rfl s] at hm; exact hm),
                fun _ _ _ _ h => nomatch h⟩
            | some triple =>
              rcases triple with ⟨v', i', m'⟩
              refine PubMainRel.pure fun σ' hpost => ?_
              rcases hpost (by simp) with ⟨hca₂, hlast₂, hcnt₂, hcorr₂, hnh₂, _, hacc_fn⟩
              rcases hacc_fn v' i' m' rfl with ⟨hacc_inl, hacc_inr⟩
              refine ⟨(fun h => nomatch h), fun st'' t' i₀ m₀ hEq => ?_⟩
              injection hEq with hEq'; injection hEq' with hEq''
              rcases Prod.mk.inj hEq'' with ⟨rfl, hrest⟩
              rcases Prod.mk.inj hrest with ⟨rfl, hrest'⟩
              rcases Prod.mk.inj hrest' with ⟨rfl, rfl⟩
              refine ⟨rfl, hnsend, hle_ep, hid₁, htcur₁, hcur₁, hvS₁, hca₂, hlast₂, hcnt₂,
                hcorr₂, hnh₂,
                fun rsv0 hrsv0 => ?_, fun t0 rsv0 hnt0 hrsv0 => ?_,
                fun sIdx hhon cnt hdr₀ e₀ hm => ?_, fun ht => ?_⟩
              · by_cases hct : c.1.1 = t
                · subst hct
                  simp only [Function.update_self, Option.some.injEq] at hrsv0
                  subst hrsv0
                  rcases hvR_t₁ rfl v hvR with ⟨sIdx₀, hv_eq, _⟩
                  rcases hacc_inr sIdx₀ hv_eq with ⟨hrsv', hhon₀, _⟩
                  exact ⟨sIdx₀, hrsv', hhon₀⟩
                · simp only [Function.update_of_ne (Ne.symm hct)] at hrsv0
                  rw [hvR_ne₁ t (Ne.symm hct)] at hrsv0
                  exact hact.vR_target P rsv0 hrsv0
              · by_cases hct0 : t0 = c.1.1
                · subst hct0
                  simp only [Function.update_self, Option.some.injEq] at hrsv0
                  subst hrsv0
                  rcases hvR_nt₁ hnt0 v hvR with ⟨rs₀, hv_eq⟩
                  rcases hacc_inl rs₀ hv_eq with ⟨rs', hrsv', _⟩
                  exact ⟨rs', hrsv'⟩
                · simp only [Function.update_of_ne hct0] at hrsv0
                  rw [hvR_ne₁ t0 hct0] at hrsv0
                  exact hact.vR_other P t0 rsv0 hnt0 hrsv0
              · cases v with
                | inl rs₀ =>
                  rcases hacc_inl rs₀ rfl with ⟨_, _, hbk₂⟩
                  rw [hbk₂] at hm; exact hm
                | inr sIdx₀ =>
                  rcases hacc_inr sIdx₀ rfl with ⟨_, _, _, hsub₀, hbk_ne, _⟩
                  by_cases hs : sIdx = sIdx₀
                  · subst hs; exact (hsub₀ cnt hdr₀ e₀ hm).2
                  · rw [hbk_ne sIdx hs] at hm; exact hm
              · rcases hvR_t₁ ht v (ht ▸ hvR) with ⟨sIdx₀, hv_eq, _⟩
                rcases hacc_inr sIdx₀ hv_eq with ⟨_, hhon₀, hi'_eq, hsub₀, _, hforged₀⟩
                refine ⟨eq_receiverOf_of_sendsIn_false (ht ▸ hnsend), hi'_eq, ⟨sIdx₀, hhon₀⟩,
                  fun sIdx hhon cnt hdr₀ e₀ hm => ?_, fun hnone => ?_⟩
                · have hs : sIdx = sIdx₀ := Option.some.inj (hhon.symm.trans hhon₀)
                  subst hs
                  exact (hsub₀ cnt hdr₀ e₀ hm).1
                · rcases hforged₀ hnone with ⟨c₀, hc₀, hlt⟩
                  exact ⟨sIdx₀, c₀, hhon₀, hc₀, hlt⟩

-- Preserving `ShiftedActiveInv` across `commitE` (`es.g.accept P st' pos`):
private theorem accept_main_preserves {Γ Pt RSt I : Type} {ℓ l t : ℕ}
    {es : ShiftedEState Γ Pt RSt I ℓ} {σ σ' : ℕ → Option (IdealHSt Pt ℓ)}
    (hact : ShiftedActiveInv l t es σ)
    (P : Party)
    (st' : VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (pos : _root_.CryptoGames.SM.Pos)
    (h₂ : ShiftedHState Pt RSt I)
    (hnsend : P.sendsIn pos.epoch = false)
    (hle_ep : pos.epoch ≤ es.g.epoch P + 1)
    (hid' : st'.id = P)
    (htcur' : st'.tcur = max (es.g.epoch P) pos.epoch)
    (hcur' : st'.curCkaMsg = (es.g.st P).curCkaMsg)
    (hvS' : st'.vS = (es.g.st P).vS)
    (hca₂ : h₂.cache = es.h.cache)
    (hlast₂ : ∀ s, sessLastIdx σ' s = ((h₂.book s).getD {}).fsCount)
    (hcnt₂ : ∀ s, ((h₂.book s).getD {}).fsCount = ((es.h.book s).getD {}).fsCount)
    (hcorr₂ : ∀ sIdx c₀, sessCorrAt σ' sIdx = some c₀ →
      honOpt t es.h = some sIdx ∧
      c₀ ≤ ((es.h.book sIdx).getD {}).fsCount ∧
      (∃ lk, es.g.tL = some lk ∧ t ≤ lk) ∧
      (∀ r ∈ es.g.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
        c₀ < r.pos.idx → r.pos ∈ es.g.comp))
    (hnh₂ : ∀ s, honOpt t es.h ≠ some s → ((h₂.book s).getD {}).fsTrans = [])
    (hvR_t' : ∀ rsv0, st'.vR t = some rsv0 → ∃ sIdx, rsv0 = .inr sIdx ∧ honOpt t es.h = some sIdx)
    (hvR_nt' : ∀ t0 rsv0, t0 ≠ t → st'.vR t0 = some rsv0 → ∃ rs, rsv0 = .inl rs)
    (hsub₂ : ∀ sIdx, honOpt t es.h = some sIdx →
      ∀ cnt hdr₀ e₀, (cnt, hdr₀, e₀) ∈ ((h₂.book sIdx).getD {}).fsTrans →
        (cnt, hdr₀, e₀) ∈ ((es.h.book sIdx).getD {}).fsTrans)
    (hno_pos : pos.epoch = t →
      ∀ sIdx, honOpt t es.h = some sIdx →
        ∀ cnt hdr₀ e₀, (cnt, hdr₀, e₀) ∈ ((h₂.book sIdx).getD {}).fsTrans → cnt ≠ pos.idx) :
    let s₁ := es.g.accept P st' pos
    ShiftedActiveInv l t
      { es with g := { s₁ with st := Function.update s₁.st P st' }, h := h₂ } σ' := by
  intro s₁
  have hhon_eq : honOpt t h₂ = honOpt t es.h := by simp [honOpt, hca₂]
  have hep_le : ∀ Q, es.g.epoch Q ≤ s₁.epoch Q := by
    intro Q
    by_cases hQP : Q = P
    · subst hQP; simp [s₁, _root_.CryptoGames.SM.GameState.accept,
        _root_.CryptoGames.SM.GameState.delete, Function.update_self]
    · simp [s₁, _root_.CryptoGames.SM.GameState.accept,
        _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hQP]
  refine
    { abort_false := hact.abort_false
      win_false := hact.win_false
      st_id := fun Q => by
        by_cases hQP : Q = P
        · subst hQP; simp [Function.update_self, hid']
        · simp [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hQP, hact.st_id Q]
      st_tcur := fun Q => by
        by_cases hQP : Q = P
        · subst hQP; simp [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, Function.update_self, htcur']
        · simp [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hQP, hact.st_tcur Q]
      tL_mem := hact.tL_mem
      leaks_ok := hact.leaks_ok
      trans_hdr := fun r hr => by
        simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
          _root_.CryptoGames.SM.GameState.delete, List.mem_filter] at hr
        rcases hact.trans_hdr r hr.1 with ⟨h1, h2⟩
        exact ⟨h1, le_trans h2 (hep_le r.pos.sender)⟩
      cache_pre := fun hep' => by
        rw [hca₂]
        exact hact.cache_pre (lt_of_le_of_lt (hep_le (Party.senderOf t)) hep')
      cache_t_some := fun Tc σc k optIdx hc => hact.cache_t_some Tc σc k optIdx (hca₂ ▸ hc)
      cache_other_none := fun t0 hne Tc σc k optIdx hc =>
        hact.cache_other_none t0 hne Tc σc k optIdx (hca₂ ▸ hc)
      vS_inr := fun Q sIdx hv => by
        have hv₀ : (es.g.st Q).vS = some (.inr sIdx) := by
          by_cases hQP : Q = P
          · subst hQP; simp only [Function.update_self, hvS'] at hv; exact hv
          · simpa [s₁, _root_.CryptoGames.SM.GameState.accept,
              _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hQP] using hv
        rcases hact.vS_inr Q sIdx hv₀ with ⟨hQS, hhon, hepQ⟩
        refine ⟨hQS, hhon_eq.trans hhon, ?_⟩
        by_cases hQP : Q = P
        · subst hQP
          simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, Function.update_self]
          rcases hepQ with hep_t | hep_t1
          · rw [hep_t] at hle_ep ⊢
            by_cases hpos : pos.epoch ≤ t
            · left; omega
            · right; omega
          · rw [hep_t1] at hle_ep ⊢
            have hne_t2 : pos.epoch ≠ t + 2 := by
              intro heq2
              rw [heq2, hQS, sendsIn_add_two, sendsIn_senderOf] at hnsend
              exact nomatch hnsend
            right; omega
        · simpa [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hQP] using hepQ
      sender_at_t := fun hep' => by
        have hep₀ : es.g.epoch (Party.senderOf t) = t := by
          by_cases hSP : Party.senderOf t = P
          · rw [hSP] at hep' ⊢
            simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
              _root_.CryptoGames.SM.GameState.delete, Function.update_self] at hep'
            by_cases hlt : es.g.epoch P < t
            · have hpeq : pos.epoch = t := by omega
              rw [← hSP, hpeq, sendsIn_senderOf] at hnsend
              exact nomatch hnsend
            · omega
          · simpa [s₁, _root_.CryptoGames.SM.GameState.accept,
              _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hSP] using hep'
        rcases hact.sender_at_t hep₀ with ⟨sIdx, hhon, hvS₀, hidx₀⟩
        refine ⟨sIdx, hhon_eq.trans hhon, ?_, hidx₀.trans (hcnt₂ sIdx).symm⟩
        by_cases hSP : Party.senderOf t = P
        · subst hSP; simp [Function.update_self, hvS', hvS₀]
        · simp [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hSP, hvS₀]
      sender_cka_at_t := fun hep' => by
        have hep₀ : es.g.epoch (Party.senderOf t) = t := by
          by_cases hSP : Party.senderOf t = P
          · rw [hSP] at hep' ⊢
            simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
              _root_.CryptoGames.SM.GameState.delete, Function.update_self] at hep'
            by_cases hlt : es.g.epoch P < t
            · have hpeq : pos.epoch = t := by omega
              rw [← hSP, hpeq, sendsIn_senderOf] at hnsend
              exact nomatch hnsend
            · omega
          · simpa [s₁, _root_.CryptoGames.SM.GameState.accept,
              _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hSP] using hep'
        rcases hact.sender_cka_at_t hep₀ with ⟨Tc, σc, k, sIdx, hca_t, hcur₀⟩
        refine ⟨Tc, σc, k, sIdx, hca₂ ▸ hca_t, ?_⟩
        by_cases hSP : Party.senderOf t = P
        · subst hSP; simp [Function.update_self, hcur', hcur₀]
        · simp [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hSP, hcur₀]
      trans_t_hdr := fun r hr hs he => by
        simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
          _root_.CryptoGames.SM.GameState.delete, List.mem_filter] at hr
        rw [hca₂]
        exact hact.trans_t_hdr r hr.1 hs he
      vR_target := fun Q rsv hv => by
        rw [hhon_eq]
        by_cases hQP : Q = P
        · subst hQP; simp only [Function.update_self] at hv; exact hvR_t' rsv hv
        · simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hQP] at hv
          exact hact.vR_target Q rsv hv
      vR_other := fun Q t0 rsv hnt0 hv => by
        by_cases hQP : Q = P
        · subst hQP; simp only [Function.update_self] at hv; exact hvR_nt' t0 rsv hnt0 hv
        · simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, Function.update_of_ne hQP] at hv
          exact hact.vR_other Q t0 rsv hnt0 hv
      non_hon_empty := fun sIdx hh =>
        ⟨(hcnt₂ sIdx).trans (hact.non_hon_empty sIdx (hhon_eq ▸ hh)).1,
         hnh₂ sIdx (hhon_eq ▸ hh)⟩
      hon_book := fun sIdx hh => by
        have hh₀ := hhon_eq ▸ hh
        refine ⟨fun cnt hdr₀ e₀ hm => ?_, fun r hr hs he => ?_⟩
        · rcases (hact.hon_book sIdx hh₀).1 cnt hdr₀ e₀ (hsub₂ sIdx hh₀ cnt hdr₀ e₀ hm) with
            ⟨hcnt_eq, r, hr_mem, hr_pos, hr_ct⟩
          refine ⟨hcnt_eq, r, ?_, hr_pos, hr_ct⟩
          simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, List.mem_filter, bne_iff_ne]
          refine ⟨hr_mem, fun heq_pos => ?_⟩
          have hep_eq : pos.epoch = t := by
            have := congrArg _root_.CryptoGames.SM.Pos.epoch (hr_pos.symm.trans heq_pos)
            exact this.symm
          have hidx_eq : cnt = pos.idx :=
            congrArg _root_.CryptoGames.SM.Pos.idx (hr_pos.symm.trans heq_pos)
          exact hno_pos hep_eq sIdx hh₀ cnt hdr₀ e₀ hm hidx_eq
        · simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
            _root_.CryptoGames.SM.GameState.delete, List.mem_filter] at hr
          rcases (hact.hon_book sIdx hh₀).2 r hr.1 hs he with ⟨h1, h2⟩
          exact ⟨h1, Nat.le_trans h2 (Nat.le_of_eq (hcnt₂ sIdx).symm)⟩
      router_last := hlast₂
      router_corr := fun sIdx c₀ hc => by
        rcases hcorr₂ sIdx c₀ hc with ⟨hh, hle, htL, hcp⟩
        refine ⟨hhon_eq.trans hh, Nat.le_trans hle (Nat.le_of_eq (hcnt₂ sIdx).symm), htL, fun r hr hs he hlt => ?_⟩
        simp only [s₁, _root_.CryptoGames.SM.GameState.accept,
          _root_.CryptoGames.SM.GameState.delete, List.mem_filter] at hr ⊢
        exact ⟨hcp r hr.1 hs he hlt, hr.2⟩ }

private theorem PubMainRel.liftH {Γ Pt RSt I α : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (x : _root_.CryptoGames.SM.Engine.HM
      (_root_.CryptoGames.SM.Construction.FSMultiSpec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (ShiftedHState Pt RSt I) α)
    (es : ShiftedEState Γ Pt RSt I ℓ)
    {Pre : (ℕ → Option (IdealHSt Pt ℓ)) → Prop}
    {Post : (α × ShiftedHState Pt RSt I) → (ℕ → Option (IdealHSt Pt ℓ)) → Prop}
    (hx : PubMainRel C ℓ encT idOf N Pre Post (x.run es.h)) :
    PubMainRel C ℓ encT idOf N Pre
      (fun pes σ' => pes.2 = { es with h := pes.2.h } ∧ Post (pes.1, pes.2.h) σ')
      ((liftH x).run es) := by
  rw [liftH_run_eq_la]
  exact hx.bind fun ⟨a, h'⟩ => PubMainRel.pure (Pt := Pt) fun _ hp => ⟨rfl, hp⟩

-- Shared second-half helper for `vSend` (`fsSend` + `s₁.record`) in `transmitE`:
private theorem fsSend_and_record_main_safe {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (es : ShiftedEState Γ Pt RSt I ℓ)
    (s₁ : _root_.CryptoGames.SM.Engine.Ctx Γ Pt RSt
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (st₁ : VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (m : LibsignalMsgPublicPart × Plain ℓ)
    (h₁ : ShiftedHState Pt RSt I)
    (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hes_ab : es.abort = false)
    (hs₁_win : s₁.win = false)
    (hs₁_id : ∀ Q, Q ≠ P → (s₁.st Q).id = Q)
    (hs₁_tcur : ∀ Q, Q ≠ P → (s₁.st Q).tcur = s₁.epoch Q)
    (hst₁_id : st₁.id = P)
    (hst₁_tcur : st₁.tcur = s₁.epoch P)
    (hs₁_send : P.sendsIn (s₁.epoch P) = true)
    (hs₁_tL : ∀ lk, s₁.tL = some lk → lk ∈ s₁.leaks)
    (hs₁_leaks : ∀ lk ∈ s₁.leaks, lk ≤ l - 1 ∨ t ≤ lk)
    (hs₁_trans : ∀ r ∈ s₁.trans, r.ct.1.1 = r.pos.epoch ∧ r.pos.epoch ≤ s₁.epoch r.pos.sender)
    (hca_pre : s₁.epoch (Party.senderOf t) < t → h₁.cache t = none)
    (hca_t : ∀ Tc σc k optIdx, h₁.cache t = some (Tc, σc, k, optIdx) → ∃ sIdx, optIdx = some sIdx)
    (hca_nt : ∀ t0, t0 ≠ t → ∀ Tc σc k optIdx, h₁.cache t0 = some (Tc, σc, k, optIdx) → optIdx = none)
    (hvS_other : ∀ Q, Q ≠ P → ∀ sIdx, (s₁.st Q).vS = some (.inr sIdx) →
      Q = Party.senderOf t ∧ honOpt t h₁ = some sIdx ∧ (s₁.epoch Q = t ∨ s₁.epoch Q = t + 1))
    (hst₁_vS_inr : ∀ sIdx, st₁.vS = some (.inr sIdx) →
      P = Party.senderOf t ∧ honOpt t h₁ = some sIdx ∧ s₁.epoch P = t ∧
      s₁.idx P = ((h₁.book sIdx).getD {}).fsCount)
    (hsender_t : s₁.epoch (Party.senderOf t) = t →
      (P = Party.senderOf t → ∃ sIdx, st₁.vS = some (.inr sIdx)) ∧
      (P ≠ Party.senderOf t → ∃ sIdx, honOpt t h₁ = some sIdx ∧
        (s₁.st (Party.senderOf t)).vS = some (.inr sIdx) ∧
        s₁.idx (Party.senderOf t) = ((h₁.book sIdx).getD {}).fsCount))
    (hsender_cka_t : s₁.epoch (Party.senderOf t) = t →
      (P = Party.senderOf t → ∃ Tc σc k sIdx,
        h₁.cache t = some (Tc, σc, k, some sIdx) ∧ st₁.curCkaMsg = some Tc) ∧
      (P ≠ Party.senderOf t → ∃ Tc σc k sIdx,
        h₁.cache t = some (Tc, σc, k, some sIdx) ∧
        (s₁.st (Party.senderOf t)).curCkaMsg = some Tc))
    (htrans_t_hdr : ∀ r ∈ s₁.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
      ∃ Tc σc k sIdx, h₁.cache t = some (Tc, σc, k, some sIdx) ∧ r.ct.1 = (t, some Tc))
    (hvR_t : ∀ Q rsv, (Function.update s₁.st P st₁ Q).vR t = some rsv →
      ∃ sIdx, rsv = .inr sIdx ∧ honOpt t h₁ = some sIdx)
    (hvR_nt : ∀ Q t0 rsv, t0 ≠ t → (Function.update s₁.st P st₁ Q).vR t0 = some rsv →
      ∃ rs, rsv = .inl rs)
    (hnh : ∀ sIdx, honOpt t h₁ ≠ some sIdx →
      ((h₁.book sIdx).getD {}).fsCount = 0 ∧ ((h₁.book sIdx).getD {}).fsTrans = [])
    (hhon_bk : ∀ sIdx, honOpt t h₁ = some sIdx →
      (∀ cnt hdr₀ e₀, (cnt, hdr₀, e₀) ∈ ((h₁.book sIdx).getD {}).fsTrans →
        cnt = e₀.1 ∧ ∃ r ∈ s₁.trans, r.pos = ⟨Party.senderOf t, t, cnt⟩ ∧ r.ct = (hdr₀, e₀)) ∧
      (∀ r ∈ s₁.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
        r.ct.2.1 = r.pos.idx ∧ r.pos.idx ≤ ((h₁.book sIdx).getD {}).fsCount))
    (hlast : ∀ sIdx, sessLastIdx σ sIdx = ((h₁.book sIdx).getD {}).fsCount)
    (hcorr : ∀ sIdx c₀, sessCorrAt σ sIdx = some c₀ →
      honOpt t h₁ = some sIdx ∧ c₀ ≤ ((h₁.book sIdx).getD {}).fsCount ∧
      (∃ lk, s₁.tL = some lk ∧ t ≤ lk) ∧
      (∀ r ∈ s₁.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
        c₀ < r.pos.idx → r.pos ∈ s₁.comp)) :
    let hdr : Header Pt := (st₁.tcur, st₁.curCkaMsg)
    let step2 : _root_.CryptoGames.SM.Engine.HM
        (_root_.CryptoGames.SM.Construction.FSMultiSpec
          (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256))
          Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (ShiftedHState Pt RSt I)
        (Option (VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
          (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
          (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) :=
      match st₁.vS with
      | none => pure (some (st₁, (hdr, default)))
      | some v => do
        match ← (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
            ⟨authH, some (l - 1), t⟩ false false).fsSend s₁ P st₁.tcur v hdr m none with
        | none => pure none
        | some (v', e) => pure (some ({ st₁ with vS := some v' }, (hdr, e)))
    PubMainRel C ℓ encT idOf N
      (fun σ₀ => σ₀ = σ)
      (fun p σ' =>
        match p.1 with
        | none => True
        | some (st', c) =>
          ShiftedActiveInv l t
            { es with
              g := s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ false
              h := p.2 } σ')
      (step2.run h₁) := by
  intro hdr step2
  have hNonTarget : ∀ (st' : VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (e_out : ℕ × LibsignalCiphertextWithSalt32),
      s₁.epoch P ≠ t →
      st'.id = P → st'.tcur = s₁.epoch P → st'.vR = st₁.vR →
      (∀ sIdx, st'.vS ≠ some (.inr sIdx)) →
      ShiftedActiveInv l t
        { es with
          g := s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, (hdr, e_out)⟩ false
          h := h₁ } σ := by
    intro st' e_out hnep hid' htcur' hvR' hnvS'
    refine
      { abort_false := hes_ab
        win_false := hs₁_win
        st_id := fun Q => by
          by_cases hQP : Q = P
          · subst hQP; simp [_root_.CryptoGames.SM.GameState.record, Function.update_self, hid']
          · simp [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP, hs₁_id Q hQP]
        st_tcur := fun Q => by
          by_cases hQP : Q = P
          · subst hQP; simp [_root_.CryptoGames.SM.GameState.record, Function.update_self, htcur']
          · simp [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP, hs₁_tcur Q hQP]
        tL_mem := hs₁_tL
        leaks_ok := hs₁_leaks
        trans_hdr := fun r hr => by
          simp only [_root_.CryptoGames.SM.GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr_old
          · exact ⟨hst₁_tcur, le_rfl⟩
          · exact hs₁_trans r hr_old
        cache_pre := hca_pre
        cache_t_some := hca_t
        cache_other_none := hca_nt
        vS_inr := fun Q sIdx hv => by
          by_cases hQP : Q = P
          · subst hQP
            simp only [_root_.CryptoGames.SM.GameState.record, Function.update_self] at hv
            exact absurd hv (hnvS' sIdx)
          · simp only [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP] at hv ⊢
            exact hvS_other Q hQP sIdx hv
        sender_at_t := fun hep_t => by
          have hPS : P ≠ Party.senderOf t := fun hEq => hnep (hEq ▸ hep_t)
          rcases (hsender_t hep_t).2 hPS with ⟨sIdx, hh, hv, hi⟩
          refine ⟨sIdx, hh, ?_, ?_⟩
          · simpa [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hPS.symm] using hv
          · simpa [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hPS.symm] using hi
        sender_cka_at_t := fun hep_t => by
          have hPS : P ≠ Party.senderOf t := fun hEq => hnep (hEq ▸ hep_t)
          rcases (hsender_cka_t hep_t).2 hPS with ⟨Tc, σc, k, sIdx, hca_t_eq, hcur_eq⟩
          refine ⟨Tc, σc, k, sIdx, hca_t_eq, ?_⟩
          simpa [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hPS.symm] using hcur_eq
        trans_t_hdr := fun r hr hs he => by
          simp only [_root_.CryptoGames.SM.GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr_old
          · exact absurd he hnep
          · exact htrans_t_hdr r hr_old hs he
        vR_target := fun Q rsv hv => by
          by_cases hQP : Q = P
          · subst hQP
            simp only [_root_.CryptoGames.SM.GameState.record, Function.update_self, hvR'] at hv
            exact hvR_t Q rsv (by simpa [Function.update_self] using hv)
          · simp only [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP] at hv
            exact hvR_t Q rsv (by simpa [Function.update_of_ne hQP] using hv)
        vR_other := fun Q t0 rsv hnt0 hv => by
          by_cases hQP : Q = P
          · subst hQP
            simp only [_root_.CryptoGames.SM.GameState.record, Function.update_self, hvR'] at hv
            exact hvR_nt Q t0 rsv hnt0 (by simpa [Function.update_self] using hv)
          · simp only [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP] at hv
            exact hvR_nt Q t0 rsv hnt0 (by simpa [Function.update_of_ne hQP] using hv)
        non_hon_empty := hnh
        hon_book := fun sIdx hh => by
          refine ⟨fun cnt hdr₀ e₀ hm => ?_, fun r hr hs he => ?_⟩
          · rcases (hhon_bk sIdx hh).1 cnt hdr₀ e₀ hm with ⟨h1, r, hr, hpos, hct⟩
            exact ⟨h1, r, List.mem_cons_of_mem _ hr, hpos, hct⟩
          · simp only [_root_.CryptoGames.SM.GameState.record, List.mem_cons] at hr
            rcases hr with rfl | hr_old
            · exact absurd he hnep
            · exact (hhon_bk sIdx hh).2 r hr_old hs he
        router_last := hlast
        router_corr := fun sIdx c₀ hc => by
          rcases hcorr sIdx c₀ hc with ⟨hh, hle, htL, hcp⟩
          refine ⟨hh, hle, htL, fun r hr hs he hlt => ?_⟩
          simp only [_root_.CryptoGames.SM.GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr_old
          · exact absurd he hnep
          · have hmem := hcp r hr_old hs he hlt
            simp only [_root_.CryptoGames.SM.GameState.record]
            split_ifs
            · exact hmem
            · exact List.mem_cons_of_mem _ hmem }
  cases hvS : st₁.vS with
  | none =>
    have hnep : s₁.epoch P ≠ t := by
      intro hep_t
      have hPS : P = Party.senderOf t := eq_senderOf_of_sendsIn (hep_t ▸ hs₁_send)
      rcases (hsender_t (hPS ▸ hep_t)).1 hPS with ⟨sIdx, hv⟩
      rw [hvS] at hv; exact nomatch hv
    dsimp only [step2]
    rw [hvS]
    simp only [StateT.run_pure]
    refine PubMainRel.pure (Pt := Pt) fun σ₀ hσ₀ => ?_
    subst σ₀
    exact hNonTarget st₁ default hnep hst₁_id hst₁_tcur rfl (fun _ h => by rw [hvS] at h; exact nomatch h)
  | some v =>
    cases v with
    | inl ss =>
      have hnep : s₁.epoch P ≠ t := by
        intro hep_t
        have hPS : P = Party.senderOf t := eq_senderOf_of_sendsIn (hep_t ▸ hs₁_send)
        rcases (hsender_t (hPS ▸ hep_t)).1 hPS with ⟨sIdx, hv⟩
        rw [hvS] at hv; exact nomatch hv
      dsimp only [step2, hooksFSMulti]
      rw [hvS]
      simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      refine PubMainRel.pure (Pt := Pt) fun σ₀ hσ₀ => ?_
      subst σ₀
      exact hNonTarget _ _ hnep hst₁_id hst₁_tcur rfl (fun _ h => nomatch h)
    | inr sIdx =>
      rcases hst₁_vS_inr sIdx hvS with ⟨hPS, hhon, hep_t, hidx_eq⟩
      let okStep : _root_.CryptoGames.SM.Engine.HM
          (_root_.CryptoGames.SM.Construction.FSMultiSpec
            (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256))
            Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
          (ShiftedHState Pt RSt I) Bool :=
        if !(s₁.safeCh (2 + Δcka) P) && !((h₁.book sIdx).getD {}).sCorr then
          if false then pure false
          else do
            match ← liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.corruptSenderQuery
                (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
                (AssocData := Header Pt) (Message := LibsignalMsgPublicPart × Plain ℓ)
                (Ciphertext := ℕ × LibsignalCiphertextWithSalt32)) with
            | none => pure false
            | some _ =>
              modify fun s =>
                let b := (s.book sIdx).getD {}
                { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
              pure true
        else pure true
      let kSend : Bool → _root_.CryptoGames.SM.Engine.HM
          (_root_.CryptoGames.SM.Construction.FSMultiSpec
            (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256))
            Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
          (ShiftedHState Pt RSt I)
          (Option (VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
            (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
            (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) :=
        fun ok =>
          if !ok then pure none
          else do
            match ← liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.transmitQuery
                (SenderState := RatchetSenderState (BitVec 256))
                (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
                hdr m) with
            | none => pure none
            | some e => do
              modify (fun s : ShiftedHState Pt RSt I =>
                let b := (s.book sIdx).getD {}
                let cnt' := b.fsCount + 1
                let b' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                  { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
                { s with book := Function.update s.book sIdx (some b') })
              pure (some ({ st₁ with vS := some (.inr sIdx) }, (hdr, e)))
      have hSendRunEq :
          step2.run h₁ = (okStep.run h₁ >>= fun p => (kSend p.1).run p.2) := by
        dsimp only [step2, hooksFSMulti, okStep, kSend]
        rw [hvS]
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        by_cases hcond : (!(s₁.safeCh (2 + Δcka) P) && !((h₁.book sIdx).getD {}).sCorr) = true
        · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
            pure_bind, bind_assoc]
          refine bind_congr fun ⟨res, h_a⟩ => ?_
          cases res with
          | none =>
            simp [Bool.not_false, StateT.run_bind, StateT.run_pure, pure_bind]
          | some _ =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
              StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc]
            refine bind_congr fun ⟨e?, h_b⟩ => ?_
            cases e? <;>
              simp [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc]
        · have hcondF : (!(s₁.safeCh (2 + Δcka) P) && !((h₁.book sIdx).getD {}).sCorr) = false :=
            Bool.not_eq_true _ |>.mp hcond
          simp only [hcondF, Bool.false_eq_true, Bool.not_true, ↓reduceIte, StateT.run_bind,
            StateT.run_pure, pure_bind, bind_assoc]
          refine bind_congr fun ⟨e?, h_b⟩ => ?_
          cases e? <;>
            simp [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc]
      rw [hSendRunEq]
      have hOkStep :
          PubMainRel C ℓ encT idOf N
            (fun σ₀ => σ₀ = σ)
            (fun p_m σ_m =>
              p_m.1 = true →
                p_m.2.cache = h₁.cache ∧
                (∀ s, s ≠ sIdx → p_m.2.book s = h₁.book s) ∧
                ((p_m.2.book sIdx).getD {}).fsCount = ((h₁.book sIdx).getD {}).fsCount ∧
                ((p_m.2.book sIdx).getD {}).fsTrans = ((h₁.book sIdx).getD {}).fsTrans ∧
                (∀ s, sessLastIdx σ_m s = ((h₁.book s).getD {}).fsCount) ∧
                (∀ s c₀, sessCorrAt σ_m s = some c₀ →
                  honOpt t h₁ = some s ∧
                  c₀ ≤ ((h₁.book s).getD {}).fsCount ∧
                  (∃ lk, s₁.tL = some lk ∧ t ≤ lk) ∧
                  (∀ r ∈ s₁.trans, r.pos.sender = Party.senderOf t → r.pos.epoch = t →
                    c₀ < r.pos.idx → r.pos ∈ s₁.comp)))
            (okStep.run h₁) := by
        dsimp only [okStep]
        by_cases hcond : (!(s₁.safeCh (2 + Δcka) P) && !((h₁.book sIdx).getD {}).sCorr) = true
        · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          have htL_ge : ∃ lk, s₁.tL = some lk ∧ t ≤ lk :=
            tL_ge_of_not_safeCh hAdm (hPS ▸ hep_t) hs₁_tL hs₁_leaks (hPS ▸ hcond.1)
          intro rc σ₀ hσ₀ z hz
          subst σ₀
          simp only [runPubIdeal, simulateQ_bind, StateT.run_bind] at hz
          rw [MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨v, hv, hzv⟩
          have hCr :
              ((liftFSMulti
                (SS := RatchetSenderState (BitVec 256))
                (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
                (E := ℕ × LibsignalCiphertextWithSalt32) sIdx
                (_root_.CryptoGames.FSAEAD.corruptSenderQuery)).run h₁) =
              (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, .inl (.inl (.inl (.inr ())))⟩) >>=
                fun a => pure (a, h₁)) := by
            simp only [_root_.CryptoGames.FSAEAD.corruptSenderQuery]
            exact liftFSMulti_run_query_eq sIdx (.inl (.inl (.inl (.inr ())))) h₁
          rw [hCr] at hv
          rcases pubQuery_corruptSender_main C ℓ encT idOf N sIdx h₁ rc σ hv with
            ⟨hhv, st', hσ₁_eq, hlast_st', hcr_cases⟩
          rcases v with ⟨⟨⟨res, h₁'⟩, rc₁⟩, σ₁⟩
          dsimp only at hhv hσ₁_eq hlast_st' hcr_cases hzv
          subst h₁'; subst σ₁
          cases res with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure] at hzv
            rw [support_pure, Set.mem_singleton_iff] at hzv
            subst hzv
            intro hfalse; exact nomatch hfalse
          | some _ =>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure] at hzv
            rw [support_pure, Set.mem_singleton_iff] at hzv
            subst hzv
            intro _
            refine ⟨rfl, fun s hs => Function.update_of_ne hs _ _,
              by simp [Function.update_self], by simp [Function.update_self],
              fun s => ?_, fun s c₀ hc => ?_⟩
            · by_cases hs : s = sIdx
              · subst s
                unfold sessLastIdx
                simp only [Function.update_self]
                rw [hlast_st', hlast]
              · unfold sessLastIdx
                simp only [Function.update_of_ne hs]
                exact hlast s
            · rcases hcr_cases with ⟨hnone, _⟩ | ⟨_, _, hcorr_st'⟩
              · exact nomatch hnone
              · by_cases hs : s = sIdx
                · subst s
                  unfold sessCorrAt at hc
                  simp only [Function.update_self] at hc
                  rw [hcorr_st'] at hc
                  simp only [Option.some.injEq] at hc
                  cases hc_old : sessCorrAt σ sIdx with
                  | some c_old =>
                    rw [hc_old, Option.getD_some] at hc
                    subst hc
                    exact hcorr sIdx c_old hc_old
                  | none =>
                    rw [hc_old, Option.getD_none, hlast sIdx] at hc
                    subst hc
                    refine ⟨hhon, le_rfl, htL_ge, fun r hr hrs hre hlt => ?_⟩
                    have hle := ((hhon_bk sIdx hhon).2 r hr hrs hre).2
                    omega
                · unfold sessCorrAt at hc
                  simp only [Function.update_of_ne hs] at hc
                  exact hcorr s c₀ hc
        · simp only [Bool.not_eq_true _ |>.mp hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
          refine PubMainRel.pure (Pt := Pt) fun σ₀ hσ₀ _ => ?_
          subst σ₀
          exact ⟨rfl, fun _ _ => rfl, rfl, rfl, hlast, hcorr⟩
      refine hOkStep.bind fun ⟨ok, h_m⟩ => ?_
      dsimp only [kSend]
      cases ok with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]
        exact PubMainRel.pure (Pt := Pt) fun _ _ => trivial
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        intro rc σ_m h_m_fn z hz
        rcases h_m_fn (by simp) with ⟨hca_m, hbk_ne_m, hcnt_m, htr_m, hlast_m, hcorr_m⟩
        simp only [runPubIdeal, simulateQ_bind, StateT.run_bind] at hz
        rw [MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨v, hv, hzv⟩
        have hTr :
            ((liftFSMulti
              (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
              (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
              (E := ℕ × LibsignalCiphertextWithSalt32) sIdx
              (_root_.CryptoGames.FSAEAD.transmitQuery hdr m)).run h_m) =
            (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl (hdr, m)))))⟩) >>=
              fun a => pure (a, h_m)) := by
          simp only [_root_.CryptoGames.FSAEAD.transmitQuery]
          exact liftFSMulti_run_query_eq sIdx (.inl (.inl (.inl (.inl (.inl (hdr, m)))))) h_m
        rw [hTr] at hv
        rcases pubQuery_transmit_main C ℓ encT idOf N sIdx hdr m h_m rc σ_m hv with
          ⟨hhv, st', hσ'_eq, hcorr_st', htr_cases⟩
        rcases v with ⟨⟨⟨e?, h_m'⟩, rc₁⟩, σ'⟩
        dsimp only at hhv hσ'_eq hcorr_st' htr_cases hzv
        subst h_m'; subst σ'
        cases e? with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure] at hzv
          rw [support_pure, Set.mem_singleton_iff] at hzv
          subst hzv
          exact trivial
        | some e =>
          rcases htr_cases with ⟨hnone, _⟩ | ⟨e₀, he₀, he_idx, hlast_st'⟩
          · exact nomatch hnone
          injection he₀ with he₀'; subst he₀'
          have he1_eq : e.1 = ((h₁.book sIdx).getD {}).fsCount + 1 :=
            he_idx.trans (congrArg (· + 1) (hlast_m sIdx))
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure] at hzv
          rw [support_pure, Set.mem_singleton_iff] at hzv
          subst hzv
          dsimp only
          let b_cur := (h_m.book sIdx).getD {}
          let cnt' := b_cur.fsCount + 1
          let b_new : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
            { b_cur with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b_cur.fsTrans }
          let h_final : ShiftedHState Pt RSt I :=
            { h_m with book := Function.update h_m.book sIdx (some b_new) }
          have hcnt'_eq : cnt' = ((h₁.book sIdx).getD {}).fsCount + 1 :=
            congrArg (· + 1) hcnt_m
          have hhon_final : honOpt t h_final = honOpt t h₁ := by
            simp [honOpt, h_final, hca_m]
          refine
            { abort_false := hes_ab
              win_false := hs₁_win
              st_id := fun Q => by
                by_cases hQP : Q = P
                · subst hQP; simp [_root_.CryptoGames.SM.GameState.record, Function.update_self, hst₁_id]
                · simp [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP, hs₁_id Q hQP]
              st_tcur := fun Q => by
                by_cases hQP : Q = P
                · subst hQP; simp [_root_.CryptoGames.SM.GameState.record, Function.update_self, hst₁_tcur]
                · simp [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP, hs₁_tcur Q hQP]
              tL_mem := hs₁_tL
              leaks_ok := hs₁_leaks
              trans_hdr := fun r hr => by
                simp only [_root_.CryptoGames.SM.GameState.record, List.mem_cons] at hr
                rcases hr with rfl | hr_old
                · exact ⟨hst₁_tcur, le_rfl⟩
                · exact hs₁_trans r hr_old
              cache_pre := fun hep => by
                dsimp only [h_final]
                rw [hca_m]
                exact hca_pre (by simpa [_root_.CryptoGames.SM.GameState.record] using hep)
              cache_t_some := fun Tc σc k optIdx hc =>
                hca_t Tc σc k optIdx (hca_m ▸ hc)
              cache_other_none := fun t0 hne Tc σc k optIdx hc =>
                hca_nt t0 hne Tc σc k optIdx (hca_m ▸ hc)
              vS_inr := fun Q sIdx' hv => by
                rw [hhon_final]
                by_cases hQP : Q = P
                · subst hQP
                  simp only [_root_.CryptoGames.SM.GameState.record, Function.update_self,
                    Option.some.injEq, Sum.inr.injEq] at hv
                  subst hv
                  exact ⟨hPS, hhon, Or.inl hep_t⟩
                · simp only [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP] at hv ⊢
                  exact hvS_other Q hQP sIdx' hv
              sender_at_t := fun _ => by
                refine ⟨sIdx, hhon_final.trans hhon, ?_, ?_⟩
                · subst hPS
                  simp [_root_.CryptoGames.SM.GameState.record, Function.update_self]
                · rw [← hPS]
                  dsimp only [h_final, b_new]
                  simp only [_root_.CryptoGames.SM.GameState.record, Function.update_self,
                    Option.getD_some]
                  rw [hcnt_m, hidx_eq]
              sender_cka_at_t := fun _ => by
                rcases (hsender_cka_t (hPS ▸ hep_t)).1 hPS with ⟨Tc, σc, k, sIdx₀, hca_t_eq, hcur_eq⟩
                refine ⟨Tc, σc, k, sIdx₀, ?_, ?_⟩
                · simpa [h_final, hca_m] using hca_t_eq
                · subst hPS
                  simpa [_root_.CryptoGames.SM.GameState.record, Function.update_self] using hcur_eq
              trans_t_hdr := fun r hr hs he => by
                simp only [_root_.CryptoGames.SM.GameState.record, List.mem_cons] at hr
                rcases hr with rfl | hr_old
                · rcases (hsender_cka_t (hPS ▸ hep_t)).1 hPS with ⟨Tc, σc, k, sIdx₀, hca_t_eq, hcur_eq⟩
                  refine ⟨Tc, σc, k, sIdx₀, by simpa [h_final, hca_m] using hca_t_eq, ?_⟩
                  dsimp only [hdr]
                  rw [hst₁_tcur, hep_t, hcur_eq]
                · rcases htrans_t_hdr r hr_old hs he with ⟨Tc, σc, k, sIdx₀, hca_t_eq, hr_hdr⟩
                  exact ⟨Tc, σc, k, sIdx₀, by simpa [h_final, hca_m] using hca_t_eq, hr_hdr⟩
              vR_target := fun Q rsv hv => by
                rw [hhon_final]
                by_cases hQP : Q = P
                · subst hQP
                  simp only [_root_.CryptoGames.SM.GameState.record, Function.update_self] at hv
                  exact hvR_t Q rsv (by simpa [Function.update_self] using hv)
                · simp only [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP] at hv
                  exact hvR_t Q rsv (by simpa [Function.update_of_ne hQP] using hv)
              vR_other := fun Q t0 rsv hnt0 hv => by
                by_cases hQP : Q = P
                · subst hQP
                  simp only [_root_.CryptoGames.SM.GameState.record, Function.update_self] at hv
                  exact hvR_nt Q t0 rsv hnt0 (by simpa [Function.update_self] using hv)
                · simp only [_root_.CryptoGames.SM.GameState.record, Function.update_of_ne hQP] at hv
                  exact hvR_nt Q t0 rsv hnt0 (by simpa [Function.update_of_ne hQP] using hv)
              non_hon_empty := fun s hh => by
                have hs : s ≠ sIdx := fun heq => hh (hhon_final.trans (heq ▸ hhon))
                simp only [h_final, Function.update_of_ne hs, hbk_ne_m s hs]
                exact hnh s (hhon_final ▸ hh)
              hon_book := fun s hh => by
                have hs : s = sIdx := (Option.some.inj (hhon.symm.trans (hhon_final.symm.trans hh))).symm
                subst s
                refine ⟨fun cnt hdr₀ e₀ hm => ?_, fun r hr hrs hre => ?_⟩
                · simp only [h_final, Function.update_self, Option.getD_some, b_new,
                    List.mem_cons, Prod.mk.injEq] at hm
                  rcases hm with ⟨hcnt0, hhdr0, he0⟩ | hm_old
                  · subst cnt hdr₀ e₀
                    refine ⟨hcnt'_eq.trans he1_eq.symm,
                      ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, (hdr, e)⟩,
                      List.mem_cons_self, ?_, rfl⟩
                    dsimp only
                    rw [hidx_eq, ← hcnt_m, hep_t, hPS]
                  · rw [htr_m] at hm_old
                    rcases (hhon_bk sIdx hhon).1 cnt hdr₀ e₀ hm_old with ⟨h1, r, hr, hpos, hct⟩
                    exact ⟨h1, r, List.mem_cons_of_mem _ hr, hpos, hct⟩
                · simp only [_root_.CryptoGames.SM.GameState.record, List.mem_cons] at hr
                  simp only [h_final, Function.update_self, Option.getD_some, b_new]
                  rcases hr with rfl | hr_old
                  · exact ⟨he1_eq.trans (congrArg (· + 1) hidx_eq.symm),
                      by dsimp only; rw [hcnt_m, hidx_eq]⟩
                  · rcases (hhon_bk sIdx hhon).2 r hr_old hrs hre with ⟨h1, h2⟩
                    exact ⟨h1, by rw [hcnt_m]; omega⟩
              router_last := fun s => by
                by_cases hs : s = sIdx
                · subst s
                  unfold sessLastIdx
                  simp only [Function.update_self]
                  rw [hlast_st', hlast_m]
                  simp only [Function.update_self, Option.getD_some, hcnt_m]
                · unfold sessLastIdx
                  simp only [Function.update_of_ne hs]
                  change sessLastIdx σ_m s = _
                  rw [hlast_m]
                  simp only [Function.update_of_ne hs, hbk_ne_m s hs]
              router_corr := fun s c₀ hc => by
                have hc_m : sessCorrAt σ_m s = some c₀ := by
                  by_cases hs : s = sIdx
                  · subst s
                    unfold sessCorrAt at hc
                    simp only [Function.update_self] at hc
                    rwa [hcorr_st'] at hc
                  · unfold sessCorrAt at hc
                    simp only [Function.update_of_ne hs] at hc
                    exact hc
                rcases hcorr_m s c₀ hc_m with ⟨hh_s, hle_s, ⟨lk, hlk_eq, hlk_ge⟩, hcp_s⟩
                have hs : s = sIdx := (Option.some.inj (hhon.symm.trans hh_s)).symm
                subst s
                refine ⟨hhon_final.trans hhon, ?_, ⟨lk, hlk_eq, hlk_ge⟩, fun r hr hrs hre hlt => ?_⟩
                · simp only [h_final, Function.update_self, Option.getD_some, b_new]
                  omega
                · have hsafe_f : s₁.safeCh (2 + Δcka) P = false := by
                    simp only [_root_.CryptoGames.SM.GameState.safeCh, hlk_eq, hep_t,
                      _root_.CryptoGames.SM.healedBy, decide_eq_false_iff_not]
                    omega
                  simp only [_root_.CryptoGames.SM.GameState.record, List.mem_cons] at hr
                  simp only [_root_.CryptoGames.SM.GameState.record, hsafe_f, Bool.false_eq_true, ↓reduceIte]
                  rcases hr with rfl | hr_old
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _ (hcp_s r hr_old hrs hre hlt) }

-- 1. `transmitE` preserves `ShiftedSafe`:
private theorem transmitE_hooksFSMulti_main_safe {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins] [SampleableType KR]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka qep l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (q_tr : Party × (LibsignalMsgPublicPart × Plain ℓ) × Option CCoins)
    (es : ShiftedEState Γ Pt RSt I ℓ) :
    PubMainRel C ℓ encT idOf N
      (fun σ => ShiftedSafe l t es σ)
      (fun p σ' => ShiftedSafe l t p.2 σ')
      ((transmitE (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
          ⟨authH, some (l - 1), t⟩ false false)
        (2 + Δcka) qep (⟨true, some (l - 1), t⟩ : Mode).policy q_tr).run es) := by
  rcases q_tr with ⟨P, m, r⟩
  intro rc σ hSafe z hz
  rcases hSafe with hab | hact
  · simp only [transmitE, hab, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_pure, pure_bind, runPubIdeal, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hab
  · simp only [transmitE, hact.abort_false, hact.win_false, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hsend1 : P.sendsIn (es.g.epoch P + 1) with
    | false =>
      have hsend_cur : P.sendsIn (es.g.epoch P) = true := by
        have hs := sendsIn_succ P (es.g.epoch P)
        rw [hsend1] at hs
        cases h0 : P.sendsIn (es.g.epoch P)
        · simp [h0] at hs
        · rfl
      simp only [_root_.CryptoGames.SM.GameState.epMgmt, hsend1, Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hqep : qep < es.g.epoch P
      · simp only [hqep, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact Or.inr hact
      · simp only [hqep, ↓reduceIte] at hz
        by_cases hdoom : _root_.CryptoGames.SM.Engine.Policy.leakDoom ⟨true, some (l - 1), t⟩ es.g es.g = true
        · simp only [Mode.policy, hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind, runPubIdeal, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact Or.inl rfl
        · simp only [Bool.not_eq_true] at hdoom
          simp only [Mode.policy, hdoom, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hz
          have hvSend_eq :
              (vSend (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                  ⟨authH, some (l - 1), t⟩ false false) es.g P (es.g.st P) m none r) =
              (match (es.g.st P).vS with
                | none => pure (some (es.g.st P, (((es.g.st P).tcur, (es.g.st P).curCkaMsg), default)))
                | some v => do
                  match ← (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                      ⟨authH, some (l - 1), t⟩ false false).fsSend
                      es.g P (es.g.st P).tcur v ((es.g.st P).tcur, (es.g.st P).curCkaMsg) m none with
                  | none => pure none
                  | some (v', e) =>
                    pure (some ({ (es.g.st P) with vS := some v' },
                      (((es.g.st P).tcur, (es.g.st P).curCkaMsg), e)))) := by
            dsimp only [vSend]
            have hguard : (es.g.st P).id.sendsIn ((es.g.st P).tcur + 1) = false := by
              rw [hact.st_id P, hact.st_tcur P]; exact hsend1
            simp only [hguard, Bool.false_eq_true, ↓reduceIte, pure_bind]
            cases (es.g.st P).vS with
            | none => rfl
            | some v =>
              exact congrArg (Bind.bind _) (funext fun x => by rcases x with _ | ⟨v', e⟩ <;> rfl)
          have hStep2 := fsSend_and_record_main_safe C ℓ encT idOf N cka prng Δcka l t authH hAdm
            es es.g P (es.g.st P) m es.h σ
            hact.abort_false hact.win_false
            (fun Q _ => hact.st_id Q) (fun Q _ => hact.st_tcur Q)
            (hact.st_id P) (hact.st_tcur P) hsend_cur
            hact.tL_mem hact.leaks_ok hact.trans_hdr
            hact.cache_pre hact.cache_t_some hact.cache_other_none
            (fun Q _ sIdx hv => hact.vS_inr Q sIdx hv)
            (fun sIdx hv => by
              rcases hact.vS_inr P sIdx hv with ⟨hPS, hhon, hep_or⟩
              have hep_t : es.g.epoch P = t := by
                rcases hep_or with h1 | h2
                · exact h1
                · rw [h2] at hsend_cur
                  have h1 := sendsIn_succ P t
                  rw [hPS, sendsIn_senderOf] at h1
                  rw [hPS, h1] at hsend_cur
                  exact Bool.noConfusion hsend_cur
              rcases hact.sender_at_t (hPS ▸ hep_t) with ⟨sIdx', _, hv', hidx'⟩
              rw [← hPS, hv] at hv'
              injection hv' with hEq; injection hEq with hsEq
              subst hsEq
              exact ⟨hPS, hhon, hep_t, hPS ▸ hidx'⟩)
            (fun hep_t =>
              ⟨fun hPS => by
                rcases hact.sender_at_t hep_t with ⟨sIdx, _, hv, _⟩
                exact ⟨sIdx, hPS ▸ hv⟩,
               fun _ => hact.sender_at_t hep_t⟩)
            (fun hep_t =>
              ⟨fun hPS => by
                subst hPS
                exact hact.sender_cka_at_t hep_t,
               fun _ => hact.sender_cka_at_t hep_t⟩)
            hact.trans_t_hdr
            (fun Q rsv hv => by
              by_cases hQP : Q = P
              · subst hQP; simpa [Function.update_self] using hact.vR_target Q rsv (by simpa [Function.update_self] using hv)
              · exact hact.vR_target Q rsv (by simpa [Function.update_of_ne hQP] using hv))
            (fun Q t0 rsv hnt0 hv => by
              by_cases hQP : Q = P
              · subst hQP; exact hact.vR_other Q t0 rsv hnt0 (by simpa [Function.update_self] using hv)
              · exact hact.vR_other Q t0 rsv hnt0 (by simpa [Function.update_of_ne hQP] using hv))
            hact.non_hon_empty hact.hon_book hact.router_last hact.router_corr
          have hLift := PubMainRel.liftH C ℓ encT idOf N
            (vSend (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
              ⟨authH, some (l - 1), t⟩ false false) es.g P (es.g.st P) m none r)
            es (by rw [hvSend_eq]; exact hStep2)
          refine (hLift.bind (Post := fun p σ' => ShiftedSafe l t p.2 σ') fun ⟨out, es₁⟩ => ?_) rc σ rfl z hz
          cases out with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PubMainRel.pure fun _ _ => Or.inl rfl
          | some pair_out =>
            rcases pair_out with ⟨st', c⟩
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            refine PubMainRel.pure fun σ' ⟨hes₁, hInv⟩ => ?_
            rw [hes₁]
            exact Or.inr hInv
    | true =>
      simp only [_root_.CryptoGames.SM.GameState.epMgmt, hsend1, ↓reduceIte] at hz
      by_cases hqep : qep < es.g.epoch P + 1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact Or.inr hact
      · simp only [hqep, ↓reduceIte] at hz
        set s_base :=
          if r.isSome && !(es.g.safeCh (2 + Δcka) P) then es.g.leak (es.g.epoch P + 1) else es.g
        set s₁ :=
          { s_base with
            epoch := Function.update s_base.epoch P (s_base.epoch P + 1)
            idx := Function.update s_base.idx P 0 }
        have hs_base_eqs :
            s_base.win = false ∧ s_base.st = es.g.st ∧ s_base.epoch = es.g.epoch ∧
            s_base.idx = es.g.idx ∧ s_base.trans = es.g.trans ∧ s_base.comp = es.g.comp ∧
            (∀ lk, s_base.tL = some lk → lk ∈ s_base.leaks) ∧
            (∀ lk₀, es.g.tL = some lk₀ → ∃ lk₁, s_base.tL = some lk₁ ∧ lk₀ ≤ lk₁) := by
          dsimp only [s_base]
          split_ifs
          · refine ⟨hact.win_false, rfl, rfl, rfl, rfl, rfl,
              fun lk hlk => ?_,
              fun lk₀ hlk₀ => ⟨_, rfl, le_maxOpt_of_some hlk₀ _⟩⟩
            simp only [_root_.CryptoGames.SM.GameState.leak, Option.some.injEq] at hlk
            subst hlk
            exact List.mem_cons_self
          · exact ⟨hact.win_false, rfl, rfl, rfl, rfl, rfl, hact.tL_mem,
              fun lk₀ hlk₀ => ⟨lk₀, hlk₀, le_rfl⟩⟩
        rcases hs_base_eqs with ⟨hsb_win, hsb_st, hsb_ep, hsb_idx, hsb_tr, hsb_cp, hsb_tL, hsb_tL_mono⟩
        simp only [Mode.policy] at hz
        by_cases hdoom : (_root_.CryptoGames.SM.Engine.Policy.mk true (some (l - 1)) t).leakDoom es.g s₁ = true
        · simp only [hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind, runPubIdeal, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact Or.inl rfl
        · simp only [Bool.not_eq_true] at hdoom
          simp only [hdoom, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hz
          have hs₁_leaks : ∀ lk ∈ s₁.leaks, lk ≤ l - 1 ∨ t ≤ lk :=
            leaks_ok_of_leakDoom_false hdoom
          have hStep1 :
              PubMainRel C ℓ encT idOf N
                (fun σ₀ => σ₀ = σ)
                (fun p₁ σ₁ =>
                  σ₁ = σ ∧ p₁.2.book = es.h.book ∧
                  ∀ γ' T' σr' ss, p₁.1 = some (γ', T', σr', ss) →
                    p₁.2.cache = Function.update es.h.cache (es.g.epoch P + 1)
                      (some (T', σr',
                        match p₁.2.cache (es.g.epoch P + 1) with
                        | some (_, _, k₀, _) => k₀
                        | none => default,
                        match ss with | .inl _ => none | .inr sIdx => some sIdx)) ∧
                    (∀ t0, t0 ≠ es.g.epoch P + 1 → p₁.2.cache t0 = es.h.cache t0) ∧
                    (es.g.epoch P + 1 = t →
                      ∃ k₀ sIdx, ss = .inr sIdx ∧
                        p₁.2.cache t = some (T', σr', k₀, some sIdx)) ∧
                    (es.g.epoch P + 1 ≠ t →
                      (∃ ss₀, ss = .inl ss₀) ∧
                      ∃ k₀, p₁.2.cache (es.g.epoch P + 1) = some (T', σr', k₀, none)))
                (((hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                    ⟨authH, some (l - 1), t⟩ false false).startSend
                  s₁ P (es.g.epoch P + 1) (es.g.st P).γ (es.g.st P).root r).run es.h) := by
            have hstart_rw :
                ((hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                    ⟨authH, some (l - 1), t⟩ false false).startSend
                  s₁ P (es.g.epoch P + 1) (es.g.st P).γ (es.g.st P).root r) =
                ((match r with
                  | some c => pure c
                  | none => StateT.lift (_root_.CryptoGames.SM.Construction.sampleT CCoins)) >>= fun coins => do
                  let (σr', k₀, sid) ← rootFSMulti prng ⟨authH, some (l - 1), t⟩
                    (es.g.epoch P + 1) (cka.send (es.g.st P).γ coins).2.2 (es.g.st P).root
                  let optIdx ← regSessOptMulti sid
                  modify fun s =>
                    { s with
                      cache := Function.update s.cache (es.g.epoch P + 1)
                        (some ((cka.send (es.g.st P).γ coins).2.1, σr', k₀, optIdx)) }
                  pure (some ((cka.send (es.g.st P).γ coins).1,
                    (cka.send (es.g.st P).γ coins).2.1, σr',
                    match optIdx with
                    | none => .inl ((ShiftedFS Pt C ℓ encT idOf).initSender k₀)
                    | some sIdx => .inr sIdx))) := by
              cases r <;> rfl
            rw [hstart_rw, StateT.run_bind]
            have hCoins :
                PubMainRel C ℓ encT idOf N
                  (fun σ₀ => σ₀ = σ)
                  (fun (p₀ : CCoins × ShiftedHState Pt RSt I) σ₀ => p₀.2 = es.h ∧ σ₀ = σ)
                  ((match r with
                    | some c => (pure c : StateT (ShiftedHState Pt RSt I) _ CCoins)
                    | none => StateT.lift (_root_.CryptoGames.SM.Construction.sampleT CCoins)).run es.h) := by
              cases r with
              | some c => exact PubMainRel.pure fun _ hσ₀ => ⟨rfl, hσ₀⟩
              | none => exact PubMainRel.stateT_lift_sampleT C ℓ encT idOf N es.h
            refine hCoins.bind fun ⟨coins, h_c⟩ => ?_
            intro rc₀ σ₀ ⟨hh_c, hσ₀⟩ z₀ hz₀
            subst hh_c; subst σ₀
            simp only [StateT.run_bind] at hz₀
            refine ((rootFSMulti_main_preserves C ℓ encT idOf N prng
              ⟨authH, some (l - 1), t⟩ (es.g.epoch P + 1) (cka.send (es.g.st P).γ coins).2.2
              (es.g.st P).root es.h (Pre := fun σ₀ => σ₀ = σ)).bind
              (Post := fun p₁ σ₁ =>
                σ₁ = σ ∧ p₁.2.book = es.h.book ∧
                ∀ γ' T' σr' ss, p₁.1 = some (γ', T', σr', ss) →
                  p₁.2.cache = Function.update es.h.cache (es.g.epoch P + 1)
                    (some (T', σr',
                      match p₁.2.cache (es.g.epoch P + 1) with
                      | some (_, _, k₀, _) => k₀
                      | none => default,
                      match ss with | .inl _ => none | .inr sIdx => some sIdx)) ∧
                  (∀ t0, t0 ≠ es.g.epoch P + 1 → p₁.2.cache t0 = es.h.cache t0) ∧
                  (es.g.epoch P + 1 = t →
                    ∃ k₀ sIdx, ss = .inr sIdx ∧
                      p₁.2.cache t = some (T', σr', k₀, some sIdx)) ∧
                  (es.g.epoch P + 1 ≠ t →
                    (∃ ss₀, ss = .inl ss₀) ∧
                    ∃ k₀, p₁.2.cache (es.g.epoch P + 1) = some (T', σr', k₀, none)))
              fun ⟨⟨σr', k₀, sid⟩, h_r⟩ => ?_) rc₀ σ rfl z₀ hz₀
            cases sid with
            | none =>
              simp only [regSessOptMulti, pure_bind, StateT.run_modify, StateT.run_pure]
              refine PubMainRel.pure fun _ ⟨hca_r, hbk_r, hsid_t, _, hσ₀⟩ => ?_
              refine ⟨hσ₀, hbk_r, fun γ' T' σr'' ss hEq => ?_⟩
              injection hEq with hEq'; rcases Prod.mk.inj hEq' with ⟨rfl, hEq2⟩
              rcases Prod.mk.inj hEq2 with ⟨rfl, hEq3⟩
              rcases Prod.mk.inj hEq3 with ⟨rfl, rfl⟩
              refine ⟨?_, fun t0 hne => by simp [Function.update_of_ne hne, hca_r],
                fun ht => by have := hsid_t ht; simp at this,
                fun _ => ⟨⟨_, rfl⟩, k₀, by simp [Function.update_self]⟩⟩
              funext t0
              by_cases ht0 : t0 = es.g.epoch P + 1
              · subst ht0; simp [Function.update_self]
              · simp [Function.update_of_ne ht0, hca_r]
            | some Ik =>
              simp only [regSessOptMulti, map_eq_bind_pure_comp, bind_assoc, Function.comp,
                StateT.run_bind]
              refine (regSessMulti_main_preserves C ℓ encT idOf N Ik h_r).bind fun ⟨sIdx, h_s⟩ => ?_
              simp only [StateT.run_modify, StateT.run_pure, pure_bind]
              refine PubMainRel.pure fun _ ⟨hca_s, hbk_s, hca_r, hbk_r, _, hsid_nt, hσ₀⟩ => ?_
              refine ⟨hσ₀, hbk_s.trans hbk_r, fun γ' T' σr'' ss hEq => ?_⟩
              injection hEq with hEq'; rcases Prod.mk.inj hEq' with ⟨rfl, hEq2⟩
              rcases Prod.mk.inj hEq2 with ⟨rfl, hEq3⟩
              rcases Prod.mk.inj hEq3 with ⟨rfl, rfl⟩
              refine ⟨?_, fun t0 hne => by simp [Function.update_of_ne hne, hca_s, hca_r],
                fun ht => ⟨k₀, sIdx, rfl, by subst ht; simp [Function.update_self]⟩,
                fun hnt => absurd (hsid_nt hnt) (by simp)⟩
              funext t0
              by_cases ht0 : t0 = es.g.epoch P + 1
              · subst ht0; simp [Function.update_self]
              · simp [Function.update_of_ne ht0, hca_s, hca_r]
          have hvSend_unfold :
              (vSend (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                  ⟨authH, some (l - 1), t⟩ false false) s₁ P (s₁.st P) m none r) =
              ((hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                    ⟨authH, some (l - 1), t⟩ false false).startSend
                  s₁ P (es.g.epoch P + 1) (es.g.st P).γ (es.g.st P).root r >>= fun startOpt =>
                match startOpt with
                | none => pure none
                | some (γ', T', σr', ss) =>
                  let st₁ : VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
                      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) :=
                    { (s₁.st P) with
                      tcur := es.g.epoch P + 1, γ := γ', curCkaMsg := some T',
                      root := σr', vS := some ss }
                  let hdr : Header Pt := (st₁.tcur, st₁.curCkaMsg)
                  match st₁.vS with
                  | none => pure (some (st₁, (hdr, default)))
                  | some v => do
                    match ← (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                        ⟨authH, some (l - 1), t⟩ false false).fsSend s₁ P st₁.tcur v hdr m none with
                    | none => pure none
                    | some (v', e) => pure (some ({ st₁ with vS := some v' }, (hdr, e)))) := by
            dsimp only [vSend]
            have hstP : s₁.st P = es.g.st P := hsb_st ▸ rfl
            have htcurP : (s₁.st P).tcur = es.g.epoch P := by rw [hstP, hact.st_tcur P]
            have hguard : (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1) = true := by
              rw [hstP, hact.st_id P, hact.st_tcur P]; exact hsend1
            simp only [hguard, ↓reduceIte]
            have hstart_eq :
                (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                  ⟨authH, some (l - 1), t⟩ false false).startSend
                  s₁ P ((s₁.st P).tcur + 1) (s₁.st P).γ (s₁.st P).root r =
                (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                  ⟨authH, some (l - 1), t⟩ false false).startSend
                  s₁ P (es.g.epoch P + 1) (es.g.st P).γ (es.g.st P).root r := by
              rw [hstP, hact.st_tcur P]
            rw [hstart_eq]
            refine congrArg _ (funext fun x => ?_)
            rcases x with _ | ⟨γ', T', σr', ss⟩
            · simp only [pure_bind]
            · simp only [pure_bind, htcurP]
              exact congrArg (Bind.bind _) (funext fun x => by rcases x with _ | ⟨v', e⟩ <;> rfl)
          have hFullVSend :
              PubMainRel C ℓ encT idOf N
                (fun σ₀ => σ₀ = σ)
                (fun p σ' =>
                  match p.1 with
                  | none => True
                  | some (st', c) =>
                    ShiftedActiveInv l t
                      { es with
                        g := s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ false
                        h := p.2 } σ')
                ((vSend (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                    ⟨authH, some (l - 1), t⟩ false false) s₁ P (s₁.st P) m none r).run es.h) := by
            rw [hvSend_unfold, StateT.run_bind]
            refine hStep1.bind fun ⟨startOpt, h₁⟩ => ?_
            cases startOpt with
            | none =>
              simp only [StateT.run_pure]
              exact PubMainRel.pure fun _ _ => trivial
            | some quad =>
              rcases quad with ⟨γ', T', σr', ss⟩
              intro rc₁ σ₁ ⟨hσ₁, hbk₁, hstart_fn⟩ z₁ hz₁
              subst σ₁
              dsimp only at hbk₁ hstart_fn
              rcases hstart_fn γ' T' σr' ss rfl with ⟨_, hca_ne₁, hstart_t, hstart_nt⟩
              let st₁ : VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
                  (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) :=
                { (s₁.st P) with
                  tcur := es.g.epoch P + 1, γ := γ', curCkaMsg := some T',
                  root := σr', vS := some ss }
              have hs₁_epP : s₁.epoch P = es.g.epoch P + 1 := by
                simp [s₁, hsb_ep, Function.update_self]
              have hs₁_epQ : ∀ Q, Q ≠ P → s₁.epoch Q = es.g.epoch Q := fun Q hQP => by
                simp [s₁, hsb_ep, Function.update_of_ne hQP]
              have hs₁_idxP : s₁.idx P = 0 := by
                simp [s₁, hsb_idx, Function.update_self]
              have hs₁_idxQ : ∀ Q, Q ≠ P → s₁.idx Q = es.g.idx Q := fun Q hQP => by
                simp [s₁, hsb_idx, Function.update_of_ne hQP]
              have hhon_before_t : es.g.epoch P + 1 = t → honOpt t es.h = none := by
                intro hep1_t
                have hPS : P = Party.senderOf t := eq_senderOf_of_sendsIn (hep1_t ▸ hsend1)
                have hlt : es.g.epoch (Party.senderOf t) < t := by rw [← hPS]; omega
                simp [honOpt, hact.cache_pre hlt]
              exact fsSend_and_record_main_safe C ℓ encT idOf N cka prng Δcka l t authH hAdm
                es s₁ P st₁ m h₁ σ
                hact.abort_false
                (by simp [s₁, hsb_win])
                (fun Q _ => by simp [s₁, hsb_st, hact.st_id Q])
                (fun Q hQP => by rw [hs₁_epQ Q hQP, ← hact.st_tcur Q]; simp [s₁, hsb_st])
                (by simp [st₁, s₁, hsb_st, hact.st_id P])
                hs₁_epP.symm
                (hs₁_epP ▸ hsend1)
                (fun lk hlk => hsb_tL lk hlk)
                hs₁_leaks
                (fun r₀ hr₀ => by
                  simp only [s₁, hsb_tr] at hr₀
                  rcases hact.trans_hdr r₀ hr₀ with ⟨h1, h2⟩
                  refine ⟨h1, le_trans h2 ?_⟩
                  by_cases hSP : r₀.pos.sender = P
                  · subst hSP; rw [hs₁_epP]; omega
                  · rw [hs₁_epQ _ hSP])
                (fun hep_lt => by
                  have hne_t : t ≠ es.g.epoch P + 1 := by
                    intro heq
                    have hPS : P = Party.senderOf t := eq_senderOf_of_sendsIn (heq ▸ hsend1)
                    rw [← hPS, hs₁_epP] at hep_lt
                    omega
                  rw [hca_ne₁ t hne_t]
                  apply hact.cache_pre
                  by_cases hSP : Party.senderOf t = P
                  · rw [hSP, hs₁_epP] at hep_lt; rw [hSP]; omega
                  · rwa [hs₁_epQ _ hSP] at hep_lt)
                (fun Tc σc k optIdx hc => by
                  by_cases ht_eq : es.g.epoch P + 1 = t
                  · rcases hstart_t ht_eq with ⟨k₀, sIdx, _, hca_t⟩
                    rw [hca_t] at hc
                    injection hc with hc'; rcases Prod.mk.inj hc' with ⟨_, hc2⟩
                    rcases Prod.mk.inj hc2 with ⟨_, hc3⟩
                    rcases Prod.mk.inj hc3 with ⟨_, rfl⟩
                    exact ⟨sIdx, rfl⟩
                  · rw [hca_ne₁ t (Ne.symm ht_eq)] at hc
                    exact hact.cache_t_some Tc σc k optIdx hc)
                (fun t0 hnt0 Tc σc k optIdx hc => by
                  by_cases ht0_eq : t0 = es.g.epoch P + 1
                  · subst ht0_eq
                    rcases (hstart_nt hnt0).2 with ⟨k₀, hca_nt⟩
                    rw [hca_nt] at hc
                    injection hc with hc'; rcases Prod.mk.inj hc' with ⟨_, hc2⟩
                    rcases Prod.mk.inj hc2 with ⟨_, hc3⟩
                    exact (Prod.mk.inj hc3).2.symm
                  · rw [hca_ne₁ t0 ht0_eq] at hc
                    exact hact.cache_other_none t0 hnt0 Tc σc k optIdx hc)
                (fun Q hQP sIdx hv => by
                  simp only [s₁, hsb_st] at hv
                  rcases hact.vS_inr Q sIdx hv with ⟨hQS, hhon_es, hep_or⟩
                  have hne_t : es.g.epoch P + 1 ≠ t := by
                    intro heq
                    exact hQP (hQS.trans (eq_senderOf_of_sendsIn (heq ▸ hsend1)).symm)
                  have hhon_eq : honOpt t h₁ = honOpt t es.h := by
                    simp [honOpt, hca_ne₁ t (Ne.symm hne_t)]
                  exact ⟨hQS, hhon_eq.trans hhon_es, by simpa [hs₁_epQ Q hQP] using hep_or⟩)
                (fun sIdx hv => by
                  simp only [st₁, Option.some.injEq] at hv
                  subst hv
                  have hep1_t : es.g.epoch P + 1 = t := by
                    by_contra hnt
                    rcases (hstart_nt hnt).1 with ⟨ss₀, hss⟩
                    exact nomatch hss
                  have hPS : P = Party.senderOf t := eq_senderOf_of_sendsIn (hep1_t ▸ hsend1)
                  rcases hstart_t hep1_t with ⟨k₀, sIdx', hss_eq, hca_t⟩
                  injection hss_eq with hs_eq; subst hs_eq
                  have hhon₁ : honOpt t h₁ = some sIdx := by simp [honOpt, hca_t]
                  have hcnt0 : ((h₁.book sIdx).getD {}).fsCount = 0 := by
                    rw [hbk₁]
                    exact (hact.non_hon_empty sIdx (by simp [hhon_before_t hep1_t])).1
                  exact ⟨hPS, hhon₁, hs₁_epP.trans hep1_t, hs₁_idxP.trans hcnt0.symm⟩)
                (fun hep_t => by
                  refine ⟨fun hPS => ?_, fun hPS => ?_⟩
                  · have hep1_t : es.g.epoch P + 1 = t := by
                      rw [← hs₁_epP, hPS, hep_t]
                    rcases hstart_t hep1_t with ⟨_, sIdx, hss_eq, _⟩
                    exact ⟨sIdx, by simp [st₁, hss_eq]⟩
                  · have hep_es : es.g.epoch (Party.senderOf t) = t := by
                      rwa [hs₁_epQ _ (Ne.symm hPS)] at hep_t
                    have hne_t : es.g.epoch P + 1 ≠ t := fun heq =>
                      hPS (eq_senderOf_of_sendsIn (heq ▸ hsend1))
                    rcases hact.sender_at_t hep_es with ⟨sIdx, hhon_es, hv_es, hidx_es⟩
                    have hhon_eq : honOpt t h₁ = honOpt t es.h := by
                      simp [honOpt, hca_ne₁ t (Ne.symm hne_t)]
                    refine ⟨sIdx, hhon_eq.trans hhon_es, ?_, ?_⟩
                    · simpa [s₁, hsb_st] using hv_es
                    · rw [hs₁_idxQ _ (Ne.symm hPS), hbk₁]; exact hidx_es)
                (fun hep_t => by
                  refine ⟨fun hPS => ?_, fun hPS => ?_⟩
                  · have hep1_t : es.g.epoch P + 1 = t := by
                      rw [← hs₁_epP, hPS, hep_t]
                    rcases hstart_t hep1_t with ⟨k₀, sIdx, _, hca_t⟩
                    exact ⟨T', σr', k₀, sIdx, hca_t, rfl⟩
                  · have hep_es : es.g.epoch (Party.senderOf t) = t := by
                      rwa [hs₁_epQ _ (Ne.symm hPS)] at hep_t
                    have hne_t : t ≠ es.g.epoch P + 1 := fun heq =>
                      hPS (eq_senderOf_of_sendsIn (heq.symm ▸ hsend1))
                    rcases hact.sender_cka_at_t hep_es with ⟨Tc, σc, k₀, sIdx, hca_es, hcur_es⟩
                    exact ⟨Tc, σc, k₀, sIdx, (hca_ne₁ t hne_t).trans hca_es,
                      by simpa [s₁, hsb_st] using hcur_es⟩)
                (fun r₀ hr₀ hrs hre => by
                  simp only [s₁, hsb_tr] at hr₀
                  have hle := (hact.trans_hdr r₀ hr₀).2
                  rw [hrs, hre] at hle
                  have hne_t : t ≠ es.g.epoch P + 1 := by
                    intro heq
                    have hPS : P = Party.senderOf t := eq_senderOf_of_sendsIn (heq.symm ▸ hsend1)
                    rw [← hPS] at hle
                    omega
                  rcases hact.trans_t_hdr r₀ hr₀ hrs hre with ⟨Tc, σc, k₀, sIdx, hca_es, hr_hdr⟩
                  exact ⟨Tc, σc, k₀, sIdx, (hca_ne₁ t hne_t).trans hca_es, hr_hdr⟩)
                (fun Q rsv hv => by
                  have hv_es : (es.g.st Q).vR t = some rsv := by
                    by_cases hQP : Q = P
                    · subst hQP; simpa [Function.update_self, st₁, s₁, hsb_st] using hv
                    · simpa [Function.update_of_ne hQP, s₁, hsb_st] using hv
                  rcases hact.vR_target Q rsv hv_es with ⟨sIdx, rfl, hhon_es⟩
                  have hne_t : es.g.epoch P + 1 ≠ t := by
                    intro heq
                    rw [hhon_before_t heq] at hhon_es
                    exact nomatch hhon_es
                  have hhon_eq : honOpt t h₁ = honOpt t es.h := by
                    simp [honOpt, hca_ne₁ t (Ne.symm hne_t)]
                  exact ⟨sIdx, rfl, hhon_eq.trans hhon_es⟩)
                (fun Q t0 rsv hnt0 hv => by
                  have hv_es : (es.g.st Q).vR t0 = some rsv := by
                    by_cases hQP : Q = P
                    · subst hQP; simpa [Function.update_self, st₁, s₁, hsb_st] using hv
                    · simpa [Function.update_of_ne hQP, s₁, hsb_st] using hv
                  exact hact.vR_other Q t0 rsv hnt0 hv_es)
                (fun sIdx hh₁ => by
                  rw [hbk₁]
                  by_cases ht_eq : es.g.epoch P + 1 = t
                  · exact hact.non_hon_empty sIdx (by simp [hhon_before_t ht_eq])
                  · have hhon_eq : honOpt t h₁ = honOpt t es.h := by
                      simp [honOpt, hca_ne₁ t (Ne.symm ht_eq)]
                    exact hact.non_hon_empty sIdx (hhon_eq ▸ hh₁))
                (fun sIdx hh₁ => by
                  by_cases ht_eq : es.g.epoch P + 1 = t
                  · have hPS : P = Party.senderOf t := eq_senderOf_of_sendsIn (ht_eq ▸ hsend1)
                    have hempty := hact.non_hon_empty sIdx (by simp [hhon_before_t ht_eq])
                    refine ⟨fun cnt hdr₀ e₀ hm => ?_, fun r₀ hr₀ hrs hre => ?_⟩
                    · rw [hbk₁, hempty.2] at hm; exact nomatch hm
                    · simp only [s₁, hsb_tr] at hr₀
                      have hle := (hact.trans_hdr r₀ hr₀).2
                      rw [hrs, ← hPS, hre] at hle
                      omega
                  · have hhon_eq : honOpt t h₁ = honOpt t es.h := by
                      simp [honOpt, hca_ne₁ t (Ne.symm ht_eq)]
                    have hh_es := hhon_eq ▸ hh₁
                    rw [hbk₁]
                    simpa [s₁, hsb_tr] using hact.hon_book sIdx hh_es)
                (fun sIdx => by rw [hbk₁]; exact hact.router_last sIdx)
                (fun sIdx c₀ hc => by
                  rcases hact.router_corr sIdx c₀ hc with ⟨hh_es, hle_es, ⟨lk₀, hlk₀, htle₀⟩, hcp_es⟩
                  have hne_t : es.g.epoch P + 1 ≠ t := by
                    intro heq; rw [hhon_before_t heq] at hh_es; exact nomatch hh_es
                  have hhon_eq : honOpt t h₁ = honOpt t es.h := by
                    simp [honOpt, hca_ne₁ t (Ne.symm hne_t)]
                  rcases hsb_tL_mono lk₀ hlk₀ with ⟨lk₁, hlk₁, hle₀₁⟩
                  refine ⟨hhon_eq.trans hh_es, ?_, ⟨lk₁, hlk₁, le_trans htle₀ hle₀₁⟩, ?_⟩
                  · rw [hbk₁]; exact hle_es
                  · simpa [s₁, hsb_tr, hsb_cp] using hcp_es)
                rc₁ σ rfl z₁ hz₁
          have hLift := PubMainRel.liftH C ℓ encT idOf N
            (vSend (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
              ⟨authH, some (l - 1), t⟩ false false) s₁ P (s₁.st P) m none r)
            es hFullVSend
          refine (hLift.bind (Post := fun p σ' => ShiftedSafe l t p.2 σ') fun ⟨out, es₁⟩ => ?_) rc σ rfl z hz
          cases out with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PubMainRel.pure fun _ _ => Or.inl rfl
          | some pair_out =>
            rcases pair_out with ⟨st', c⟩
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            refine PubMainRel.pure fun σ' ⟨hes₁, hInv⟩ => ?_
            rw [hes₁]
            exact Or.inr hInv

-- 2. `challE` preserves `ShiftedSafe` (`(Config.auth t).challAllowedIn _ = false`):
private theorem challE_hooksFSMulti_main_safe {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins] [SampleableType KR]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka qep l t : ℕ) (authH : Bool)
    (q_ch : Party × (LibsignalMsgPublicPart × Plain ℓ) × (LibsignalMsgPublicPart × Plain ℓ) × Option CCoins)
    (es : ShiftedEState Γ Pt RSt I ℓ) :
    PubMainRel C ℓ encT idOf N
      (fun σ => ShiftedSafe l t es σ)
      (fun p σ' => ShiftedSafe l t p.2 σ')
      ((challE (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
          ⟨authH, some (l - 1), t⟩ false false)
        (2 + Δcka) qep (⟨true, some (l - 1), t⟩ : Mode).cfg
        (⟨true, some (l - 1), t⟩ : Mode).policy q_ch).run es) := by
  rcases q_ch with ⟨P, m₀, m₁, r⟩
  unfold challE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hab : (es.abort || es.g.win) = true
  · simp only [hab, ↓reduceIte, StateT.run_pure]
    exact PubMainRel.pure fun _ hSafe => hSafe
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none =>
      simp only [StateT.run_pure]
      exact PubMainRel.pure fun _ hSafe => hSafe
    | some s₁ =>
      simp only [Mode.cfg, _root_.CryptoGames.SM.Config.auth,
        Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure]
      exact PubMainRel.pure fun _ hSafe => hSafe

private theorem liftH_pure_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γv T Sv SSv RSv M E HS α : Type} (a : α)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (liftH (tspec := tspec) (HS := HS) (pure a)).run es = pure (a, es) := by
  simp [StateT.run_pure]

-- 3. `deliverE` preserves `ShiftedSafe`:
private theorem deliverE_hooksFSMulti_main_safe {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (q_dl : Party × (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))
    (es : ShiftedEState Γ Pt RSt I ℓ) :
    PubMainRel C ℓ encT idOf N
      (fun σ => ShiftedSafe l t es σ)
      (fun p σ' => ShiftedSafe l t p.2 σ')
      ((deliverE (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
          ⟨authH, some (l - 1), t⟩ false false)
        maxForwardJumps (⟨true, some (l - 1), t⟩ : Mode).cfg q_dl).run es) := by
  rcases q_dl with ⟨P, c⟩
  intro rc σ hSafe z hz
  rcases hSafe with hab | hact
  · simp only [deliverE, hab, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_pure, pure_bind, runPubIdeal, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hab
  · simp only [deliverE, hact.abort_false, hact.win_false, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hit : es.g.inTransit P.other c with
    | none =>
      simp only [hit, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inr hact
    | some r =>
      have hr_props : r ∈ es.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold _root_.CryptoGames.SM.GameState.inTransit at hit
        have hmem := List.mem_of_find?_eq_some hit
        have hpred := List.find?_some hit
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
        exact ⟨hmem, hpred.1, hpred.2⟩
      rcases hr_props with ⟨hr_mem, hr_send, hr_ct⟩
      have hc_ep : c.1.1 = r.pos.epoch := by
        rw [← hr_ct]
        exact (hact.trans_hdr r hr_mem).1
      simp only [hit, Mode.cfg, ↓reduceIte, _root_.CryptoGames.SM.Config.auth,
        Bool.false_and, StateT.run_bind] at hz
      have hLift := PubMainRel.liftH C ℓ encT idOf N _ es
        (vRecv_hooksFSMulti_main_step C ℓ encT idOf N cka prng Δcka l t authH hAdm
          es σ hact P c (some r)
          (fun _ ht _ => Or.inl ⟨r, hr_mem, hr_send, by rw [hr_ct], hc_ep.symm.trans ht⟩)
          (fun h => nomatch h))
      refine (hLift.bind (Post := fun p σ' => ShiftedSafe l t p.2 σ') fun ⟨ro, es₁⟩ => ?_) rc σ rfl z hz
      cases ro with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact PubMainRel.pure fun _ _ => Or.inl rfl
      | some r_in =>
        cases r_in with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
          refine PubMainRel.pure fun σ' ⟨hes₁, hv_none, _⟩ => ?_
          rw [hes₁]
          exact Or.inr (hv_none trivial)
        | some quad =>
          rcases quad with ⟨st', t', i', m'⟩
          simp only [commitE, hooksFSMulti, StateT.run_bind, liftH_pure_run,
            Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            StateT.run_modify, pure_bind]
          refine PubMainRel.pure fun σ' ⟨hes₁, _, hv_some⟩ => ?_
          rcases hv_some st' t' i' m' rfl with ⟨ht'_eq, hnsend, hle_ep, hid', htcur', hcur', hvS', hca₂, hlast₂, hcnt₂,
            hcorr₂, hnh₂, hvR_t', hvR_nt', hsub₂, h_at_t⟩
          have ht'_pos : t' = r.pos.epoch := ht'_eq.trans hc_ep
          rw [hes₁]
          dsimp only
          exact Or.inr (accept_main_preserves hact P st' r.pos es₁.h
            (ht'_pos ▸ hnsend) (ht'_pos ▸ hle_ep) hid' (ht'_pos ▸ htcur') hcur' hvS'
            hca₂ hlast₂ hcnt₂ hcorr₂ hnh₂ hvR_t' hvR_nt' hsub₂
            (fun hpos_t sIdx hhon cnt hdr₀ e₀ hm => by
              rcases h_at_t (ht'_pos.trans hpos_t) with ⟨hPR, hi'_eq, _, hno_i', _⟩
              have hr_sender_t : r.pos.sender = Party.senderOf t := by
                rw [hr_send, hPR, other_receiverOf]
              have hidx_eq : r.pos.idx = i' := by
                have hct2 := ((hact.hon_book sIdx hhon).2 r hr_mem hr_sender_t hpos_t).1
                rw [hr_ct] at hct2
                exact hct2.symm.trans hi'_eq.symm
              rw [hidx_eq]
              exact hno_i' sIdx hhon cnt hdr₀ e₀ hm))

-- 4. `injectEGen` preserves `ShiftedSafe` (covers both `b1 = true` and `b1 = false`):
private theorem injectEGen_hooksFSMulti_main_safe {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (b1 : Bool)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka qep l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (q_ij : Party × (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))
    (es : ShiftedEState Γ Pt RSt I ℓ) :
    PubMainRel C ℓ encT idOf N
      (fun σ => ShiftedSafe l t es σ)
      (fun p σ' => ShiftedSafe l t p.2 σ')
      ((_root_.CryptoGames.SM.Engine.injectEGen b1
        (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
          ⟨authH, some (l - 1), t⟩ false false)
        (2 + Δcka) qep t (⟨true, some (l - 1), t⟩ : Mode).cfg q_ij).run es) := by
  rcases q_ij with ⟨P, c⟩
  intro rc σ hSafe z hz
  cases b1
  · -- `b1 = false` (`injectE`, `Δ = 2 + Δcka`)
    simp only [_root_.CryptoGames.SM.Engine.injectEGen, Bool.false_eq_true, ↓reduceIte,
      injectE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    rcases hSafe with hab | hact
    · simp only [hab, Bool.true_or, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl hab
    · by_cases hguard : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
          !(es.g.safeInj (2 + Δcka))) = true
      · simp only [hguard, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr hact
      · simp only [Bool.not_eq_true] at hguard
        have hit_false : (es.g.inTransit P.other c).isSome = false :=
          (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp hguard).1).2
        have hsafe_add : es.g.safeInj (2 + Δcka) = true :=
          by simpa using (Bool.or_eq_false_iff.mp hguard).2
        simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hz
        have hLift := PubMainRel.liftH C ℓ encT idOf N _ es
          (vRecv_hooksFSMulti_main_step C ℓ encT idOf N cka prng Δcka l t authH hAdm
            es σ hact P c none
            (fun _ _ _ => Or.inr (safeInj_two_of_safeInj_add hsafe_add))
            (fun _ => hit_false))
        refine (hLift.bind (Post := fun p σ' => ShiftedSafe l t p.2 σ') fun ⟨ro, es₁⟩ => ?_) rc σ rfl z hz
        cases ro with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PubMainRel.pure fun _ _ => Or.inl rfl
        | some r_in =>
          cases r_in with
          | none =>
            simp only [StateT.run_pure]
            refine PubMainRel.pure fun σ' ⟨hes₁, hv_none, _⟩ => ?_
            rw [hes₁]; exact Or.inr (hv_none trivial)
          | some quad =>
            rcases quad with ⟨st', t', i', m'⟩
            by_cases hqep_lt : qep + 1 < t'
            · simp only [hqep_lt, ↓reduceIte, StateT.run_pure]
              refine PubMainRel.pure fun σ' ⟨hes₁, _, hv_some⟩ => ?_
              rcases hv_some st' t' i' m' rfl with ⟨_, _, _, _, _, _, _, hca₂, hlast₂, hcnt₂,
                hcorr₂, hnh₂, _, _, hsub₂, _⟩
              rw [hes₁]
              exact Or.inr (shiftedActiveInv_of_book_shrink hact es₁.h hca₂ hlast₂ hcnt₂
                hcorr₂ hnh₂ hsub₂)
            · simp only [hqep_lt, ↓reduceIte]
              let pos : _root_.CryptoGames.SM.Pos := ⟨P.other, t', i'⟩
              by_cases htriv : es.g.trivial (2 + Δcka) pos = true
              · dsimp only [pos] at htriv
                simp only [htriv, ↓reduceIte, commitE, hooksFSMulti, StateT.run_bind,
                  liftH_pure_run, StateT.run_pure, StateT.run_modify, pure_bind]
                refine PubMainRel.pure fun σ' ⟨hes₁, _, hv_some⟩ => ?_
                rcases hv_some st' t' i' m' rfl with ⟨_, hnsend, hle_ep, hid', htcur', hcur', hvS', hca₂, hlast₂, hcnt₂,
                  hcorr₂, hnh₂, hvR_t', hvR_nt', hsub₂, h_at_t⟩
                rw [hes₁]
                dsimp only
                exact Or.inr (accept_main_preserves hact P st' pos es₁.h
                  hnsend hle_ep hid' htcur' hcur' hvS' hca₂ hlast₂ hcnt₂ hcorr₂ hnh₂ hvR_t' hvR_nt' hsub₂
                  (fun ht_eq sIdx hhon cnt hdr₀ e₀ hm =>
                    (h_at_t ht_eq).2.2.2.1 sIdx hhon cnt hdr₀ e₀ hm))
              · simp only [Bool.not_eq_true] at htriv
                have htriv' : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = false := htriv
                simp only [htriv', Bool.false_eq_true, ↓reduceIte]
                intro rc₁ σ' ⟨hes₁, _, hv_some⟩ z₁ hz₁
                rcases hv_some st' t' i' m' rfl with ⟨_, _, _, _, _, _, _, hca₂, hlast₂, hcnt₂,
                  hcorr₂, hnh₂, _, _, hsub₂, h_at_t⟩
                have ht'_ne : t' ≠ t := by
                  intro ht_eq
                  rcases h_at_t ht_eq with ⟨hPR, _, _, _, hforged⟩
                  rcases hforged trivial with ⟨sIdx, c₀, _, hc₀, hlt⟩
                  rcases hcorr₂ sIdx c₀ hc₀ with ⟨_, _, htL, hcp⟩
                  have hpos_eq : pos = ⟨Party.senderOf t, t, i'⟩ := by
                    simp [pos, hPR, ht_eq]
                  have htriv_true := trivial_true_of_corr_inv (Δ₀ := 2 + Δcka) (by omega) htL hcp hlt
                  rw [← hpos_eq, htriv] at htriv_true
                  exact nomatch htriv_true
                have hinj_f : (Mode.cfg (M := LibsignalMsgPublicPart × Plain ℓ) ⟨true, some (l - 1), t⟩).injectFull t' = false := by
                  simp [Mode.cfg, _root_.CryptoGames.SM.Config.auth, ht'_ne]
                simp only [hinj_f, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                  runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz₁
                subst hz₁
                rw [hes₁]
                exact Or.inr (shiftedActiveInv_of_book_shrink hact es₁.h hca₂ hlast₂ hcnt₂
                  hcorr₂ hnh₂ hsub₂)
  · -- `b1 = true` (`injectEB1`, `trivB1 t`)
    simp only [_root_.CryptoGames.SM.Engine.injectEGen, ↓reduceIte,
      _root_.CryptoGames.SM.Construction.DeliverForge.injectEB1,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    rcases hSafe with hab | hact
    · simp only [hab, Bool.true_or, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl hab
    · by_cases hguard : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
          !(es.g.safeInj 2)) = true
      · simp only [hguard, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr hact
      · simp only [Bool.not_eq_true] at hguard
        have hit_false : (es.g.inTransit P.other c).isSome = false :=
          (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp hguard).1).2
        have hsafe2 : es.g.safeInj 2 = true :=
          by simpa using (Bool.or_eq_false_iff.mp hguard).2
        simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hz
        have hLift := PubMainRel.liftH C ℓ encT idOf N _ es
          (vRecv_hooksFSMulti_main_step C ℓ encT idOf N cka prng Δcka l t authH hAdm
            es σ hact P c none
            (fun _ _ _ => Or.inr hsafe2)
            (fun _ => hit_false))
        refine (hLift.bind (Post := fun p σ' => ShiftedSafe l t p.2 σ') fun ⟨ro, es₁⟩ => ?_) rc σ rfl z hz
        cases ro with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PubMainRel.pure fun _ _ => Or.inl rfl
        | some r_in =>
          cases r_in with
          | none =>
            simp only [StateT.run_pure]
            refine PubMainRel.pure fun σ' ⟨hes₁, hv_none, _⟩ => ?_
            rw [hes₁]; exact Or.inr (hv_none trivial)
          | some quad =>
            rcases quad with ⟨st', t', i', m'⟩
            by_cases hqep_lt : qep + 1 < t'
            · simp only [hqep_lt, ↓reduceIte, StateT.run_pure]
              refine PubMainRel.pure fun σ' ⟨hes₁, _, hv_some⟩ => ?_
              rcases hv_some st' t' i' m' rfl with ⟨_, _, _, _, _, _, _, hca₂, hlast₂, hcnt₂,
                hcorr₂, hnh₂, _, _, hsub₂, _⟩
              rw [hes₁]
              exact Or.inr (shiftedActiveInv_of_book_shrink hact es₁.h hca₂ hlast₂ hcnt₂
                hcorr₂ hnh₂ hsub₂)
            · simp only [hqep_lt, ↓reduceIte]
              let pos : _root_.CryptoGames.SM.Pos := ⟨P.other, t', i'⟩
              by_cases htriv : _root_.CryptoGames.SM.Construction.DeliverForge.trivB1 t es.g pos = true
              · dsimp only [pos] at htriv
                simp only [htriv, ↓reduceIte, commitE, hooksFSMulti, StateT.run_bind,
                  liftH_pure_run, StateT.run_pure, StateT.run_modify, pure_bind]
                refine PubMainRel.pure fun σ' ⟨hes₁, _, hv_some⟩ => ?_
                rcases hv_some st' t' i' m' rfl with ⟨_, hnsend, hle_ep, hid', htcur', hcur', hvS', hca₂, hlast₂, hcnt₂,
                  hcorr₂, hnh₂, hvR_t', hvR_nt', hsub₂, h_at_t⟩
                rw [hes₁]
                dsimp only
                exact Or.inr (accept_main_preserves hact P st' pos es₁.h
                  hnsend hle_ep hid' htcur' hcur' hvS' hca₂ hlast₂ hcnt₂ hcorr₂ hnh₂ hvR_t' hvR_nt' hsub₂
                  (fun ht_eq sIdx hhon cnt hdr₀ e₀ hm =>
                    (h_at_t ht_eq).2.2.2.1 sIdx hhon cnt hdr₀ e₀ hm))
              · simp only [Bool.not_eq_true] at htriv
                have htriv' : _root_.CryptoGames.SM.Construction.DeliverForge.trivB1 t es.g ⟨P.other, t', i'⟩ = false := htriv
                simp only [htriv', Bool.false_eq_true, ↓reduceIte]
                intro rc₁ σ' ⟨hes₁, _, hv_some⟩ z₁ hz₁
                rcases hv_some st' t' i' m' rfl with ⟨_, _, _, _, _, _, _, hca₂, hlast₂, hcnt₂,
                  hcorr₂, hnh₂, _, _, hsub₂, h_at_t⟩
                have ht'_ne : t' ≠ t := by
                  intro ht_eq
                  rcases h_at_t ht_eq with ⟨hPR, _, _, _, hforged⟩
                  rcases hforged trivial with ⟨sIdx, c₀, _, hc₀, hlt⟩
                  rcases hcorr₂ sIdx c₀ hc₀ with ⟨_, _, htL, hcp⟩
                  have hpos_eq : pos = ⟨Party.senderOf t, t, i'⟩ := by
                    simp [pos, hPR, ht_eq]
                  have htriv2 := trivial_true_of_corr_inv (Δ₀ := 2) (by omega) htL hcp hlt
                  have htrivB1 : _root_.CryptoGames.SM.Construction.DeliverForge.trivB1 t es.g pos = true := by
                    simp [_root_.CryptoGames.SM.Construction.DeliverForge.trivB1, hpos_eq ▸ htriv2]
                  rw [htriv] at htrivB1
                  exact nomatch htrivB1
                have hinj_f : (Mode.cfg (M := LibsignalMsgPublicPart × Plain ℓ) ⟨true, some (l - 1), t⟩).injectFull t' = false := by
                  simp [Mode.cfg, _root_.CryptoGames.SM.Config.auth, ht'_ne]
                simp only [hinj_f, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                  runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz₁
                subst hz₁
                rw [hes₁]
                exact Or.inr (shiftedActiveInv_of_book_shrink hact es₁.h hca₂ hlast₂ hcnt₂
                  hcorr₂ hnh₂ hsub₂)

-- 5. `corrEShiftedPaper` preserves `ShiftedSafe`:
private theorem corrEShiftedPaper_hooksFSMulti_main_safe {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (P : Party) (es : ShiftedEState Γ Pt RSt I ℓ) :
    PubMainRel C ℓ encT idOf N
      (fun σ => ShiftedSafe l t es σ)
      (fun p σ' => ShiftedSafe l t p.2 σ')
      ((corrEShiftedPaper l
        (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
          ⟨authH, some (l - 1), t⟩ false false)
        (⟨true, some (l - 1), t⟩ : Mode).policy P).run es) := by
  intro rc σ hSafe z hz
  unfold corrEShiftedPaper at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  rcases hSafe with hab | hact
  · simp only [hab, Bool.true_or, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact Or.inl hab
  · by_cases hguard : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true
    · simp only [hguard, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inr hact
    · simp only [hguard, Bool.false_eq_true, ↓reduceIte, Mode.policy] at hz
      set s₁ := _root_.CryptoGames.SM.Construction.DeliverForge.afterCorrShifted l es.g P
      by_cases hdoom :
          ((_root_.CryptoGames.SM.Engine.Policy.mk true (some (l - 1)) t).leakDoom es.g s₁ ||
           (_root_.CryptoGames.SM.Engine.Policy.mk true (some (l - 1)) t).corrDoom es.g P) = true
      · simp only [hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, pure_bind, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact Or.inl rfl
      · simp only [Bool.not_eq_true] at hdoom
        have hleak_ok : ∀ lk ∈ s₁.leaks, lk ≤ l - 1 ∨ t ≤ lk :=
          leaks_ok_of_leakDoom_false (Bool.or_eq_false_iff.mp hdoom).1
        have hs₁_tL_mem : ∀ lk, s₁.tL = some lk → lk ∈ s₁.leaks := by
          intro lk hlk
          simp only [s₁, _root_.CryptoGames.SM.Construction.DeliverForge.afterCorrShifted,
            _root_.CryptoGames.SM.GameState.leak, Option.some.injEq] at hlk ⊢
          subst hlk; exact List.mem_cons_self
        have hs₁_tL_mono : ∀ lk₀, es.g.tL = some lk₀ → ∃ lk₁, s₁.tL = some lk₁ ∧ lk₀ ≤ lk₁ := by
          intro lk₀ hlk₀
          simp only [s₁, _root_.CryptoGames.SM.Construction.DeliverForge.afterCorrShifted,
            _root_.CryptoGames.SM.GameState.leak]
          exact ⟨_, rfl, le_maxOpt_of_some hlk₀ _⟩
        have hs₁_comp_sub : ∀ pos ∈ es.g.comp, pos ∈ s₁.comp := by
          intro pos hmem
          simp only [s₁, _root_.CryptoGames.SM.Construction.DeliverForge.afterCorrShifted,
            _root_.CryptoGames.SM.GameState.leak]
          exact List.mem_append_right _ hmem
        simp only [hdoom, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hz
        have hRev :
            PubMainRel C ℓ encT idOf N
              (fun σ₀ => σ₀ = σ)
              (fun p σ' =>
                ∀ st_out, p.1 = some st_out →
                  ShiftedActiveInv l t { es with g := s₁, h := p.2 } σ')
              (((hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
                  ⟨authH, some (l - 1), t⟩ false false).reveal es.g P (es.g.st P)).run es.h) := by
          dsimp only [hooksFSMulti]
          have hNoQuery :
              ShiftedActiveInv l t { es with g := s₁, h := es.h } σ :=
            { abort_false := hact.abort_false
              win_false := hact.win_false
              st_id := hact.st_id
              st_tcur := hact.st_tcur
              tL_mem := hs₁_tL_mem
              leaks_ok := hleak_ok
              trans_hdr := hact.trans_hdr
              cache_pre := hact.cache_pre
              cache_t_some := hact.cache_t_some
              cache_other_none := hact.cache_other_none
              vS_inr := hact.vS_inr
              sender_at_t := hact.sender_at_t
              sender_cka_at_t := hact.sender_cka_at_t
              trans_t_hdr := hact.trans_t_hdr
              vR_target := hact.vR_target
              vR_other := hact.vR_other
              non_hon_empty := hact.non_hon_empty
              hon_book := hact.hon_book
              router_last := hact.router_last
              router_corr := fun sIdx c₀ hc => by
                rcases hact.router_corr sIdx c₀ hc with ⟨hh, hle, ⟨lk₀, hlk₀, htle₀⟩, hcp⟩
                rcases hs₁_tL_mono lk₀ hlk₀ with ⟨lk₁, hlk₁, hle₀₁⟩
                exact ⟨hh, hle, ⟨lk₁, hlk₁, le_trans htle₀ hle₀₁⟩,
                  fun r hr hs he hlt => hs₁_comp_sub _ (hcp r hr hs he hlt)⟩ }
          cases hvS : (es.g.st P).vS with
          | none =>
            split_ifs <;> exact PubMainRel.pure fun _ hσ₀ _ _ => hσ₀ ▸ hNoQuery
          | some v =>
            cases v with
            | inl ss =>
              split_ifs <;> exact PubMainRel.pure fun _ hσ₀ _ _ => hσ₀ ▸ hNoQuery
            | inr sIdx =>
              rcases hact.vS_inr P sIdx hvS with ⟨hPS, hhon, hep_or⟩
              have hep_ge : t ≤ es.g.epoch P := by omega
              have htL_ge : ∃ lk, s₁.tL = some lk ∧ t ≤ lk :=
                afterCorrShifted_tL_ge_of_epoch_ge hAdm hep_ge
              simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
              intro rc₀ σ₀ hσ₀ z₀ hz₀
              subst σ₀
              simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz₀
              rcases hz₀ with ⟨v₀, hv₀, hzv₀⟩
              erw [liftFSMulti_run_query_eq (ℓ := ℓ) sIdx (.inl (.inl (.inl (.inr ())))) es.h] at hv₀
              rcases pubQuery_corruptSender_main C ℓ encT idOf N sIdx es.h rc₀ σ hv₀ with ⟨hhv₀, hcr_cases⟩
              rcases v₀ with ⟨⟨⟨res, h_a⟩, rc₁⟩, σ'⟩
              dsimp only at hhv₀ hcr_cases hzv₀
              subst hhv₀
              cases res with
              | none =>
                simp only [StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hzv₀
                subst hzv₀
                intro _ hfalse; exact nomatch hfalse
              | some ss =>
                rcases hcr_cases with ⟨st', rfl, hlast_st', ⟨hnone, _⟩ | ⟨_, _, hcorr_st'⟩⟩
                · exact nomatch hnone
                simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hzv₀
                let b_new : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                  { ((es.h.book sIdx).getD {}) with sCorr := true }
                let h_new : ShiftedHState Pt RSt I :=
                  { es.h with book := Function.update es.h.book sIdx (some b_new) }
                have hcnt_eq : ∀ s, ((h_new.book s).getD {}).fsCount = ((es.h.book s).getD {}).fsCount := by
                  intro s
                  by_cases hs : s = sIdx
                  · subst hs; simp [h_new, Function.update_self, b_new]
                  · simp [h_new, Function.update_of_ne hs]
                have htr_eq : ∀ s, ((h_new.book s).getD {}).fsTrans = ((es.h.book s).getD {}).fsTrans := by
                  intro s
                  by_cases hs : s = sIdx
                  · subst hs; simp [h_new, Function.update_self, b_new]
                  · simp [h_new, Function.update_of_ne hs]
                have hActiveNew :
                    ShiftedActiveInv l t
                      { es with g := s₁, h := h_new }
                      (Function.update σ sIdx (some st')) :=
                  { abort_false := hact.abort_false
                    win_false := hact.win_false
                    st_id := hact.st_id
                    st_tcur := hact.st_tcur
                    tL_mem := hs₁_tL_mem
                    leaks_ok := hleak_ok
                    trans_hdr := hact.trans_hdr
                    cache_pre := hact.cache_pre
                    cache_t_some := hact.cache_t_some
                    cache_other_none := hact.cache_other_none
                    vS_inr := hact.vS_inr
                    sender_at_t := fun hep => by
                      rcases hact.sender_at_t hep with ⟨s₀, hh₀, hv₀', hi₀⟩
                      exact ⟨s₀, hh₀, hv₀', hi₀.trans (hcnt_eq s₀).symm⟩
                    sender_cka_at_t := hact.sender_cka_at_t
                    trans_t_hdr := hact.trans_t_hdr
                    vR_target := hact.vR_target
                    vR_other := hact.vR_other
                    non_hon_empty := fun s hh =>
                      ⟨(hcnt_eq s).trans (hact.non_hon_empty s hh).1,
                       (htr_eq s).trans (hact.non_hon_empty s hh).2⟩
                    hon_book := fun s hh => by
                      refine ⟨fun cnt hdr₀ e₀ hm => ?_, fun r hr hrs hre => ?_⟩
                      · rw [htr_eq s] at hm
                        exact (hact.hon_book s hh).1 cnt hdr₀ e₀ hm
                      · rcases (hact.hon_book s hh).2 r hr hrs hre with ⟨h1, h2⟩
                        rw [← hcnt_eq s] at h2
                        exact ⟨h1, h2⟩
                    router_last := fun s => by
                      dsimp only
                      rw [hcnt_eq s]
                      by_cases hs : s = sIdx
                      · subst s
                        have h1 : sessLastIdx (Function.update σ sIdx (some st')) sIdx = st'.1.lastSentIdx := by
                          simp [sessLastIdx, Function.update_self]
                        exact h1.trans (hlast_st'.trans (hact.router_last sIdx))
                      · have h1 : sessLastIdx (Function.update σ sIdx (some st')) s = sessLastIdx σ s := by
                          simp [sessLastIdx, Function.update_of_ne hs]
                        exact h1.trans (hact.router_last s)
                    router_corr := fun s c₀ hc => by
                      dsimp only
                      rw [hcnt_eq s]
                      by_cases hs : s = sIdx
                      · subst s
                        have hc_eq : sessCorrAt (Function.update σ sIdx (some st')) sIdx = st'.1.senderCorruptedAt := by
                          simp [sessCorrAt, Function.update_self]
                        rw [hc_eq, hcorr_st', Option.some.injEq] at hc
                        cases hc_old : sessCorrAt σ sIdx with
                        | some c_old =>
                          rw [hc_old, Option.getD_some] at hc
                          subst hc
                          rcases hact.router_corr sIdx c_old hc_old with ⟨hh, hle, _, hcp⟩
                          exact ⟨hh, hle, htL_ge,
                            fun r hr hrs hre hlt => hs₁_comp_sub _ (hcp r hr hrs hre hlt)⟩
                        | none =>
                          rw [hc_old, Option.getD_none, hact.router_last sIdx] at hc
                          subst hc
                          refine ⟨hhon, le_rfl, htL_ge, fun r hr hrs hre hlt => ?_⟩
                          have hle := ((hact.hon_book sIdx hhon).2 r hr hrs hre).2
                          omega
                      · simp only [sessCorrAt, Function.update_of_ne hs] at hc
                        rcases hact.router_corr s c₀ hc with ⟨hh, hle, ⟨lk₀, hlk₀, htle₀⟩, hcp⟩
                        rcases hs₁_tL_mono lk₀ hlk₀ with ⟨lk₁, hlk₁, hle₀₁⟩
                        exact ⟨hh, hle, ⟨lk₁, hlk₁, le_trans htle₀ hle₀₁⟩,
                          fun r hr hrs hre hlt => hs₁_comp_sub _ (hcp r hr hrs hre hlt)⟩ }
                split_ifs at hzv₀
                · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hzv₀
                  subst hzv₀
                  intro _ hfalse; exact nomatch hfalse
                · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hzv₀
                  subst hzv₀
                  intro _ _; exact hActiveNew
        have hLift := PubMainRel.liftH C ℓ encT idOf N _ es hRev
        refine (hLift.bind (Post := fun p σ' => ShiftedSafe l t p.2 σ') fun ⟨stOpt, es₁⟩ => ?_) rc σ rfl z hz
        cases stOpt with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact PubMainRel.pure fun _ _ => Or.inl rfl
        | some st_out =>
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          refine PubMainRel.pure fun σ' ⟨hes₁, hInv⟩ => ?_
          rw [hes₁]
          exact Or.inr (hInv st_out rfl)

-- 6. `deliverForgeEGen` preserves `ShiftedSafe` (covers both `b1 = true` and `b1 = false`):
private theorem deliverForgeEGen_hooksFSMulti_main_safe {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (b1 : Bool)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka qep l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (q_df : Party × (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) ×
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))
    (es : ShiftedEState Γ Pt RSt I ℓ) :
    PubMainRel C ℓ encT idOf N
      (fun σ => ShiftedSafe l t es σ)
      (fun p σ' => ShiftedSafe l t p.2 σ')
      ((_root_.CryptoGames.SM.Engine.deliverForgeEGen b1
        (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
          ⟨authH, some (l - 1), t⟩ false false)
        (2 + Δcka) qep t (⟨true, some (l - 1), t⟩ : Mode).cfg q_df).run es) := by
  rcases q_df with ⟨P, c, c'⟩
  intro rc σ hSafe z hz
  cases b1
  · -- `b1 = false` (`deliverForgeE`, `Δ = 2 + Δcka`)
    simp only [_root_.CryptoGames.SM.Engine.deliverForgeEGen, Bool.false_eq_true, ↓reduceIte,
      deliverForgeE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    rcases hSafe with hab | hact
    · simp only [hab, Bool.true_or, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl hab
    · simp only [hact.abort_false, hact.win_false, Bool.or_self, Bool.false_eq_true,
        ↓reduceIte] at hz
      cases hrc_it : es.g.inTransit P.other c with
      | none =>
        simp only [hrc_it] at hz
        simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr hact
      | some r_c =>
        simp only [hrc_it] at hz
        have hrc_props : r_c ∈ es.g.trans ∧ r_c.pos.sender = P.other ∧ r_c.ct = c := by
          unfold _root_.CryptoGames.SM.GameState.inTransit at hrc_it
          have hmem := List.mem_of_find?_eq_some hrc_it
          have hpred := List.find?_some hrc_it
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
          exact ⟨hmem, hpred.1, hpred.2⟩
        by_cases hguard : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r_c.pos ||
            (c.1 != c'.1)) = true
        · simp only [hguard, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inr hact
        · simp only [Bool.not_eq_true] at hguard
          have hit_false : (es.g.inTransit P.other c').isSome = false :=
            (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp hguard).1).1
          have hc_hdr_eq : c.1 = c'.1 :=
            bne_eq_false_iff_eq.mp (Bool.or_eq_false_iff.mp hguard).2
          simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hz
          have hLift := PubMainRel.liftH C ℓ encT idOf N _ es
            (vRecv_hooksFSMulti_main_step C ℓ encT idOf N cka prng Δcka l t authH hAdm
              es σ hact P c' none
              (fun _ ht _ => Or.inl ⟨r_c, hrc_props.1, hrc_props.2.1,
                (congrArg Prod.fst hrc_props.2.2).trans hc_hdr_eq,
                ((hact.trans_hdr r_c hrc_props.1).1.symm.trans
                  (congrArg (fun x => x.1.1) hrc_props.2.2)).trans
                  ((congrArg Prod.fst hc_hdr_eq).trans ht)⟩)
              (fun _ => hit_false))
          refine (hLift.bind (Post := fun p σ' => ShiftedSafe l t p.2 σ') fun ⟨ro, es₁⟩ => ?_) rc σ rfl z hz
          cases ro with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PubMainRel.pure fun _ _ => Or.inl rfl
          | some r_in =>
            cases r_in with
            | none =>
              simp only [StateT.run_pure]
              refine PubMainRel.pure fun σ' ⟨hes₁, hv_none, _⟩ => ?_
              rw [hes₁]; exact Or.inr (hv_none trivial)
            | some quad =>
              rcases quad with ⟨st', t', i', m'⟩
              by_cases hbad_ep : (decide (qep + 1 < t') || (t' != r_c.pos.epoch)) = true
              · simp only [hbad_ep, ↓reduceIte, StateT.run_pure]
                refine PubMainRel.pure fun σ' ⟨hes₁, _, hv_some⟩ => ?_
                rcases hv_some st' t' i' m' rfl with ⟨_, _, _, _, _, _, _, hca₂, hlast₂, hcnt₂,
                  hcorr₂, hnh₂, _, _, hsub₂, _⟩
                rw [hes₁]
                exact Or.inr (shiftedActiveInv_of_book_shrink hact es₁.h hca₂ hlast₂ hcnt₂
                  hcorr₂ hnh₂ hsub₂)
              · simp only [Bool.not_eq_true] at hbad_ep
                simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte]
                let pos : _root_.CryptoGames.SM.Pos := ⟨P.other, t', i'⟩
                by_cases htriv : es.g.trivial (2 + Δcka) pos = true
                · dsimp only [pos] at htriv
                  simp only [htriv, ↓reduceIte, commitE, hooksFSMulti, StateT.run_bind,
                    liftH_pure_run, StateT.run_pure, StateT.run_modify, pure_bind]
                  refine PubMainRel.pure fun σ' ⟨hes₁, _, hv_some⟩ => ?_
                  rcases hv_some st' t' i' m' rfl with ⟨_, hnsend, hle_ep, hid', htcur', hcur', hvS', hca₂, hlast₂, hcnt₂,
                    hcorr₂, hnh₂, hvR_t', hvR_nt', hsub₂, h_at_t⟩
                  rw [hes₁]
                  dsimp only
                  exact Or.inr (accept_main_preserves hact P st' pos es₁.h
                    hnsend hle_ep hid' htcur' hcur' hvS' hca₂ hlast₂ hcnt₂ hcorr₂ hnh₂ hvR_t' hvR_nt' hsub₂
                    (fun ht_eq sIdx hhon cnt hdr₀ e₀ hm =>
                      (h_at_t ht_eq).2.2.2.1 sIdx hhon cnt hdr₀ e₀ hm))
                · simp only [Bool.not_eq_true] at htriv
                  have htriv' : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = false := htriv
                  simp only [htriv', Bool.false_eq_true, ↓reduceIte]
                  intro rc₁ σ' ⟨hes₁, _, hv_some⟩ z₁ hz₁
                  rcases hv_some st' t' i' m' rfl with ⟨_, _, _, _, _, _, _, hca₂, hlast₂, hcnt₂,
                    hcorr₂, hnh₂, _, _, hsub₂, h_at_t⟩
                  have ht'_ne : t' ≠ t := by
                    intro ht_eq
                    rcases h_at_t ht_eq with ⟨hPR, _, _, _, hforged⟩
                    rcases hforged trivial with ⟨sIdx, c₀, _, hc₀, hlt⟩
                    rcases hcorr₂ sIdx c₀ hc₀ with ⟨_, _, htL, hcp⟩
                    have hpos_eq : pos = ⟨Party.senderOf t, t, i'⟩ := by
                      simp [pos, hPR, ht_eq]
                    have htriv_true := trivial_true_of_corr_inv (Δ₀ := 2 + Δcka) (by omega) htL hcp hlt
                    rw [← hpos_eq, htriv] at htriv_true
                    exact nomatch htriv_true
                  have hinj_f : (Mode.cfg (M := LibsignalMsgPublicPart × Plain ℓ) ⟨true, some (l - 1), t⟩).injectFull t' = false := by
                    simp [Mode.cfg, _root_.CryptoGames.SM.Config.auth, ht'_ne]
                  simp only [hinj_f, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                    runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz₁
                  subst hz₁
                  rw [hes₁]
                  exact Or.inr (shiftedActiveInv_of_book_shrink hact es₁.h hca₂ hlast₂ hcnt₂
                    hcorr₂ hnh₂ hsub₂)
  · -- `b1 = true` (`deliverForgeEB1`, `trivB1 t`)
    simp only [_root_.CryptoGames.SM.Engine.deliverForgeEGen, ↓reduceIte,
      _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    rcases hSafe with hab | hact
    · simp only [hab, Bool.true_or, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl hab
    · simp only [hact.abort_false, hact.win_false, Bool.or_self, Bool.false_eq_true,
        ↓reduceIte] at hz
      cases hrc_it : es.g.inTransit P.other c with
      | none =>
        simp only [hrc_it] at hz
        simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr hact
      | some r_c =>
        simp only [hrc_it] at hz
        have hrc_props : r_c ∈ es.g.trans ∧ r_c.pos.sender = P.other ∧ r_c.ct = c := by
          unfold _root_.CryptoGames.SM.GameState.inTransit at hrc_it
          have hmem := List.mem_of_find?_eq_some hrc_it
          have hpred := List.find?_some hrc_it
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
          exact ⟨hmem, hpred.1, hpred.2⟩
        by_cases hguard : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r_c.pos ||
            (c.1 != c'.1)) = true
        · simp only [hguard, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inr hact
        · simp only [Bool.not_eq_true] at hguard
          have hit_false : (es.g.inTransit P.other c').isSome = false :=
            (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp hguard).1).1
          have hc_hdr_eq : c.1 = c'.1 :=
            bne_eq_false_iff_eq.mp (Bool.or_eq_false_iff.mp hguard).2
          simp only [hguard, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hz
          have hLift := PubMainRel.liftH C ℓ encT idOf N _ es
            (vRecv_hooksFSMulti_main_step C ℓ encT idOf N cka prng Δcka l t authH hAdm
              es σ hact P c' none
              (fun _ ht _ => Or.inl ⟨r_c, hrc_props.1, hrc_props.2.1,
                (congrArg Prod.fst hrc_props.2.2).trans hc_hdr_eq,
                ((hact.trans_hdr r_c hrc_props.1).1.symm.trans
                  (congrArg (fun x => x.1.1) hrc_props.2.2)).trans
                  ((congrArg Prod.fst hc_hdr_eq).trans ht)⟩)
              (fun _ => hit_false))
          refine (hLift.bind (Post := fun p σ' => ShiftedSafe l t p.2 σ') fun ⟨ro, es₁⟩ => ?_) rc σ rfl z hz
          cases ro with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PubMainRel.pure fun _ _ => Or.inl rfl
          | some r_in =>
            cases r_in with
            | none =>
              simp only [StateT.run_pure]
              refine PubMainRel.pure fun σ' ⟨hes₁, hv_none, _⟩ => ?_
              rw [hes₁]; exact Or.inr (hv_none trivial)
            | some quad =>
              rcases quad with ⟨st', t', i', m'⟩
              by_cases hbad_ep : (decide (qep + 1 < t') || (t' != r_c.pos.epoch)) = true
              · simp only [hbad_ep, ↓reduceIte, StateT.run_pure]
                refine PubMainRel.pure fun σ' ⟨hes₁, _, hv_some⟩ => ?_
                rcases hv_some st' t' i' m' rfl with ⟨_, _, _, _, _, _, _, hca₂, hlast₂, hcnt₂,
                  hcorr₂, hnh₂, _, _, hsub₂, _⟩
                rw [hes₁]
                exact Or.inr (shiftedActiveInv_of_book_shrink hact es₁.h hca₂ hlast₂ hcnt₂
                  hcorr₂ hnh₂ hsub₂)
              · simp only [Bool.not_eq_true] at hbad_ep
                simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte]
                let pos : _root_.CryptoGames.SM.Pos := ⟨P.other, t', i'⟩
                by_cases htriv : _root_.CryptoGames.SM.Construction.DeliverForge.trivB1 t es.g pos = true
                · dsimp only [pos] at htriv
                  simp only [htriv, ↓reduceIte, commitE, hooksFSMulti, StateT.run_bind,
                    liftH_pure_run, StateT.run_pure, StateT.run_modify, pure_bind]
                  refine PubMainRel.pure fun σ' ⟨hes₁, _, hv_some⟩ => ?_
                  rcases hv_some st' t' i' m' rfl with ⟨_, hnsend, hle_ep, hid', htcur', hcur', hvS', hca₂, hlast₂, hcnt₂,
                    hcorr₂, hnh₂, hvR_t', hvR_nt', hsub₂, h_at_t⟩
                  rw [hes₁]
                  dsimp only
                  exact Or.inr (accept_main_preserves hact P st' pos es₁.h
                    hnsend hle_ep hid' htcur' hcur' hvS' hca₂ hlast₂ hcnt₂ hcorr₂ hnh₂ hvR_t' hvR_nt' hsub₂
                    (fun ht_eq sIdx hhon cnt hdr₀ e₀ hm =>
                      (h_at_t ht_eq).2.2.2.1 sIdx hhon cnt hdr₀ e₀ hm))
                · simp only [Bool.not_eq_true] at htriv
                  have htriv' : _root_.CryptoGames.SM.Construction.DeliverForge.trivB1 t es.g ⟨P.other, t', i'⟩ = false := htriv
                  simp only [htriv', Bool.false_eq_true, ↓reduceIte]
                  intro rc₁ σ' ⟨hes₁, _, hv_some⟩ z₁ hz₁
                  rcases hv_some st' t' i' m' rfl with ⟨_, _, _, _, _, _, _, hca₂, hlast₂, hcnt₂,
                    hcorr₂, hnh₂, _, _, hsub₂, h_at_t⟩
                  have ht'_ne : t' ≠ t := by
                    intro ht_eq
                    rcases h_at_t ht_eq with ⟨hPR, _, _, _, hforged⟩
                    rcases hforged trivial with ⟨sIdx, c₀, _, hc₀, hlt⟩
                    rcases hcorr₂ sIdx c₀ hc₀ with ⟨_, _, htL, hcp⟩
                    have hpos_eq : pos = ⟨Party.senderOf t, t, i'⟩ := by
                      simp [pos, hPR, ht_eq]
                    have htriv2 := trivial_true_of_corr_inv (Δ₀ := 2) (by omega) htL hcp hlt
                    have htrivB1 : _root_.CryptoGames.SM.Construction.DeliverForge.trivB1 t es.g pos = true := by
                      simp [_root_.CryptoGames.SM.Construction.DeliverForge.trivB1, hpos_eq ▸ htriv2]
                    rw [htriv] at htrivB1
                    exact nomatch htrivB1
                  have hinj_f : (Mode.cfg (M := LibsignalMsgPublicPart × Plain ℓ) ⟨true, some (l - 1), t⟩).injectFull t' = false := by
                    simp [Mode.cfg, _root_.CryptoGames.SM.Config.auth, ht'_ne]
                  simp only [hinj_f, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                    runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz₁
                  subst hz₁
                  rw [hes₁]
                  exact Or.inr (shiftedActiveInv_of_book_shrink hact es₁.h hca₂ hlast₂ hcnt₂
                    hcorr₂ hnh₂ hsub₂)

-- Full 1-step dispatch for `implEDFShiftedPaperGen` at `la = false`:
private theorem implEDFShiftedPaperGen_step_main_safe {KC Γ CCoins Pt KR RSt I : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins] [SampleableType KR]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (b1 : Bool)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka qep l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (q : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
      (_root_.CryptoGames.SM.Construction.PartyState Γ Pt RSt
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (es : ShiftedEState Γ Pt RSt I ℓ) :
    PubMainRel C ℓ encT idOf N
      (fun σ => ShiftedSafe l t es σ)
      (fun p σ' => ShiftedSafe l t p.2 σ')
      ((implEDFShiftedPaperGen b1 l
        (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
          ⟨authH, some (l - 1), t⟩ false false)
        (2 + Δcka) qep maxForwardJumps t
        (⟨true, some (l - 1), t⟩ : Mode).cfg
        (⟨true, some (l - 1), t⟩ : Mode).policy q).run es) := by
  rcases q with n | (((((q_tr | q_ch) | q_dl) | q_ij) | q_cr) | q_df)
  · dsimp only [implEDFShiftedPaperGen, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, coinsE]
    rw [stateT_lift_run]
    intro rc σ hSafe z hz
    simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, simulateQ_HasQuery_query,
      pubMultiImpl, stateT_lift_run, idealSessImpl, sessLift_inl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
      StateT.run_pure, simulateQ_pure, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hSafe
  · exact transmitE_hooksFSMulti_main_safe C ℓ encT idOf N cka prng Δcka qep l t authH hAdm q_tr es
  · exact challE_hooksFSMulti_main_safe C ℓ encT idOf N cka prng Δcka qep l t authH q_ch es
  · exact deliverE_hooksFSMulti_main_safe C ℓ encT idOf N cka prng Δcka l t authH hAdm q_dl es
  · exact injectEGen_hooksFSMulti_main_safe C ℓ encT idOf N b1 cka prng Δcka qep l t authH hAdm q_ij es
  · exact corrEShiftedPaper_hooksFSMulti_main_safe C ℓ encT idOf N cka prng Δcka l t authH hAdm q_cr es
  · exact deliverForgeEGen_hooksFSMulti_main_safe C ℓ encT idOf N b1 cka prng Δcka qep l t authH hAdm q_df es

-- Induction over `simulateQ` for `A` at `la = false`:
private theorem simulateQ_implEDFShiftedPaperGen_main_safe {KC Γ CCoins Pt KR RSt I α : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType I] [SampleableType CCoins] [SampleableType KR]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (b1 : Bool)
    (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins Pt I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I (BitVec 256))
    (Δcka qep l t : ℕ) (authH : Bool) (hAdm : (l - 1) + (2 + Δcka) ≤ t)
    (x : OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
      (_root_.CryptoGames.SM.Construction.PartyState Γ Pt RSt
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) α)
    (es : ShiftedEState Γ Pt RSt I ℓ) :
    PubMainRel C ℓ encT idOf N
      (fun σ => ShiftedSafe l t es σ)
      (fun p σ' => ShiftedSafe l t p.2 σ')
      ((simulateQ (implEDFShiftedPaperGen b1 l
        (hooksFSMulti cka prng (ShiftedFS Pt C ℓ encT idOf) Δcka
          ⟨authH, some (l - 1), t⟩ false false)
        (2 + Δcka) qep maxForwardJumps t
        (⟨true, some (l - 1), t⟩ : Mode).cfg
        (⟨true, some (l - 1), t⟩ : Mode).policy) x).run es) := by
  induction x using OracleComp.inductionOn generalizing es with
  | pure a => exact PubMainRel.pure fun _ hSafe => hSafe
  | query_bind q r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    exact (implEDFShiftedPaperGen_step_main_safe C ℓ encT idOf N b1 cka prng
      Δcka qep l t authH hAdm q es).bind fun ⟨ans, es'⟩ => ih ans es'

end ShiftedMainProof

section MultiSessEndZero

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)

/-- Ideal-cutoff (`hp cut cut la`) zero-output theorem for `redFSAuthDFShiftedPaperMultiGen`
(`B1` and `B2`). -/
theorem multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka qep l t : ℕ) (authH la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : 2 * q ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t authH la' A))
      la = 0 := by
  let cka := dhScheme Dh
  let prng := CryptoGames.Ratchet.rootPRNG C.F encPt
  let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  let AdvPub := fun la' =>
    redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l t authH la' A
  have hqb : ∀ la' s,
      (AdvPub la').IsQueryBoundP (fun x => sessQueryAt s x = true) (2 * q) := by
    intro la' s
    convert redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP
      cka prng fs lam q Δcka qep l t authH la' A hq s using 1
    funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  refine multiSessEndWinProb_eq_zero_of_hpIdeal C ℓ encT idOf q qR AdvPub la
    hqb hqR ?_
  apply multiSessPubToAD_support_of_runPubIdeal
  let N := authHopCutoff maxForwardJumps qR la
  cases la with
  | true =>
    intro w hw
    dsimp only [AdvPub, redFSAuthDFShiftedPaperMultiGen, runFSMultiDFShiftedPaper] at hw
    rw [bind_assoc] at hw
    have hRun :
        PubLaSafe C ℓ encT idOf N (fun b_out => b_out = false)
          (initFSMultiRaw cka prng fs lam ⟨authH, some (l - 1), t⟩ false >>= fun es₀ =>
            (simulateQ (implEDFShiftedPaperGen (!authH) l
              (hooksFSMulti cka prng fs Δcka ⟨authH, some (l - 1), t⟩ false true)
              (2 + Δcka) qep fs.maxSkip t
              (⟨true, some (l - 1), t⟩ : Mode).cfg
              (⟨true, some (l - 1), t⟩ : Mode).policy) A).run es₀ >>= fun p =>
              pure p.2.h.lfWin) := by
      refine (initFSMultiRaw_la_safe C ℓ encT idOf N cka prng lam ⟨authH, some (l - 1), t⟩ false).bind
        fun es₀ hes₀ => ?_
      refine (simulateQ_implEDFShiftedPaperGen_la_safe C ℓ encT idOf N (!authH) l cka prng
        Δcka qep t ⟨authH, some (l - 1), t⟩ ⟨true, some (l - 1), t⟩ A es₀ hes₀).bind
        fun p hp => PubLaSafe.pure hp
    exact (hRun (fun _ => false) (fun _ => none) (fun _ _ h => nomatch h) w hw).1
  | false =>
    by_cases hAdm : (l - 1) + (2 + Δcka) ≤ t
    · intro w hw
      dsimp only [AdvPub, redFSAuthDFShiftedPaperMultiGen, runFSMultiDFShiftedPaper] at hw
      have hfs_skip : fs.maxSkip = maxForwardJumps := rfl
      rw [hfs_skip, bind_assoc] at hw
      have ht2 : 2 ≤ t := by omega
      simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hw
      rcases hw with ⟨w₀, hw₀, hw₁⟩
      have hSafe₀ : ShiftedSafe l t w₀.1.1 w₀.2 :=
        initFSMultiRaw_main_safe C ℓ encT idOf N cka prng lam l t authH ht2
          (fun _ => false) (fun _ => none) rfl w₀ hw₀
      rcases hw₁ with ⟨w₁, hw₁, hw₂⟩
      have hSafe₁ : ShiftedSafe l t w₁.1.1.2 w₁.2 :=
        simulateQ_implEDFShiftedPaperGen_main_safe C ℓ encT idOf N (!authH) cka prng
          Δcka qep l t authH hAdm A w₀.1.1 w₀.1.2 w₀.2 hSafe₀ w₁ hw₁
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw₂
      subst hw₂
      exact authOut_eq_false_of_shiftedSafe Δcka l t w₁.1.1.2 w₁.2 hSafe₁
    · intro w hw
      dsimp only [AdvPub, redFSAuthDFShiftedPaperMultiGen, runFSMultiDFShiftedPaper] at hw
      simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hw
      rcases hw with ⟨p, _, hwp⟩
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hwp
      subst hwp
      exact authOut_eq_false_of_not_adm Δcka l t hAdm p.1.1.2

/-- Ideal-cutoff (`hp cut cut la`, `min (2 * q) (q + 2) ≤ qR`) zero-output theorem for
`redFSAuthDFShiftedPaperMultiGen` (`B1` and `B2`). -/
theorem multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero_min
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka qep l t : ℕ) (authH la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : min (2 * q) (q + 2) ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t authH la' A))
      la = 0 := by
  let cka := dhScheme Dh
  let prng := CryptoGames.Ratchet.rootPRNG C.F encPt
  let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  let AdvPub := fun la' =>
    redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l t authH la' A
  have hqb : ∀ la' s,
      (AdvPub la').IsQueryBoundP (fun x => sessQueryAt s x = true) (min (2 * q) (q + 2)) := by
    intro la' s
    convert redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP_min
      cka prng fs lam q Δcka qep l t authH la' A hq s using 1
    funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  refine multiSessEndWinProb_eq_zero_of_hpIdeal_gen C ℓ encT idOf (min (2 * q) (q + 2)) qR AdvPub la
    hqb hqR ?_
  apply multiSessPubToAD_support_of_runPubIdeal
  let N := authHopCutoff maxForwardJumps qR la
  cases la with
  | true =>
    intro w hw
    dsimp only [AdvPub, redFSAuthDFShiftedPaperMultiGen, runFSMultiDFShiftedPaper] at hw
    rw [bind_assoc] at hw
    have hRun :
        PubLaSafe C ℓ encT idOf N (fun b_out => b_out = false)
          (initFSMultiRaw cka prng fs lam ⟨authH, some (l - 1), t⟩ false >>= fun es₀ =>
            (simulateQ (implEDFShiftedPaperGen (!authH) l
              (hooksFSMulti cka prng fs Δcka ⟨authH, some (l - 1), t⟩ false true)
              (2 + Δcka) qep fs.maxSkip t
              (⟨true, some (l - 1), t⟩ : Mode).cfg
              (⟨true, some (l - 1), t⟩ : Mode).policy) A).run es₀ >>= fun p =>
              pure p.2.h.lfWin) := by
      refine (initFSMultiRaw_la_safe C ℓ encT idOf N cka prng lam ⟨authH, some (l - 1), t⟩ false).bind
        fun es₀ hes₀ => ?_
      refine (simulateQ_implEDFShiftedPaperGen_la_safe C ℓ encT idOf N (!authH) l cka prng
        Δcka qep t ⟨authH, some (l - 1), t⟩ ⟨true, some (l - 1), t⟩ A es₀ hes₀).bind
        fun p hp => PubLaSafe.pure hp
    exact (hRun (fun _ => false) (fun _ => none) (fun _ _ h => nomatch h) w hw).1
  | false =>
    by_cases hAdm : (l - 1) + (2 + Δcka) ≤ t
    · intro w hw
      dsimp only [AdvPub, redFSAuthDFShiftedPaperMultiGen, runFSMultiDFShiftedPaper] at hw
      have hfs_skip : fs.maxSkip = maxForwardJumps := rfl
      rw [hfs_skip, bind_assoc] at hw
      have ht2 : 2 ≤ t := by omega
      simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hw
      rcases hw with ⟨w₀, hw₀, hw₁⟩
      have hSafe₀ : ShiftedSafe l t w₀.1.1 w₀.2 :=
        initFSMultiRaw_main_safe C ℓ encT idOf N cka prng lam l t authH ht2
          (fun _ => false) (fun _ => none) rfl w₀ hw₀
      rcases hw₁ with ⟨w₁, hw₁, hw₂⟩
      have hSafe₁ : ShiftedSafe l t w₁.1.1.2 w₁.2 :=
        simulateQ_implEDFShiftedPaperGen_main_safe C ℓ encT idOf N (!authH) cka prng
          Δcka qep l t authH hAdm A w₀.1.1 w₀.1.2 w₀.2 hSafe₀ w₁ hw₁
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw₂
      subst hw₂
      exact authOut_eq_false_of_shiftedSafe Δcka l t w₁.1.1.2 w₁.2 hSafe₁
    · intro w hw
      dsimp only [AdvPub, redFSAuthDFShiftedPaperMultiGen, runFSMultiDFShiftedPaper] at hw
      simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hw
      rcases hw with ⟨p, _, hwp⟩
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hwp
      subst hwp
      exact authOut_eq_false_of_not_adm Δcka l t hAdm p.1.1.2

end MultiSessEndZero

end

end Computational.Proofs.E2E.SessionAuthMultiEnd

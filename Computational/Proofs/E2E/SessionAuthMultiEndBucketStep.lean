/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiEndBase -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiEndBucketLa -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiEndBucketSteps -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthMultiEndBucketHooks
import Computational.Proofs.E2E.SessionAuthMultiEndBucketRecv

import Computational.Proofs.E2E.SessionAuthMultiEndBucketCorr
import Computational.Proofs.E2E.SessionAuthMultiEndBucketTransmit
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
/-!
# Unified Single-Step `BucketInv` Preservation for `DeliverForgePaperMultiBucket`

Proves single-query preservation of `BucketInv` across `implEDFPaperBucketRaw`, `withWinEpDF`,
and `withWinEpDFMode gMain` (`la = false`, `1 ≤ q`, `2 ≤ Δbucket`), covering all seven arms
(`coinsE`, `transmitEBucket`, `challEBucket`, `deliverE`, `injectE`, `corrEPaperBucket`,
and `deliverForgeE`).-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEndBucketStep

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (
  LibsignalMsgPublicPart LibsignalCiphertextWithSalt32 lFS lChainPRG)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run)
open _root_.CryptoGames.SM (GameState Pos Record RecvResult healedBy maxOpt ltOpt lastLeakGuessAdmissible)
open _root_.CryptoGames.SM.Construction (
  Header FSMultiSpec FSMultiBook FSMultiDFBucketState
  hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode
  isHonestHdrFSMultiDFBucket inStage2BucketGen bucketAuthCfgGen postLeakDFBucket healEpoch)
open _root_.CryptoGames.SM.Engine (
  VP Ctx EState Hooks liftH abortE vSend vRecv commitE deliverE injectE coinsE)
open _root_.CryptoGames.SM.Construction.DeliverForge (
  AdversaryDF MakesAtMostQueriesDF deliverForgeE corrEPaperBucket
  transmitEBucket challEBucket implEDFPaperBucketRaw implEDFPaperBucket
  implEDFPaperBucketMode withWinEpDF withWinEpDFMode dfQueryTargetEpoch)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (
  lazyInit_run_none' lazyInit_run_some' sessLift_inl)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit)
open _root_.CryptoVerification.E2E.Signed.SessionWire (hpIdeal)
open _root_.CryptoGames.FSAEAD.Thm5 (HState corruptSenderH hInit)
open Computational.Proofs.E2E.SessionAuthMultiEnd (
  IdealHSt PubMultiSpec pubMultiImpl idealSessImpl runPubIdeal)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketLa (
  runPubIdeal_bind_support_false CoinOnly)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketSteps (
  corruptSenderH_hpIdeal_false_step_spec
  runPubIdeal_liftFSMultiDFBucket_corruptSender_support
  healEpoch_le_of_inStage2BucketGen ltOpt_of_ge_healEpoch
  startSend_bucket_coinOnly startRecv_bucket_coinOnly startRecv_bucketMode_coinOnly
  BucketEState IsTargetEpoch EpochBad EpochCompEntry EpochPre
  EpochIdealAt EpochIdeal EpochInv GlobalBucketWF BucketWon BucketActive BucketInv)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketHooks (
  fsSend_inr_bucket_any_support)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketRecv (
  GlobalBucketWF_mono_rem BucketActive_mono_rem BucketInv_mono_rem
  fsSend_inr_bucket_step_post vRecv_bucket_step)

section BucketStep

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

open Computational.Proofs.E2E.SessionAuthMultiEndBucketCorr (
  healedBy_of_leak tL_mem_of_leak EpochBad.of_sub_leaks block_eq_imp_epoch_eq
  EpochInv.record_ne corrEPaperBucket_bucket_step)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketTransmit (
  transmitEBucket_bucket_step)

/-! ## 4. Unified 6-Oracle `implEDFPaperBucketRaw` Step & `withWinEpDF` / `withWinEpDFMode` Wrappers -/

private theorem runPubIdeal_liftH_bind_support {α β : Type}
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    (x : StateT (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
      (OracleComp (unifSpec + FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))) α)
    (k : α → StateT (BucketEState Pt ℓ)
      (OracleComp (unifSpec + FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))) β)
    (es : BucketEState Pt ℓ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    {w : ((β × BucketEState Pt ℓ) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ))}
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false ((liftH x >>= k).run es) rc σ)) :
    ∃ w_vr ∈ support (runPubIdeal C ℓ encT idOf N false (x.run es.h) rc σ),
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        ((k w_vr.1.1.1).run { es with h := w_vr.1.1.2 }) w_vr.1.2 w_vr.2) := by
  simp only [StateT.run_bind] at hw
  rcases runPubIdeal_bind_support_false _ _ rc σ hw with ⟨w_v, hw_v, hw_fin⟩
  change w_v ∈ support (runPubIdeal C ℓ encT idOf N false
    (x.run es.h >>= fun p => Pure.pure (p.1, { es with h := p.2 })) rc σ) at hw_v
  rcases runPubIdeal_bind_support_false _ _ rc σ hw_v with ⟨w_vr, hw_vr, hw_lp⟩
  simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hw_lp
  subst hw_lp
  exact ⟨w_vr, hw_vr, hw_fin⟩

private theorem implEDFPaperBucketRaw_inr_step
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hq : 1 ≤ q) (hΔb : 2 ≤ Δbucket)
    (hk : Hooks (FSMultiSpec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (hss_eq : hk.startSend = (hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).startSend)
    (hfs_eq : hk.fsSend = (hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).fsSend)
    (hfr_eq : hk.fsRecv = (hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).fsRecv)
    (hcm_eq : hk.commit = (hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).commit)
    (hsr_spec : ∀ t_recv P ctx γ σr Tn hs,
      (hs.sessions t_recv).length < q →
      CoinOnly (fun p =>
        p.2.cache = hs.cache ∧
        p.2.book = hs.book ∧
        (p.2.sessions t_recv).length ≤ (hs.sessions t_recv).length + 1 ∧
        (∀ u', u' ≠ t_recv → p.2.sessions u' = hs.sessions u') ∧
        (p.1 = none ∨ p.1 = some none ∨
          ∃ γ' σr' rsv, p.1 = some (some (γ', σr', rsv)) ∧
            ((∃ σc k optIdx, hs.cache t_recv = some (Tn, σc, k, optIdx) ∧
                ((optIdx = none ∧ ∃ rs, rsv = .inl rs) ∨ (∃ s₀, optIdx = some s₀ ∧ rsv = .inr s₀))) ∨
             ((∀ σc k optIdx, hs.cache t_recv ≠ some (Tn, σc, k, optIdx)) ∧
                t_recv ≤ qep + 1 ∧ inStage2BucketGen Δbucket tL par t_recv = true ∧
                ((postLeakDFBucket tL ctx = true ∧ ∃ rs, rsv = .inl rs) ∨
                 (postLeakDFBucket tL ctx = false ∧
                   ∃ sIdx, rsv = .inr sIdx ∧ sIdx / q = t_recv - healEpoch tL))))))
        C ℓ encT idOf N ((hk.startRecv ctx P t_recv γ σr Tn).run hs))
    (hrv_spec : ∀ ctx P vp hs rc σ w,
      w ∈ support (runPubIdeal C ℓ encT idOf N false ((hk.reveal ctx P vp).run hs) rc σ) →
      (w.1.1.1 = none) ∨
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).reveal
          ctx P vp).run hs) rc σ))
    (rem' : ℕ)
    (qdf : (CryptoGames.SM.Construction.DeliverForge.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (es : BucketEState Pt ℓ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hact : BucketActive q Δcka Δbucket qep tL par (rem' + 1) (es, none) σ)
    (w : _)
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((implEDFPaperBucketRaw hk (2 + Δcka) qep maxForwardJumps
        (bucketAuthCfgGen Δbucket tL par) (.inr qdf)).run es) rc σ)) :
    w.1.1.2.abort = true ∨
    (w.1.1.2.g.win = false ∧ BucketActive q Δcka Δbucket qep tL par rem' (w.1.1.2, none) w.2) ∨
    (w.1.1.2.g.win = true ∧
      ∀ tWin, dfQueryTargetEpoch (St := Fig8St Pt) (fun c : Fig8C Pt => c.1.1) (.inr qdf) = some tWin →
        lastLeakGuessAdmissible (2 + Δcka) tL tWin = false ∨ EpochBad tL tWin w.1.1.2.g) := by
  have hwf := hact.2.1
  have habort_f : es.abort = false := hwf.habort
  have hwin_f : es.g.win = false := hwf.hwin
  rcases qdf with ((((⟨P, pm, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · -- 1. `transmitEBucket`
    rcases transmitEBucket_bucket_step C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
        hq hΔb hk hss_eq hfs_eq rem' P pm r es rc σ hact w hw with hab | hok
    · exact Or.inl hab
    · exact Or.inr (Or.inl hok)
  · -- 2. `challEBucket`
    change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((challEBucket ⟨P, m₀, m₁, r⟩).run es) rc σ) at hw
    simp only [challEBucket,
      StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact Or.inr (Or.inl ⟨hwin_f, BucketActive_mono_rem hact (Nat.le_succ rem')⟩)
  · -- 3. `deliverE`
    change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((deliverE hk maxForwardJumps (bucketAuthCfgGen Δbucket tL par) ⟨P, c⟩).run es) rc σ) at hw
    simp only [deliverE,
      StateT.run_bind, StateT.run_get, pure_bind, habort_f, hwin_f, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte] at hw
    cases hit_find : es.g.inTransit P.other c with
    | none =>
      simp only [hit_find, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hw
      subst hw
      exact Or.inr (Or.inl ⟨hwin_f, BucketActive_mono_rem hact (Nat.le_succ rem')⟩)
    | some r_del =>
      have hr_mem : r_del ∈ es.g.trans := List.mem_of_find?_eq_some hit_find
      have hr_pred := List.find?_some hit_find
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
      have hr_ep : r_del.pos.epoch = c.1.1 :=
        (hwf.htrans_wf r_del hr_mem).1.trans (congrArg (fun x => x.1.1) hr_pred.2)
      simp only [hit_find] at hw
      rcases runPubIdeal_liftH_bind_support _ _ es rc σ hw with ⟨w_vr, hw_vr, hw_fin⟩
      rcases vRecv_bucket_step C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
          hq hΔb hk hfr_eq hsr_spec rem' P es rc σ hact c (some r_del)
          (Or.inr ⟨r_del, hr_mem, congrArg Prod.fst hr_pred.2⟩)
          w_vr hw_vr with hvr_none | ⟨hvr_rej, hact_rej⟩ | ⟨st', i', m', hvr_acc, _, _, hacc_inv⟩
      · simp only [hvr_none, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
        subst hw_fin; exact Or.inl rfl
      · simp only [hvr_rej, bucketAuthCfgGen, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
        subst hw_fin; exact Or.inr (Or.inl ⟨hwin_f, hact_rej⟩)
      · rw [hvr_acc] at hw_fin
        unfold commitE at hw_fin
        rw [hcm_eq] at hw_fin
        dsimp only [hooksFSMultiDFBucketPaper, liftH] at hw_fin
        simp only [bucketAuthCfgGen, StateT.run_bind, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte, runPubIdeal] at hw_fin
        subst hw_fin
        have hidem : { es.g.accept P st' r_del.pos with
            st := Function.update (es.g.accept P st' r_del.pos).st P st' } =
            es.g.accept P st' r_del.pos := by
          cases es.g; simp [GameState.accept, Function.update_idem]
        rw [hidem]
        have hact' := hacc_inv r_del.pos hr_ep (Or.inr ⟨r_del, hr_mem, rfl, rfl, hr_pred.2⟩)
        exact Or.inr (Or.inl ⟨hact'.2.1.hwin, hact'⟩)
  · -- 4. `injectE`
    change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((injectE hk (2 + Δcka) qep (bucketAuthCfgGen Δbucket tL par) ⟨P, c⟩).run es) rc σ) at hw
    simp only [injectE,
      StateT.run_bind, StateT.run_get, pure_bind] at hw
    split_ifs at hw with hguard
    · simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hw
      subst hw
      exact Or.inr (Or.inl ⟨hwin_f, BucketActive_mono_rem hact (Nat.le_succ rem')⟩)
    · have hsafe_inj : es.g.safeInj (2 + Δcka) = true := by
        cases hsi : es.g.safeInj (2 + Δcka)
        · exfalso; apply hguard; simp [hsi]
        · rfl
      have hnot_tr : (es.g.inTransit P.other c).isSome = false := by
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard
        exact hguard.1.2
      rcases runPubIdeal_liftH_bind_support _ _ es rc σ hw with ⟨w_vr, hw_vr, hw_fin⟩
      rcases vRecv_bucket_step C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
          hq hΔb hk hfr_eq hsr_spec rem' P es rc σ hact c none
          (Or.inl hsafe_inj)
          w_vr hw_vr with hvr_none | ⟨hvr_rej, hact_rej⟩ |
        ⟨st', i', m', hvr_acc, htriv_target, hnoacc_inv, hacc_inv⟩
      · simp only [hvr_none, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
        subst hw_fin; exact Or.inl rfl
      · simp only [hvr_rej, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw_fin
        subst hw_fin; exact Or.inr (Or.inl ⟨hwin_f, hact_rej⟩)
      · simp only [hvr_acc] at hw_fin
        split at hw_fin
        case isTrue hcap =>
          simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw_fin
          subst hw_fin
          exact Or.inr (Or.inl ⟨hwin_f, hnoacc_inv rfl hnot_tr⟩)
        case isFalse hcap =>
          split at hw_fin
          case isTrue htriv =>
            unfold commitE at hw_fin
            rw [hcm_eq] at hw_fin
            dsimp only [hooksFSMultiDFBucketPaper, liftH] at hw_fin
            simp only [StateT.run_bind, runPubIdeal] at hw_fin
            subst hw_fin
            have hidem : { es.g.accept P st' ⟨P.other, c.1.1, i'⟩ with
                st := Function.update (es.g.accept P st' ⟨P.other, c.1.1, i'⟩).st P st' } =
                es.g.accept P st' ⟨P.other, c.1.1, i'⟩ := by
              cases es.g; simp [GameState.accept, Function.update_idem]
            rw [hidem]
            have hact' := hacc_inv ⟨P.other, c.1.1, i'⟩ rfl (Or.inl ⟨rfl, hnot_tr⟩)
            exact Or.inr (Or.inl ⟨hact'.2.1.hwin, hact'⟩)
          case isFalse htriv =>
            simp only [bucketAuthCfgGen] at hw_fin
            cases hbuck_c : inStage2BucketGen Δbucket tL par c.1.1 with
            | false =>
              simp only [hbuck_c, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, runPubIdeal,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin
              exact Or.inr (Or.inl ⟨hwin_f, hnoacc_inv rfl hnot_tr⟩)
            | true =>
              simp only [hbuck_c, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin
              refine Or.inr (Or.inr ⟨rfl, fun tWin htWin => ?_⟩)
              simp only [dfQueryTargetEpoch, Option.some.injEq] at htWin
              subst htWin
              cases hadm : lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 with
              | false => exact Or.inl rfl
              | true =>
                refine Or.inr ?_
                by_contra hnb
                exact htriv (htriv_target rfl hnot_tr ⟨hbuck_c, hadm, Nat.not_lt.mp hcap⟩ hnb)
  · -- 5. `corrEPaperBucket`
    rcases corrEPaperBucket_bucket_step C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
        hq hΔb hk hrv_spec rem' P es rc σ hact w hw with hab | hok
    · exact Or.inl hab
    · exact Or.inr (Or.inl hok)
  · -- 6. `deliverForgeE`
    change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((deliverForgeE hk (2 + Δcka) qep (bucketAuthCfgGen Δbucket tL par) ⟨P, c, c'⟩).run es) rc σ) at hw
    simp only [deliverForgeE,
      StateT.run_bind, StateT.run_get, pure_bind, habort_f, hwin_f, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte] at hw
    cases hit_c : es.g.inTransit P.other c with
    | none =>
      simp only [hit_c, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hw
      subst hw
      exact Or.inr (Or.inl ⟨hwin_f, BucketActive_mono_rem hact (Nat.le_succ rem')⟩)
    | some r_ref =>
      simp only [hit_c] at hw
      split_ifs at hw with hguard
      · simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw
        subst hw
        exact Or.inr (Or.inl ⟨hwin_f, BucketActive_mono_rem hact (Nat.le_succ rem')⟩)
      · have hr_ref_mem : r_ref ∈ es.g.trans := List.mem_of_find?_eq_some hit_c
        have hr_ref_pred := List.find?_some hit_c
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_ref_pred
        have hc_hdr_eq : c.1 = c'.1 := by
          by_contra hne; apply hguard; simp [hne]
        have hnot_tr' : (es.g.inTransit P.other c').isSome = false := by
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard
          exact hguard.1.1
        rcases runPubIdeal_liftH_bind_support _ _ es rc σ hw with ⟨w_vr, hw_vr, hw_fin⟩
        rcases vRecv_bucket_step C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
            hq hΔb hk hfr_eq hsr_spec rem' P es rc σ hact c' none
            (Or.inr ⟨r_ref, hr_ref_mem, (congrArg Prod.fst hr_ref_pred.2).trans hc_hdr_eq⟩)
            w_vr hw_vr with hvr_none | ⟨hvr_rej, hact_rej⟩ |
          ⟨st', i', m', hvr_acc, htriv_target, hnoacc_inv, hacc_inv⟩
        · simp only [hvr_none, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
          subst hw_fin; exact Or.inl rfl
        · simp only [hvr_rej, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw_fin
          subst hw_fin; exact Or.inr (Or.inl ⟨hwin_f, hact_rej⟩)
        · simp only [hvr_acc] at hw_fin
          split at hw_fin
          case isTrue hcap =>
            simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw_fin
            subst hw_fin
            exact Or.inr (Or.inl ⟨hwin_f, hnoacc_inv rfl hnot_tr'⟩)
          case isFalse hcap =>
            have hc'_le : c'.1.1 ≤ qep + 1 := by
              simp only [Bool.or_eq_true, not_or, decide_eq_true_eq] at hcap
              omega
            split at hw_fin
            case isTrue htriv =>
              unfold commitE at hw_fin
              rw [hcm_eq] at hw_fin
              dsimp only [hooksFSMultiDFBucketPaper, liftH] at hw_fin
              simp only [StateT.run_bind, runPubIdeal] at hw_fin
              subst hw_fin
              have hidem : { es.g.accept P st' ⟨P.other, c'.1.1, i'⟩ with
                  st := Function.update (es.g.accept P st' ⟨P.other, c'.1.1, i'⟩).st P st' } =
                  es.g.accept P st' ⟨P.other, c'.1.1, i'⟩ := by
                cases es.g; simp [GameState.accept, Function.update_idem]
              rw [hidem]
              have hact' := hacc_inv ⟨P.other, c'.1.1, i'⟩ rfl (Or.inl ⟨rfl, hnot_tr'⟩)
              exact Or.inr (Or.inl ⟨hact'.2.1.hwin, hact'⟩)
            case isFalse htriv =>
              simp only [bucketAuthCfgGen] at hw_fin
              cases hbuck_c : inStage2BucketGen Δbucket tL par c'.1.1 with
              | false =>
                simp only [hbuck_c, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, runPubIdeal,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                subst hw_fin
                exact Or.inr (Or.inl ⟨hwin_f, hnoacc_inv rfl hnot_tr'⟩)
              | true =>
                simp only [hbuck_c, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                  runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
                subst hw_fin
                refine Or.inr (Or.inr ⟨rfl, fun tWin htWin => ?_⟩)
                simp only [dfQueryTargetEpoch, Option.some.injEq] at htWin
                subst htWin
                cases hadm : lastLeakGuessAdmissible (2 + Δcka) tL c'.1.1 with
                | false => exact Or.inl rfl
                | true =>
                  refine Or.inr ?_
                  by_contra hnb
                  exact htriv (htriv_target rfl hnot_tr' ⟨hbuck_c, hadm, hc'_le⟩ hnb)

private theorem raw_frozen_on_abort_or_win
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hk : Hooks (FSMultiSpec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (qdf : (CryptoGames.SM.Construction.DeliverForge.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (es : BucketEState Pt ℓ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hfrozen : es.abort = true ∨ es.g.win = true)
    (w : _)
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((implEDFPaperBucketRaw hk (2 + Δcka) qep maxForwardJumps
        (bucketAuthCfgGen Δbucket tL par) (.inr qdf)).run es) rc σ)) :
    w.1.1.2 = es := by
  have hcond : (es.abort || es.g.win) = true := by
    rcases hfrozen with h | h <;> simp [h]
  rcases qdf with ((((⟨P, pm, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((transmitEBucket hk (2 + Δcka) qep ⟨P, pm, r⟩).run es) rc σ) at hw
    simp only [transmitEBucket,
      StateT.run_bind, StateT.run_get, pure_bind, hcond, ↓reduceIte, StateT.run_pure,
      runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw; rfl
  · change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((challEBucket ⟨P, m₀, m₁, r⟩).run es) rc σ) at hw
    simp only [challEBucket,
      StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw; rfl
  · change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((deliverE hk maxForwardJumps (bucketAuthCfgGen Δbucket tL par) ⟨P, c⟩).run es) rc σ) at hw
    simp only [deliverE,
      StateT.run_bind, StateT.run_get, pure_bind, hcond, ↓reduceIte, StateT.run_pure,
      runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw; rfl
  · change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((injectE hk (2 + Δcka) qep (bucketAuthCfgGen Δbucket tL par) ⟨P, c⟩).run es) rc σ) at hw
    simp only [injectE,
      StateT.run_bind, StateT.run_get, pure_bind] at hw
    have hg : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true := by
      simp [hcond]
    simp only [hg, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hw
    subst hw; rfl
  · change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((corrEPaperBucket hk P).run es) rc σ) at hw
    simp only [corrEPaperBucket,
      StateT.run_bind, StateT.run_get, pure_bind] at hw
    have hg : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true := by simp [hcond]
    simp only [hg, ↓reduceIte, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hw
    subst hw; rfl
  · change w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((deliverForgeE hk (2 + Δcka) qep (bucketAuthCfgGen Δbucket tL par) ⟨P, c, c'⟩).run es) rc σ) at hw
    simp only [deliverForgeE,
      StateT.run_bind, StateT.run_get, pure_bind, hcond, ↓reduceIte, StateT.run_pure,
      runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw; rfl

private theorem runPubIdeal_coinsE_support
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N n : ℕ)
    (es : BucketEState Pt ℓ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    {v : ((Fin (n + 1) × BucketEState Pt ℓ) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ))}
    (hv : v ∈ support (runPubIdeal C ℓ encT idOf N false ((coinsE n).run es) rc σ)) :
    v.1.1.2 = es ∧ v.1.2 = rc ∧ v.2 = σ := by
  simp only [coinsE, stateT_lift_run] at hv
  change v ∈ support (runPubIdeal C ℓ encT idOf N false
    (query (spec := PubMultiSpec Pt ℓ) (.inl n) >>= fun u => Pure.pure (u, es)) rc σ) at hv
  simp only [runPubIdeal, simulateQ_bind, pubMultiImpl, StateT.run_bind, stateT_lift_run,
    simulateQ_HasQuery_query, idealSessImpl, sessLift_inl, QueryImpl.liftTarget_apply,
    QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    simulateQ_pure, StateT.run_pure, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hv
  rcases hv with ⟨_, _, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

theorem implEDFPaperBucketMode_coins_bucketInv
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (rem : ℕ) (n : ℕ)
    (st : BucketEState Pt ℓ × Option ℕ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hinv : BucketInv q Δcka Δbucket qep tL par rem st σ)
    (w : _)
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((implEDFPaperBucketMode
        (hooksFSMultiDFBucketPaperMode (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep gMain tL par false)
        (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par)
        gMain isHonestHdrFSMultiDFBucket (.inl n)).run st) rc σ)) :
    BucketInv q Δcka Δbucket qep tL par rem w.1.1.2 w.2 := by
  rcases st with ⟨es, winEp⟩
  have hnw : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
  cases gMain with
  | true =>
    simp only [implEDFPaperBucketMode, withWinEpDFMode, ↓reduceIte, withWinEpDF,
      StateT.run_mk] at hw
    rcases runPubIdeal_bind_support_false _ _ rc σ hw with ⟨v, hv, hw'⟩
    have hv_eq := runPubIdeal_coinsE_support C ℓ encT idOf N n es rc σ hv
    rcases hv_eq with ⟨hve, hvrc, hvσ⟩
    rw [hve, hvrc, hvσ] at hw'
    simp only [hnw, Bool.false_eq_true, ↓reduceIte, runPubIdeal, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hw'
    subst hw'; exact hinv
  | false =>
    simp only [implEDFPaperBucketMode, withWinEpDFMode, Bool.false_eq_true, ↓reduceIte,
      StateT.run_mk] at hw
    rcases runPubIdeal_bind_support_false _ _ rc σ hw with ⟨v, hv, hw'⟩
    have hv_eq := runPubIdeal_coinsE_support C ℓ encT idOf N n es rc σ hv
    rcases hv_eq with ⟨hve, hvrc, hvσ⟩
    rw [hve, hvrc, hvσ] at hw'
    simp only [hnw, Bool.false_eq_true, ↓reduceIte, runPubIdeal, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hw'
    subst hw'; exact hinv

theorem implEDFPaperBucketMode_inr_bucketInv
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (hq : 1 ≤ q) (hΔb : 2 ≤ Δbucket) (rem' : ℕ)
    (qdf : (CryptoGames.SM.Construction.DeliverForge.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (st : BucketEState Pt ℓ × Option ℕ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hinv : BucketInv q Δcka Δbucket qep tL par (rem' + 1) st σ)
    (w : _)
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((implEDFPaperBucketMode
        (hooksFSMultiDFBucketPaperMode (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep gMain tL par false)
        (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par)
        gMain isHonestHdrFSMultiDFBucket (.inr qdf)).run st) rc σ)) :
    BucketInv q Δcka Δbucket qep tL par rem' w.1.1.2 w.2 := by
  rcases st with ⟨es, winEp⟩
  let hk := hooksFSMultiDFBucketPaperMode (q + 1) (dhScheme Dh)
    (CryptoGames.Ratchet.rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep gMain tL par false
  have hrv_spec : ∀ ctx P vp hs rc0 σ0 w0,
      w0 ∈ support (runPubIdeal C ℓ encT idOf N false ((hk.reveal ctx P vp).run hs) rc0 σ0) →
      (w0.1.1.1 = none) ∨
      w0 ∈ support (runPubIdeal C ℓ encT idOf N false
        (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).reveal
          ctx P vp).run hs) rc0 σ0) := by
    intro ctx P vp hs rc0 σ0 w0 hw0
    dsimp only [hk, hooksFSMultiDFBucketPaperMode] at hw0
    cases gMain with
    | true => exact Or.inr hw0
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hw0
      split_ifs at hw0
      · simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw0
        subst hw0; exact Or.inl rfl
      · exact Or.inr hw0
  have hraw_wrap : ∃ z ∈ support (runPubIdeal C ℓ encT idOf N false
        ((implEDFPaperBucketRaw hk (2 + Δcka) qep maxForwardJumps
          (bucketAuthCfgGen Δbucket tL par) (.inr qdf)).run es) rc σ),
      w.2 = z.2 ∧ w.1.1.2.1 = z.1.1.2 ∧
      ((!es.g.win && z.1.1.2.g.win) = false → w.1.1.2.2 = winEp) ∧
      (∀ tWin, (!es.g.win && z.1.1.2.g.win) = true → w.1.1.2.2 = some tWin →
        w.1.1.2.2 = winEp ∨
        dfQueryTargetEpoch (St := Fig8St Pt) (fun c : Fig8C Pt => c.1.1) (.inr qdf) = some tWin) := by
    cases gMain with
    | true =>
      simp only [implEDFPaperBucketMode, withWinEpDFMode, ↓reduceIte, withWinEpDF,
        StateT.run_mk] at hw
      rcases runPubIdeal_bind_support_false _ _ rc σ hw with ⟨z, hz, hwz⟩
      simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hwz
      subst hwz
      refine ⟨z, hz, rfl, rfl, fun hnw => by simp [hnw], fun tWin hw_t htWin => ?_⟩
      simp only [hw_t, ↓reduceIte] at htWin
      exact Or.inr htWin
    | false =>
      simp only [implEDFPaperBucketMode, withWinEpDFMode, Bool.false_eq_true, ↓reduceIte,
        StateT.run_mk] at hw
      rcases runPubIdeal_bind_support_false _ _ rc σ hw with ⟨z, hz, hwz⟩
      simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hwz
      subst hwz
      refine ⟨z, hz, rfl, rfl, fun hnw => by simp [hnw], fun tWin hw_t htWin => ?_⟩
      rcases qdf with ((((q1 | q2) | q3) | ⟨P_inj, c_inj⟩) | q5) | q6
      · dsimp only at ⊢; simp only [hw_t, ↓reduceIte]; exact Or.inl trivial
      · dsimp only at ⊢; simp only [hw_t, ↓reduceIte]; exact Or.inl trivial
      · dsimp only at ⊢; simp only [hw_t, ↓reduceIte]; exact Or.inl trivial
      · dsimp only at htWin ⊢
        simp only [hw_t, ↓reduceIte] at htWin ⊢
        split_ifs at htWin ⊢ with h_inj
        · exact Or.inr htWin
        · exact Or.inl rfl
      · dsimp only at ⊢; simp only [hw_t, ↓reduceIte]; exact Or.inl trivial
      · dsimp only at ⊢; simp only [hw_t, ↓reduceIte]; exact Or.inl trivial
  rcases hraw_wrap with ⟨z, hz, hw_σ, hw_es, hno_flip, hon_flip⟩
  rw [hw_σ]
  dsimp only [BucketInv, BucketWon, BucketActive] at hinv
  rcases hinv with hab | hwon | hact
  · have heq := raw_frozen_on_abort_or_win C ℓ encT idOf N Δcka Δbucket qep tL par hk qdf es rc σ
      (Or.inl hab) z hz
    exact Or.inl ((congrArg EState.abort hw_es).trans (heq.symm ▸ hab))
  · have heq := raw_frozen_on_abort_or_win C ℓ encT idOf N Δcka Δbucket qep tL par hk qdf es rc σ
      (Or.inr hwon.1) z hz
    have hnw : (!es.g.win && z.1.1.2.g.win) = false := by simp [hwon.1]
    have hpair : w.1.1.2 = (es, winEp) := Prod.ext (hw_es.trans heq) (hno_flip hnw)
    rw [hpair]
    exact Or.inr (Or.inl hwon)
  · have hwin_f : es.g.win = false := hact.2.1.hwin
    have hwinEp_none : winEp = none := hact.1
    rcases implEDFPaperBucketRaw_inr_step C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
        hq hΔb hk rfl rfl rfl rfl
        (fun t_recv P ctx γ σr Tn hs hlen =>
          startRecv_bucketMode_coinOnly C ℓ Dh encPt encT idOf q N Δcka Δbucket qep gMain tL par
            hq t_recv P ctx γ σr Tn hs hlen)
        hrv_spec rem' qdf es rc σ ⟨rfl, hact.2.1, hact.2.2⟩ z hz with hab' | ⟨hwin'_f, hact'⟩ | ⟨hwin'_t, hbad_win⟩
    · exact Or.inl ((congrArg EState.abort hw_es).trans hab')
    · have hnw : (!es.g.win && z.1.1.2.g.win) = false := by simp [hwin_f, hwin'_f]
      have hpair : w.1.1.2 = (z.1.1.2, none) := Prod.ext hw_es ((hno_flip hnw).trans hwinEp_none)
      rw [hpair]
      exact Or.inr (Or.inr hact')
    · have hw_t : (!es.g.win && z.1.1.2.g.win) = true := by simp [hwin_f, hwin'_t]
      refine Or.inr (Or.inl ⟨(congrArg (fun x => x.g.win) hw_es).trans hwin'_t, fun tWin htWin => ?_⟩)
      rw [hw_es]
      rcases hon_flip tWin hw_t htWin with hEq | htarget
      · rw [hwinEp_none] at hEq; rw [hEq] at htWin; cases htWin
      · exact hbad_win tWin htarget

/-- Un-split `implEDFPaperBucket` (`gMain = true`) corollary of `implEDFPaperBucketMode_*_bucketInv`. -/
theorem implEDFPaperBucket_step_bucketInv
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hq : 1 ≤ q) (hΔb : 2 ≤ Δbucket)
    (t_q : (unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (rem : ℕ) (st : BucketEState Pt ℓ × Option ℕ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : _)
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((implEDFPaperBucket
        (hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false)
        (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par) t_q).run st) rc σ)) :
    (∀ n, t_q = .inl n →
      BucketInv q Δcka Δbucket qep tL par rem st σ →
      BucketInv q Δcka Δbucket qep tL par rem w.1.1.2 w.2) ∧
    (∀ qdf rem', t_q = .inr qdf → rem = rem' + 1 →
      BucketInv q Δcka Δbucket qep tL par (rem' + 1) st σ →
      BucketInv q Δcka Δbucket qep tL par rem' w.1.1.2 w.2) := by
  constructor
  · intro n hn hinv
    subst hn
    rcases st with ⟨es, winEp⟩
    have hnw : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
    simp only [implEDFPaperBucket, withWinEpDF, StateT.run_mk] at hw
    rcases runPubIdeal_bind_support_false _ _ rc σ hw with ⟨v, hv, hw'⟩
    have hv_eq := runPubIdeal_coinsE_support C ℓ encT idOf N n es rc σ hv
    rcases hv_eq with ⟨hve, hvrc, hvσ⟩
    rw [hve, hvrc, hvσ] at hw'
    simp only [hnw, Bool.false_eq_true, ↓reduceIte, runPubIdeal, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hw'
    subst hw'; exact hinv
  · intro qdf rem' hqdf _ hinv
    subst hqdf
    rcases st with ⟨es, winEp⟩
    let hk := hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false
    simp only [implEDFPaperBucket, withWinEpDF, StateT.run_mk] at hw
    rcases runPubIdeal_bind_support_false _ _ rc σ hw with ⟨z, hz, hwz⟩
    simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hwz
    subst hwz
    dsimp only [BucketInv, BucketWon, BucketActive] at hinv
    rcases hinv with hab | hwon | hact
    · have heq := raw_frozen_on_abort_or_win C ℓ encT idOf N Δcka Δbucket qep tL par hk qdf es rc σ
        (Or.inl hab) z hz
      exact Or.inl (heq.symm ▸ hab)
    · have heq := raw_frozen_on_abort_or_win C ℓ encT idOf N Δcka Δbucket qep tL par hk qdf es rc σ
        (Or.inr hwon.1) z hz
      have hnw : (!es.g.win && es.g.win) = false := by simp [hwon.1]
      simp only [heq, hnw, Bool.false_eq_true, ↓reduceIte]
      exact Or.inr (Or.inl hwon)
    · have hwin_f : es.g.win = false := hact.2.1.hwin
      have hwinEp_none : winEp = none := hact.1
      rcases implEDFPaperBucketRaw_inr_step C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
          hq hΔb hk rfl rfl rfl rfl
          (fun t_recv P ctx γ σr Tn hs hlen =>
            startRecv_bucket_coinOnly C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
              hq t_recv P ctx γ σr Tn hs hlen)
          (fun _ _ _ _ _ _ _ h => Or.inr h)
          rem' qdf es rc σ ⟨rfl, hact.2.1, hact.2.2⟩ z hz with hab' | ⟨hwin'_f, hact'⟩ | ⟨hwin'_t, hbad_win⟩
      · exact Or.inl hab'
      · have hnw : (!es.g.win && z.1.1.2.g.win) = false := by simp [hwin_f, hwin'_f]
        simp only [hnw, Bool.false_eq_true, ↓reduceIte, hwinEp_none]
        exact Or.inr (Or.inr hact')
      · have hw_t : (!es.g.win && z.1.1.2.g.win) = true := by simp [hwin_f, hwin'_t]
        simp only [hw_t, ↓reduceIte]
        exact Or.inr (Or.inl ⟨hwin'_t, hbad_win⟩)

end BucketStep

end

end Computational.Proofs.E2E.SessionAuthMultiEndBucketStep

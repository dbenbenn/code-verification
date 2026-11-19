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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions

/-!
# `transmitEBucket` Step Preservation for `DeliverForgePaperMultiBucket`

Proves `transmitEBucket_bucket_step` (`la = false`, `1 ≤ q`, `2 ≤ Δbucket`).-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEndBucketTransmit

public section

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
  healedBy_of_leak tL_mem_of_leak EpochBad.of_sub_leaks block_eq_imp_epoch_eq EpochInv.record_ne)

/-! ## 3. `transmitEBucket` Step Preservation -/

private theorem liftH_bind_run {ι : Type} {tspec : _root_.OracleSpec.{0, 0} ι}
    {Γv T Sv SSv RSv M E HS α β : Type} (x : CryptoGames.SM.Engine.HM tspec HS α)
    (k : α → CryptoGames.SM.Engine.EM tspec Γv T Sv SSv RSv M E HS β)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (liftH x >>= k).run es =
      (x.run es.h >>= fun p =>
        pure (p.1, { es with h := p.2 }) >>= fun p_lift => (k p_lift.1).run p_lift.2) := by
  rw [StateT.run_bind]; exact bind_assoc _ _ _

private theorem record_ne_maxOpt {ℓ : ℕ}
    {q Δcka Δbucket qep : ℕ} {tL : Option ℕ} {par : Bool} {u t : ℕ}
    {P : Party} {es : BucketEState Pt ℓ}
    {s₁ : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {st' : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)}
    {pm : LibsignalMsgPublicPart × Plain ℓ} {c : Fig8C Pt}
    {hs' : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    {σ σ' : ℕ → Option (IdealHSt Pt ℓ)}
    (ht : IsTargetEpoch Δcka Δbucket qep tL par t) (hne_ut : u ≠ t)
    (hinv : EpochInv q Δcka tL t es σ)
    (hs₁_st : s₁.st = es.g.st) (hs₁_tr : s₁.trans = es.g.trans) (hs₁_cp : s₁.comp = es.g.comp)
    (hs₁_epP : s₁.epoch P = u) (hs₁_epQ : ∀ Q, Q ≠ P → s₁.epoch Q = es.g.epoch Q)
    (hs₁_ep_mono : ∀ Q, es.g.epoch Q ≤ s₁.epoch Q) (hs₁_ep_le_succ : s₁.epoch P ≤ es.g.epoch P + 1)
    (hs₁_idxQ : ∀ Q, Q ≠ P → s₁.idx Q = es.g.idx Q)
    (hs₁_leak_cases :
      (s₁.leaks = es.g.leaks ∧ s₁.tL = es.g.tL) ∨
      (s₁.leaks = maxOpt es.g.tL u :: es.g.leaks ∧ s₁.tL = some (maxOpt es.g.tL u)))
    (hvR' : st'.vR = (es.g.st P).vR)
    (hvS'_blk : ∀ sIdx, sIdx / q = t - healEpoch tL → st'.vS ≠ some (.inr sIdx))
    (hc_t : hs'.cache t = es.h.cache t)
    (hσ_t : ∀ sIdx, sIdx / q = t - healEpoch tL → σ' sIdx = σ sIdx) :
    EpochInv q Δcka tL t
      { es with
          g := s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, pm, c⟩ false
          h := hs' } σ' := by
  have hne_ep : s₁.epoch P ≠ t := hs₁_epP ▸ hne_ut
  have hleaks_sub : ∀ lk ∈ es.g.leaks, lk ∈ s₁.leaks := by
    intro lk hlk; rcases hs₁_leak_cases with ⟨hL, _⟩ | ⟨hL, _⟩ <;> rw [hL]
    · exact hlk
    · exact List.mem_cons_of_mem _ hlk
  have hs₁_heal : healedBy s₁.tL (2 + Δcka) t = true → healedBy es.g.tL (2 + Δcka) t = true := by
    rcases hs₁_leak_cases with ⟨_, htL_eq⟩ | ⟨_, htL_eq⟩
    · rw [htL_eq]; exact id
    · rw [htL_eq]; exact fun hh => healedBy_of_leak es.g u (2 + Δcka) t hh
  rcases hinv with hbad | hcomp | hpre | ⟨s₀, hidl⟩
  · exact Or.inl (EpochBad.of_sub_leaks hbad fun lk hlk => by simp [GameState.record, hleaks_sub lk hlk])
  · refine Or.inr (Or.inl ⟨by simp only [GameState.record]; exact le_trans hcomp.1 (hs₁_ep_mono _), ?_, ?_, ?_, ?_,
      by simpa only [hc_t] using hcomp.2.2.2.2.2⟩)
    · rcases hcomp.2.1 with ⟨cur0, hcur0, hle0⟩
      rcases hs₁_leak_cases with ⟨_, htL_eq⟩ | ⟨_, htL_eq⟩
      · exact ⟨cur0, by simp [GameState.record, htL_eq, hcur0], hle0⟩
      · exact ⟨max cur0 u, by simp [GameState.record, htL_eq, maxOpt, hcur0], le_trans hle0 (Nat.le_max_left _ _)⟩
    · intro r0 hr0 hep0; simp only [GameState.record, List.mem_cons] at hr0
      rcases hr0 with rfl | hr_old
      · exact (hne_ep hep0).elim
      · have hc_old := hcomp.2.2.1 r0 (hs₁_tr ▸ hr_old) hep0
        simp only [GameState.record, hs₁_cp]; split_ifs <;> simp [hc_old]
    · intro Q sIdx hblk hvS; by_cases hQ : Q = P
      · rw [hQ] at hvS; simp only [GameState.record, Function.update_self] at hvS; exact hvS'_blk sIdx hblk hvS
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS; exact hcomp.2.2.2.1 Q sIdx hblk hvS
    · intro Q sIdx; by_cases hQ : Q = P
      · rw [hQ]; simp only [GameState.record, Function.update_self, hvR']; exact hcomp.2.2.2.2.1 P sIdx
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st]; exact hcomp.2.2.2.2.1 Q sIdx
  · have hu_lt_t : u < t := by have := hpre.1 P; omega
    have hep'_lt : ∀ Q, (s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, pm, c⟩ false).epoch Q < t := by
      intro Q; simp only [GameState.record]; by_cases hQ : Q = P
      · rw [hQ, hs₁_epP]; exact hu_lt_t
      · rw [hs₁_epQ Q hQ]; exact hpre.1 Q
    have hvR'_none : ∀ Q, ((s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, pm, c⟩ false).st Q).vR t = none := by
      intro Q; by_cases hQ : Q = P
      · rw [hQ]; simp [GameState.record, hvR', hpre.2.2.2.1 P]
      · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hpre.2.2.2.1 Q]
    have hvS'_ne : ∀ Q sIdx, sIdx / q = t - healEpoch tL →
        ((s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, pm, c⟩ false).st Q).vS ≠ some (.inr sIdx) := by
      intro Q sIdx hblk hvS; by_cases hQ : Q = P
      · rw [hQ] at hvS; simp only [GameState.record, Function.update_self] at hvS; exact hvS'_blk sIdx hblk hvS
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS; exact hpre.2.2.2.2.1 Q sIdx hblk hvS
    have hσ'_clean : ∀ sIdx st, sIdx / q = t - healEpoch tL → σ' sIdx = some st →
        st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧ st.1.inTransit = [] ∧ st.1.lastSentIdx = 0 :=
      fun sIdx st hblk hst => hpre.2.2.2.2.2.2 sIdx st hblk ((hσ_t sIdx hblk) ▸ hst)
    rcases hs₁_leak_cases with ⟨_, htL_eq⟩ | ⟨hL_eq, htL_eq⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hep'_lt, by simpa only [GameState.record, htL_eq] using hpre.2.1,
        by simpa only [postLeakDFBucket, GameState.record, htL_eq] using hpre.2.2.1,
        hvR'_none, hvS'_ne, hc_t.trans hpre.2.2.2.2.2.1, hσ'_clean⟩))
    · cases hlt_u : ltOpt tL u with
      | true =>
        have hle_max : u ≤ maxOpt es.g.tL u := by
          cases es.g.tL with
          | none => exact le_rfl
          | some _ => exact Nat.le_max_right _ _
        refine Or.inl ⟨maxOpt es.g.tL u, by simp [GameState.record, hL_eq], ?_, ?_⟩
        · cases tL with
          | none => rfl
          | some l =>
            simp only [ltOpt, decide_eq_true_eq] at hlt_u ⊢
            exact lt_of_lt_of_le hlt_u hle_max
        · cases htL_es : es.g.tL with
          | none => simpa [maxOpt] using hu_lt_t
          | some cur0 => have := hpre.2.1 cur0 htL_es; simp only [maxOpt]; omega
      | false =>
        refine Or.inr (Or.inr (Or.inl ⟨hep'_lt, ?_, ?_, hvR'_none, hvS'_ne, hc_t.trans hpre.2.2.2.2.2.1, hσ'_clean⟩))
        · intro cur' hcur'; simp only [GameState.record, htL_eq, Option.some.injEq] at hcur'; subst hcur'
          cases htL_es : es.g.tL with
          | none => simpa [maxOpt] using hu_lt_t
          | some cur0 => have := hpre.2.1 cur0 htL_es; simp only [maxOpt]; omega
        · cases tL with
          | none => simp [ltOpt] at hlt_u
          | some l =>
            simp only [ltOpt, decide_eq_false_iff_not, not_lt] at hlt_u
            cases htL_es : es.g.tL with
            | none => simp [postLeakDFBucket, GameState.record, htL_eq, htL_es, maxOpt, ltOpt, Nat.not_lt.mpr hlt_u]
            | some cur0 =>
              have hpl0 := hpre.2.2.1
              simp only [postLeakDFBucket, htL_es, ltOpt, decide_eq_false_iff_not, not_lt] at hpl0
              simp only [postLeakDFBucket, GameState.record, htL_eq, htL_es, maxOpt, ltOpt, decide_eq_false_iff_not, not_lt]
              omega
  · rcases hidl with ⟨hdiv, hep, hct_idx, hvS_eq, hvS_all, hunused, hnone_tr, hsome, hvR, hvR_ge, hpin⟩
    have hs₀_eq : σ' s₀ = σ s₀ := hσ_t s₀ hdiv
    refine Or.inr (Or.inr (Or.inr ⟨s₀, hdiv, by simp only [GameState.record]; exact le_trans hep (hs₁_ep_mono _),
      ?_, ?_, ?_, fun sIdx st hblk hne hst => hunused sIdx st hblk hne ((hσ_t sIdx hblk) ▸ hst), ?_, ?_, ?_, ?_, ?_⟩))
    · intro r0 hr0 hep0; simp only [GameState.record, List.mem_cons] at hr0
      rcases hr0 with rfl | hr_old
      · exact (hne_ep hep0).elim
      · exact hct_idx r0 (hs₁_tr ▸ hr_old) hep0
    · intro hep_rec; simp only [GameState.record] at hep_rec
      by_cases hS : Party.senderOf t = P
      · exfalso; rw [hS] at hep_rec; exact hne_ep hep_rec
      · simp only [GameState.record, Function.update_of_ne hS, hs₁_st]
        rw [hs₁_epQ _ hS] at hep_rec; exact hvS_eq hep_rec
    · intro Q sIdx hblk hvS; by_cases hQ : Q = P
      · rw [hQ] at hvS; simp only [GameState.record, Function.update_self] at hvS; exact (hvS'_blk sIdx hblk hvS).elim
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
        rcases hvS_all Q sIdx hblk hvS with ⟨rfl, rfl, hsends⟩
        refine ⟨rfl, rfl, fun hsIn => ?_⟩
        simp only [GameState.record, Function.update_of_ne hQ, hs₁_epQ _ hQ, hs₁_idxQ _ hQ, hs₀_eq] at hsIn ⊢
        exact hsends hsIn
    · intro hnone r0 hr0 hep0; simp only [GameState.record, List.mem_cons] at hr0
      rcases hr0 with rfl | hr_old
      · exact hne_ep hep0
      · exact hnone_tr (hs₀_eq ▸ hnone) r0 (hs₁_tr ▸ hr_old) hep0
    · intro st hst; have h5 := hsome st (hs₀_eq ▸ hst)
      refine ⟨h5.1, h5.2.1, ?_, ?_, ?_⟩
      · intro r0 hr0 hep0; simp only [GameState.record, List.mem_cons] at hr0
        rcases hr0 with rfl | hr_old
        · exact (hne_ep hep0).elim
        · exact h5.2.2.1 r0 (hs₁_tr ▸ hr_old) hep0
      · intro hheal_g'; simp only [GameState.record] at hheal_g'
        rcases h5.2.2.2.1 (hs₁_heal hheal_g') with ⟨hsc0, htr0⟩
        refine ⟨hsc0, fun r_fs hr_fs => ?_⟩
        rcases htr0 r_fs hr_fs with ⟨m0, hm0⟩
        exact ⟨m0, by simp [GameState.record, hs₁_tr, hm0]⟩
      · intro r0 hr0 hep0 hnc0; simp only [GameState.record, List.mem_cons] at hr0
        rcases hr0 with rfl | hr_old
        · exact (hne_ep hep0).elim
        · have hnc_old : r0.pos ∉ es.g.comp := fun hc => hnc0 (by simp only [GameState.record, hs₁_cp]; split_ifs <;> simp [hc])
          exact h5.2.2.2.2 r0 (hs₁_tr ▸ hr_old) hep0 hnc_old
    · intro Q v0 hv0; by_cases hQ : Q = P
      · rw [hQ] at hv0; simp only [GameState.record, Function.update_self, hvR'] at hv0; exact hvR P v0 hv0
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hv0; exact hvR Q v0 hv0
    · intro hle_rec; simp only [GameState.record] at hle_rec
      by_cases hR : Party.receiverOf t = P
      · have hle_old : t ≤ es.g.epoch P := by have h1 : t ≤ s₁.epoch P := hR ▸ hle_rec; omega
        simpa [GameState.record, hR, hvR'] using hvR_ge (hR.symm ▸ hle_old)
      · simpa [GameState.record, Function.update_of_ne hR, hs₁_st] using hvR_ge ((hs₁_epQ _ hR) ▸ hle_rec)
    · intro ht_pos; rcases hpin ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
      refine ⟨Tc, σc, k, hc_t ▸ hc_Tc, ?_, ?_⟩
      · intro hep_rec; simp only [GameState.record] at hep_rec
        by_cases hS : Party.senderOf t = P
        · exfalso; rw [hS] at hep_rec; exact hne_ep hep_rec
        · simp only [GameState.record, Function.update_of_ne hS, hs₁_st]
          rw [hs₁_epQ _ hS] at hep_rec; exact hcur_Tc hep_rec
      · intro r0 hr0 hep0; simp only [GameState.record, List.mem_cons] at hr0
        rcases hr0 with rfl | hr_old
        · exact (hne_ep hep0).elim
        · exact htr_Tc r0 (hs₁_tr ▸ hr_old) hep0

theorem transmitEBucket_bucket_step
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
    (rem' : ℕ) (P : Party) (pm : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (es : BucketEState Pt ℓ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hact : BucketActive q Δcka Δbucket qep tL par (rem' + 1) (es, none) σ)
    (w : ((Option (Fig8C Pt) × BucketEState Pt ℓ) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((transmitEBucket hk (2 + Δcka) qep ⟨P, pm, r⟩).run es) rc σ)) :
    w.1.1.2.abort = true ∨
    (w.1.1.2.g.win = false ∧ BucketActive q Δcka Δbucket qep tL par rem' (w.1.1.2, none) w.2) := by
  dsimp only [BucketActive] at hact
  rcases hact with ⟨_, hwf, hep_inv⟩
  simp only [transmitEBucket, StateT.run_bind, StateT.run_get, pure_bind,
    hwf.habort, hwf.hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hw
  cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
  | none =>
    simp only [hep, StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hw
    subst hw
    exact Or.inr ⟨hwf.hwin, rfl, GlobalBucketWF_mono_rem hwf (Nat.le_succ rem'), hep_inv⟩
  | some s₁ =>
    simp only [hep] at hw
    unfold GameState.epMgmt at hep
    by_cases hsIn1 : P.sendsIn (es.g.epoch P + 1) = true
    · -- Case T1: `P` advances to new sending epoch `u := es.g.epoch P + 1`.
      simp only [hsIn1, ↓reduceIte] at hep
      generalize hu_eq : es.g.epoch P + 1 = u at hep hsIn1
      have hu_def : u = es.g.epoch P + 1 := hu_eq.symm
      have hu_pos : 1 ≤ u := by omega
      have hP_sender : P = Party.senderOf u := by
        cases P <;> simp [Party.senderOf, Party.sendsIn] at hsIn1 ⊢ <;> exact hsIn1
      have hu_le_qep0 : u ≤ qep := by
        by_contra hgt
        have hlt : qep < u := by omega
        simp only [hlt, ↓reduceIte] at hep
        cases hep
      have hu_le_qep : u ≤ qep + 1 := Nat.le_succ_of_le hu_le_qep0
      have hs₁_def : s₁ =
          if r.isSome && !(es.g.safeCh (2 + Δcka) P) then
            { es.g.leak u with epoch := Function.update (es.g.leak u).epoch P u,
                               idx := Function.update (es.g.leak u).idx P 0 }
          else
            { es.g with epoch := Function.update es.g.epoch P u,
                        idx := Function.update es.g.idx P 0 } := by
        have hnot_lt : ¬ qep < u := by omega
        simp only [hnot_lt] at hep
        by_cases hc : (r.isSome && !es.g.safeCh (2 + Δcka) P) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at hep ⊢
          simpa [GameState.leak, ← hu_def] using hep.symm
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hep ⊢
          simpa [← hu_def] using hep.symm
      have hs₁_st : s₁.st = es.g.st := by subst hs₁_def; split_ifs <;> rfl
      have hs₁_tr : s₁.trans = es.g.trans := by subst hs₁_def; split_ifs <;> rfl
      have hs₁_cp : s₁.comp = es.g.comp := by subst hs₁_def; split_ifs <;> rfl
      have hs₁_win : s₁.win = false := by subst hs₁_def; split_ifs <;> exact hwf.hwin
      have hs₁_epP : s₁.epoch P = u := by subst hs₁_def; split_ifs <;> simp [GameState.leak]
      have hs₁_epQ : ∀ Q, Q ≠ P → s₁.epoch Q = es.g.epoch Q := by
        intro Q hQ; subst hs₁_def; split_ifs <;> simp [GameState.leak, Function.update_of_ne hQ]
      have hs₁_ep_mono : ∀ Q, es.g.epoch Q ≤ s₁.epoch Q := by
        intro Q; by_cases hQ : Q = P
        · rw [hQ, hs₁_epP]; omega
        · rw [hs₁_epQ Q hQ]
      have hs₁_idxP : s₁.idx P = 0 := by subst hs₁_def; split_ifs <;> simp [GameState.leak]
      have hs₁_idxQ : ∀ Q, Q ≠ P → s₁.idx Q = es.g.idx Q := by
        intro Q hQ; subst hs₁_def; split_ifs <;> simp [GameState.leak, Function.update_of_ne hQ]
      have hs₁_tL_mem : ∀ cur, s₁.tL = some cur → cur ∈ s₁.leaks := by
        subst hs₁_def
        split_ifs
        · exact tL_mem_of_leak u hwf.htL_mem
        · exact hwf.htL_mem
      have hs₁_leak_cases :
          (s₁.leaks = es.g.leaks ∧ s₁.tL = es.g.tL) ∨
          (s₁.leaks = maxOpt es.g.tL u :: es.g.leaks ∧ s₁.tL = some (maxOpt es.g.tL u)) := by
        subst hs₁_def
        split_ifs
        · dsimp only [GameState.leak]; exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
      have hlen_u : (es.h.sessions u).length < q := by
        have := hwf.hsess_pos u hu_pos; omega
      rw [liftH_bind_run] at hw
      rcases runPubIdeal_bind_support_false _ _ rc σ hw with ⟨w_v, hw_v, hw_fin⟩
      dsimp only [runPubIdeal] at hw_fin
      unfold vSend at hw_v
      rw [hss_eq, hfs_eq] at hw_v
      simp only [hs₁_st, hwf.hid P, hwf.htcur P, ← hu_def, hsIn1, ↓reduceIte,
        StateT.run_bind] at hw_v
      rcases runPubIdeal_bind_support_false _ _ rc σ hw_v with ⟨w_ss, hw_ss, hw_fs⟩
      dsimp only [runPubIdeal] at hw_fs
      rcases startSend_bucket_coinOnly C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
          hq u P s₁ (es.g.st P).γ (es.g.st P).root r es.h hlen_u rc σ w_ss hw_ss with
        ⟨⟨γ', T', σr', ssv, hss_ok, hbk_ss, hse_u_ss, hse_ne_ss, hc_ne_ss, hss_branch⟩, hrc_ss, hσ_ss⟩
      rw [hrc_ss, hσ_ss] at hw_fs
      simp only [hss_ok, pure_bind] at hw_fs
      rcases hss_branch with ⟨hpl_f, _, hbuck_u, s₀, k_u, rfl, hdiv_s₀, hc_u_ss⟩ |
        ⟨hnot_buck, ⟨ss_inl, rfl⟩, k_u, hc_u_ss⟩
      · -- Branch T1a: `ssv = .inr s₀` (`postLeakDFBucket tL s₁ = false`, `inStage2BucketGen ... u = true`).
        by_cases htarget_u : IsTargetEpoch Δcka Δbucket qep tL par u ∧ ¬ EpochBad tL u s₁
        · -- Subcase T1a-1: `u` is a clean target epoch (`EpochPre` -> `EpochIdealAt`).
          rcases htarget_u with ⟨ht_u, hnot_bad_s₁⟩
          have hnot_bad_es : ¬ EpochBad tL u es.g := fun hb =>
            hnot_bad_s₁ (EpochBad.of_sub_leaks hb fun lk hlk => by
              rcases hs₁_leak_cases with ⟨hL, _⟩ | ⟨hL, _⟩ <;> [rw [hL]; rw [hL]]
              · exact hlk
              · exact List.mem_cons_of_mem _ hlk)
          have hpre_u : EpochPre q tL u es σ := by
            rcases hep_inv u ht_u with hbad | hcomp | hpre | ⟨_, hidl⟩
            · exact (hnot_bad_es hbad).elim
            · exfalso; have := hcomp.1; rw [← hP_sender] at this; omega
            · exact hpre
            · exfalso; have := hidl.2.1; rw [← hP_sender] at this; omega
          have hno_u_tr : ∀ r0 ∈ s₁.trans, r0.pos.epoch ≠ u := by
            intro r0 hr0 hep0
            rw [hs₁_tr] at hr0
            have hle := (hwf.htrans_wf r0 hr0).2.2.1
            have := hpre_u.1 r0.pos.sender
            omega
          simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hw_fs
          rcases hw_fs with ⟨w_sd, hw_sd, hw_ret⟩
          rcases fsSend_inr_bucket_step_post C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
              u s₀ s₁ (u, some T') pm w_ss.1.1.2 rc σ
              (hP_sender ▸ hs₁_epP)
              (by
                cases hσ0 : σ s₀ with
                | none => exact Or.inl ⟨rfl, hP_sender ▸ hs₁_idxP, hno_u_tr⟩
                | some st₀ =>
                  rcases hpre_u.2.2.2.2.2.2 s₀ st₀ hdiv_s₀ hσ0 with ⟨he, hsc, hit, hls⟩
                  exact Or.inr ⟨st₀, rfl, he, hls.trans (hP_sender ▸ hs₁_idxP).symm,
                    by simp [hit], fun r0 hr0 hep0 => (hno_u_tr r0 hr0 hep0).elim,
                    fun _ => ⟨hsc, by simp [hit]⟩,
                    fun r0 hr0 hep0 _ => (hno_u_tr r0 hr0 hep0).elim⟩)
              w_sd
              (by convert hw_sd using 5; exact hP_sender.symm) with hsd_none |
            ⟨rawCt, st₂, hsd_ok, hc_sd, hse_sd, hσ_upd, hend₂, hls₂, hit₂, hrec₂⟩
          · simp only [hsd_none, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw_ret
            subst hw_ret
            simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
            subst hw_fin; exact Or.inl rfl
          · simp only [hsd_ok, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw_ret
            subst hw_ret
            simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
            subst hw_fin
            dsimp only
            subst hP_sender
            rcases hrec₂ _ with ⟨hrec_idx, hrec_heal, hrec_unc⟩
            refine Or.inr ⟨hs₁_win, rfl, ?_, ?_⟩
            · refine {
                habort := hwf.habort
                hwin := hs₁_win
                hid := fun Q => by
                  by_cases hQ : Q = Party.senderOf u
                  · rw [hQ]; simp [GameState.record]
                  · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hwf.hid Q]
                htcur := fun Q => by
                  by_cases hQ : Q = Party.senderOf u
                  · rw [hQ]; simp [GameState.record, hs₁_epP]
                  · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hs₁_epQ Q hQ, hwf.htcur Q]
                htL_mem := hs₁_tL_mem
                hsess_zero := fun ik hik => by
                  rw [hse_sd, hse_ne_ss 0 (by omega)] at hik ⊢
                  exact hwf.hsess_zero ik hik
                hsess_pos := fun u' hu' => by
                  rw [hse_sd]
                  by_cases hEq : u' = u
                  · subst u'; have := hwf.hsess_pos u hu_pos; omega
                  · rw [hse_ne_ss u' hEq]; have := hwf.hsess_pos u' hu'; omega
                hcache_blk := fun u' Tc σc k sIdx hc => by
                  rw [hc_sd] at hc
                  by_cases hEq : u' = u
                  · subst u'; rw [hc_u_ss] at hc
                    injection hc with hquad
                    rcases Prod.mk.inj hquad with ⟨_, hrest⟩
                    rcases Prod.mk.inj hrest with ⟨_, hrest2⟩
                    rcases Prod.mk.inj hrest2 with ⟨_, hsIdx⟩
                    injection hsIdx with hsIdx_eq; subst hsIdx_eq
                    exact ⟨hu_pos, hbuck_u, hu_le_qep, hdiv_s₀⟩
                  · rw [hc_ne_ss u' hEq] at hc
                    exact hwf.hcache_blk u' Tc σc k sIdx hc
                hvR_blk := fun Q u' sIdx hvR => by
                  by_cases hQ : Q = Party.senderOf u
                  · rw [hQ] at hvR; simp only [GameState.record, Function.update_self] at hvR
                    exact hwf.hvR_blk _ u' sIdx hvR
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvR
                    exact hwf.hvR_blk Q u' sIdx hvR
                hvS_blk := fun Q sIdx hvS => by
                  by_cases hQ : Q = Party.senderOf u
                  · rw [hQ] at hvS ⊢
                    simp only [GameState.record, Function.update_self, Option.some.injEq,
                      Sum.inr.injEq] at hvS
                    subst hvS
                    exact ⟨u, by simp [GameState.record, hs₁_epP], fun _ => by simp [GameState.record, hs₁_epP],
                      rfl, hbuck_u, hu_le_qep, hdiv_s₀⟩
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
                    rcases hwf.hvS_blk Q sIdx hvS with ⟨u0, hle0, hs0, hP0, hb0, hq0, hd0⟩
                    exact ⟨u0, by simpa [GameState.record, hs₁_epQ Q hQ] using hle0,
                      by simpa [GameState.record, hs₁_epQ Q hQ] using hs0, hP0, hb0, hq0, hd0⟩
                htrans_wf := fun r0 hr0 => by
                  simp only [GameState.record, List.mem_cons] at hr0
                  rcases hr0 with rfl | hr_old
                  · exact ⟨hs₁_epP, by rw [hs₁_epP], le_rfl, fun _ => by simp [GameState.record]⟩
                  · rw [hs₁_tr] at hr_old
                    rcases hwf.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4⟩
                    refine ⟨h1, h2, le_trans h3 (hs₁_ep_mono _), ?_⟩
                    by_cases hS : r0.pos.sender = Party.senderOf u
                    · intro hEq; exfalso
                      simp only [GameState.record, hS, hs₁_epP] at hEq
                      rw [hS] at h3; omega
                    · simpa [GameState.record, Function.update_of_ne hS, hs₁_epQ _ hS, hs₁_idxQ _ hS] using h4
              }
            · intro t ht
              by_cases heq_ut : u = t
              · subst heq_ut
                rw [hσ_upd]
                refine Or.inr (Or.inr (Or.inr ⟨s₀, hdiv_s₀,
                  by simp [GameState.record, hs₁_epP], ?_,
                  fun _ => by simp [GameState.record], ?_, ?_,
                  by intro h; simp at h, ?_, ?_, ?_, ?_⟩))
                · intro r0 hr0 hep0
                  simp only [GameState.record, List.mem_cons] at hr0
                  rcases hr0 with rfl | hr_old
                  · rfl
                  · exact (hno_u_tr r0 hr_old hep0).elim
                · intro Q idx hblkQ hvSQ
                  by_cases hQ : Q = Party.senderOf u
                  · rw [hQ] at hvSQ ⊢
                    simp only [GameState.record, Function.update_self, Option.some.injEq,
                      Sum.inr.injEq] at hvSQ
                    subst hvSQ
                    refine ⟨rfl, rfl, fun _ => ⟨by simp [GameState.record, hs₁_epP],
                      Or.inr ⟨st₂, by simp, ?_⟩⟩⟩
                    simp [GameState.record, hls₂]
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvSQ
                    exact (hpre_u.2.2.2.2.1 Q idx hblkQ hvSQ).elim
                · intro idx st hblk_i hne_i hst_i
                  rw [Function.update_of_ne hne_i] at hst_i
                  exact hpre_u.2.2.2.2.2.2 idx st hblk_i hst_i
                · intro st hst
                  simp only [Function.update_self, Option.some.injEq] at hst; subst hst
                  simp only [hs₁_epP] at hrec_idx hrec_heal hrec_unc ⊢
                  exact ⟨hend₂, hit₂, hrec_idx, hrec_heal, hrec_unc⟩
                · intro Q v0 hv0
                  by_cases hQ : Q = Party.senderOf u
                  · rw [hQ] at hv0; simp only [GameState.record, Function.update_self] at hv0
                    rw [hpre_u.2.2.2.1] at hv0; cases hv0
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hv0
                    rw [hpre_u.2.2.2.1 Q] at hv0; cases hv0
                · intro hle_rec
                  exfalso
                  have hne_rs : Party.receiverOf u ≠ Party.senderOf u := by
                    cases h : Party.senderOf u <;> simp [Party.receiverOf, Party.other, h]
                  simp only [GameState.record, hs₁_epQ _ hne_rs] at hle_rec
                  have := hpre_u.1 (Party.receiverOf u)
                  omega
                · intro _
                  refine ⟨T', σr', k_u, hc_sd ▸ hc_u_ss, fun _ => by simp [GameState.record], ?_⟩
                  intro r0 hr0 hep0
                  simp only [GameState.record, List.mem_cons] at hr0
                  rcases hr0 with rfl | hr_old
                  · rfl
                  · exact (hno_u_tr r0 hr_old hep0).elim
              · refine record_ne_maxOpt ht heq_ut (hep_inv t ht) hs₁_st hs₁_tr hs₁_cp
                  hs₁_epP hs₁_epQ hs₁_ep_mono (by rw [hs₁_epP]; omega) hs₁_idxQ hs₁_leak_cases rfl ?_ ?_ ?_
                · intro sIdx hblk_t hvS
                  simp only [Option.some.injEq, Sum.inr.injEq] at hvS; subst hvS
                  exact heq_ut (block_eq_imp_epoch_eq hΔb hbuck_u ht.1 hdiv_s₀ hblk_t)
                · exact (congrFun hc_sd t).trans (hc_ne_ss t (Ne.symm heq_ut))
                · intro sIdx hblk_t
                  rw [hσ_upd]
                  have hne_s : sIdx ≠ s₀ := fun hEq_s =>
                    heq_ut (block_eq_imp_epoch_eq hΔb hbuck_u ht.1 hdiv_s₀ (hEq_s ▸ hblk_t))
                  exact Function.update_of_ne hne_s _ _
        · -- Subcase T1a-2: `¬ (IsTargetEpoch ... u ∧ ¬ EpochBad tL u s₁)` — use `fsSend_inr_bucket_any_support`.
          simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hw_fs
          rcases hw_fs with ⟨w_sd, hw_sd, hw_ret⟩
          rcases fsSend_inr_bucket_any_support C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
              P u s₀ s₁ (u, some T') pm w_ss.1.1.2 rc σ w_sd hw_sd with
            ⟨hc_sd, hse_sd, hσ_ne, hsd_none | ⟨e_out, hsd_ok⟩⟩
          · simp only [hsd_none, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw_ret
            subst hw_ret
            simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
            subst hw_fin; exact Or.inl rfl
          · simp only [hsd_ok, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw_ret
            subst hw_ret
            simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
            subst hw_fin
            dsimp only
            refine Or.inr ⟨hs₁_win, rfl, ?_, ?_⟩
            · refine {
                habort := hwf.habort
                hwin := hs₁_win
                hid := fun Q => by
                  by_cases hQ : Q = P
                  · rw [hQ]; simp [GameState.record]
                  · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hwf.hid Q]
                htcur := fun Q => by
                  by_cases hQ : Q = P
                  · rw [hQ]; simp [GameState.record, hs₁_epP]
                  · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hs₁_epQ Q hQ, hwf.htcur Q]
                htL_mem := hs₁_tL_mem
                hsess_zero := fun ik hik => by
                  rw [hse_sd, hse_ne_ss 0 (by omega)] at hik ⊢
                  exact hwf.hsess_zero ik hik
                hsess_pos := fun u' hu' => by
                  rw [hse_sd]
                  by_cases hEq : u' = u
                  · subst u'; have := hwf.hsess_pos u hu_pos; omega
                  · rw [hse_ne_ss u' hEq]; have := hwf.hsess_pos u' hu'; omega
                hcache_blk := fun u' Tc σc k sIdx hc => by
                  rw [hc_sd] at hc
                  by_cases hEq : u' = u
                  · subst u'; rw [hc_u_ss] at hc
                    injection hc with hquad
                    rcases Prod.mk.inj hquad with ⟨_, hrest⟩
                    rcases Prod.mk.inj hrest with ⟨_, hrest2⟩
                    rcases Prod.mk.inj hrest2 with ⟨_, hsIdx⟩
                    injection hsIdx with hsIdx_eq; subst hsIdx_eq
                    exact ⟨hu_pos, hbuck_u, hu_le_qep, hdiv_s₀⟩
                  · rw [hc_ne_ss u' hEq] at hc
                    exact hwf.hcache_blk u' Tc σc k sIdx hc
                hvR_blk := fun Q u' sIdx hvR => by
                  by_cases hQ : Q = P
                  · rw [hQ] at hvR; simp only [GameState.record, Function.update_self] at hvR
                    exact hwf.hvR_blk P u' sIdx hvR
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvR
                    exact hwf.hvR_blk Q u' sIdx hvR
                hvS_blk := fun Q sIdx hvS => by
                  by_cases hQ : Q = P
                  · rw [hQ] at hvS ⊢
                    simp only [GameState.record, Function.update_self, Option.some.injEq,
                      Sum.inr.injEq] at hvS
                    subst hvS
                    exact ⟨u, by simp [GameState.record, hs₁_epP], fun _ => by simp [GameState.record, hs₁_epP],
                      hP_sender, hbuck_u, hu_le_qep, hdiv_s₀⟩
                  · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
                    rcases hwf.hvS_blk Q sIdx hvS with ⟨u0, hle0, hs0, hP0, hb0, hq0, hd0⟩
                    exact ⟨u0, by simpa [GameState.record, hs₁_epQ Q hQ] using hle0,
                      by simpa [GameState.record, hs₁_epQ Q hQ] using hs0, hP0, hb0, hq0, hd0⟩
                htrans_wf := fun r0 hr0 => by
                  simp only [GameState.record, List.mem_cons] at hr0
                  rcases hr0 with rfl | hr_old
                  · exact ⟨hs₁_epP, by rw [hs₁_epP]; exact hP_sender, le_rfl, fun _ => by simp [GameState.record]⟩
                  · rw [hs₁_tr] at hr_old
                    rcases hwf.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4⟩
                    refine ⟨h1, h2, le_trans h3 (hs₁_ep_mono _), ?_⟩
                    by_cases hS : r0.pos.sender = P
                    · intro hEq; exfalso
                      simp only [GameState.record, hS, hs₁_epP] at hEq
                      rw [hS] at h3; omega
                    · simpa [GameState.record, Function.update_of_ne hS, hs₁_epQ _ hS, hs₁_idxQ _ hS] using h4
              }
            · intro t ht
              by_cases heq_ut : u = t
              · subst heq_ut
                have hbad_s₁ : EpochBad tL u s₁ := by
                  by_contra hnb; exact htarget_u ⟨ht, hnb⟩
                exact Or.inl (EpochBad.of_sub_leaks hbad_s₁ fun lk hlk => by simp [GameState.record, hlk])
              · refine record_ne_maxOpt ht heq_ut (hep_inv t ht) hs₁_st hs₁_tr hs₁_cp
                  hs₁_epP hs₁_epQ hs₁_ep_mono (by rw [hs₁_epP]; omega) hs₁_idxQ hs₁_leak_cases rfl ?_ ?_ ?_
                · intro sIdx hblk_t hvS
                  simp only [Option.some.injEq, Sum.inr.injEq] at hvS; subst hvS
                  exact heq_ut (block_eq_imp_epoch_eq hΔb hbuck_u ht.1 hdiv_s₀ hblk_t)
                · exact (congrFun hc_sd t).trans (hc_ne_ss t (Ne.symm heq_ut))
                · intro sIdx hblk_t
                  have hne_s : sIdx ≠ s₀ := fun hEq_s =>
                    heq_ut (block_eq_imp_epoch_eq hΔb hbuck_u ht.1 hdiv_s₀ (hEq_s ▸ hblk_t))
                  exact hσ_ne sIdx hne_s
      · -- Branch T1b: `ssv = .inl ss_inl` (`postLeakDFBucket = true ∨ qep + 1 < u ∨ inStage2BucketGen = false`).
        dsimp only [hooksFSMultiDFBucketPaper] at hw_fs
        simp only [StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw_fs
        subst hw_fs
        simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
        subst hw_fin
        dsimp only
        refine Or.inr ⟨hs₁_win, rfl, ?_, ?_⟩
        · refine {
            habort := hwf.habort
            hwin := hs₁_win
            hid := fun Q => by
              by_cases hQ : Q = P
              · rw [hQ]; simp [GameState.record]
              · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hwf.hid Q]
            htcur := fun Q => by
              by_cases hQ : Q = P
              · rw [hQ]; simp [GameState.record, hs₁_epP]
              · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hs₁_epQ Q hQ, hwf.htcur Q]
            htL_mem := hs₁_tL_mem
            hsess_zero := fun ik hik => by
              rw [hse_ne_ss 0 (by omega)] at hik ⊢
              exact hwf.hsess_zero ik hik
            hsess_pos := fun u' hu' => by
              dsimp only
              by_cases hEq : u' = u
              · subst u'; have := hwf.hsess_pos u hu_pos; omega
              · rw [hse_ne_ss u' hEq]; have := hwf.hsess_pos u' hu'; omega
            hcache_blk := fun u' Tc σc k sIdx hc => by
              by_cases hEq : u' = u
              · subst u'; rw [hc_u_ss] at hc; simp at hc
              · rw [hc_ne_ss u' hEq] at hc
                exact hwf.hcache_blk u' Tc σc k sIdx hc
            hvR_blk := fun Q u' sIdx hvR => by
              by_cases hQ : Q = P
              · rw [hQ] at hvR; simp only [GameState.record, Function.update_self] at hvR
                exact hwf.hvR_blk P u' sIdx hvR
              · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvR
                exact hwf.hvR_blk Q u' sIdx hvR
            hvS_blk := fun Q sIdx hvS => by
              by_cases hQ : Q = P
              · rw [hQ] at hvS; simp [GameState.record] at hvS
              · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
                rcases hwf.hvS_blk Q sIdx hvS with ⟨u0, hle0, hs0, hP0, hb0, hq0, hd0⟩
                exact ⟨u0, by simpa [GameState.record, hs₁_epQ Q hQ] using hle0,
                  by simpa [GameState.record, hs₁_epQ Q hQ] using hs0, hP0, hb0, hq0, hd0⟩
            htrans_wf := fun r0 hr0 => by
              simp only [GameState.record, List.mem_cons] at hr0
              rcases hr0 with rfl | hr_old
              · exact ⟨hs₁_epP, by rw [hs₁_epP]; exact hP_sender, le_rfl, fun _ => by simp [GameState.record]⟩
              · rw [hs₁_tr] at hr_old
                rcases hwf.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4⟩
                refine ⟨h1, h2, le_trans h3 (hs₁_ep_mono _), ?_⟩
                by_cases hS : r0.pos.sender = P
                · intro hEq; exfalso
                  simp only [GameState.record, hS, hs₁_epP] at hEq
                  rw [hS] at h3; omega
                · simpa [GameState.record, Function.update_of_ne hS, hs₁_epQ _ hS, hs₁_idxQ _ hS] using h4
          }
        · intro t ht
          by_cases heq_ut : u = t
          · -- Entering target epoch `t = u` with `postLeakDFBucket tL s₁ = true` -> `EpochCompEntry` (or `EpochBad`)!
            subst heq_ut
            have hpl_true : postLeakDFBucket tL s₁ = true := by
              rcases hnot_buck with hpl | hgt | hfb
              · exact hpl
              · omega
              · rw [ht.1] at hfb; cases hfb
            rcases hep_inv u ht with hbad | hcomp | hpre | ⟨_, hidl⟩
            · exact Or.inl (EpochBad.of_sub_leaks hbad fun lk hlk => by
                rcases hs₁_leak_cases with ⟨hL, _⟩ | ⟨hL, _⟩ <;> simp [GameState.record, hL, hlk])
            · exfalso; have := hcomp.1; rw [← hP_sender] at this; omega
            · -- `EpochPre` + `postLeakDFBucket tL s₁ = true` means `s₁` leaked `u`, so `s₁.tL = some (maxOpt es.g.tL u)`!
              have hs₁_tL_u : ∃ cur, s₁.tL = some cur ∧ u ≤ cur := by
                rcases hs₁_leak_cases with ⟨_, htL_eq⟩ | ⟨_, htL_eq⟩
                · exfalso
                  have hpl0 := hpre.2.2.1
                  simp only [postLeakDFBucket, htL_eq] at hpl_true
                  simp only [postLeakDFBucket] at hpl0
                  rw [hpl0] at hpl_true; cases hpl_true
                · exact ⟨maxOpt es.g.tL u, htL_eq, by
                    cases es.g.tL with
                    | none => exact le_rfl
                    | some cur0 => exact Nat.le_max_right _ _⟩
              rcases hs₁_tL_u with ⟨cur_u, hs₁_tL_eq, hu_le_cur⟩
              have hnot_heal_u : healedBy s₁.tL (2 + Δcka) u = false := by
                simp only [hs₁_tL_eq, healedBy, decide_eq_false_iff_not]; omega
              refine Or.inr (Or.inl ⟨by simp [GameState.record, ← hP_sender, hs₁_epP],
                ⟨cur_u, by simp [GameState.record, hs₁_tL_eq], hu_le_cur⟩, ?_, ?_, ?_, ?_⟩)
              · intro r0 hr0 hep0
                simp only [GameState.record, List.mem_cons] at hr0
                rcases hr0 with rfl | hr_old
                · simp [GameState.record, GameState.safeCh, hs₁_epP, hnot_heal_u]
                · exfalso
                  rw [hs₁_tr] at hr_old
                  have hle := (hwf.htrans_wf r0 hr_old).2.2.1
                  have := hpre.1 r0.pos.sender
                  omega
              · intro Q sIdx hblk hvS
                by_cases hQ : Q = P
                · rw [hQ] at hvS; simp [GameState.record] at hvS
                · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
                  exact hpre.2.2.2.2.1 Q sIdx hblk hvS
              · intro Q sIdx
                by_cases hQ : Q = P
                · rw [hQ]; simp [GameState.record, hpre.2.2.2.1 P]
                · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hpre.2.2.2.1 Q]
              · intro Tc σc k optIdx hc
                rw [hc_u_ss] at hc
                injection hc with hquad
                exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hquad).2).2).2.symm
            · exfalso; have := hidl.2.1; rw [← hP_sender] at this; omega
          · refine record_ne_maxOpt ht heq_ut (hep_inv t ht) hs₁_st hs₁_tr hs₁_cp
              hs₁_epP hs₁_epQ hs₁_ep_mono (by rw [hs₁_epP]; omega) hs₁_idxQ hs₁_leak_cases rfl ?_ ?_ ?_
            · intro _ _ hvS; simp at hvS
            · exact hc_ne_ss t (Ne.symm heq_ut)
            · exact fun _ _ => rfl
    · -- Case T2: `P` stays in current sending epoch `u := es.g.epoch P` (`s₁ = es.g`).
      simp only [Bool.not_eq_true] at hsIn1
      simp only [hsIn1, Bool.false_eq_true, ↓reduceIte] at hep
      generalize hu_eq : es.g.epoch P = u at hep hsIn1
      have hu_def : u = es.g.epoch P := hu_eq.symm
      have hsIn0 : P.sendsIn u = true := by
        cases P <;> simp [Party.sendsIn] at hsIn1 ⊢ <;> omega
      have hP_sender : P = Party.senderOf u := by
        cases P <;> simp [Party.senderOf, Party.sendsIn] at hsIn0 ⊢ <;> exact hsIn0
      have hs₁_eq : s₁ = es.g := by
        by_cases hlt : qep < u
        · simp only [hlt, ↓reduceIte] at hep; cases hep
        · simp only [hlt, ↓reduceIte, Option.some.injEq] at hep; exact hep.symm
      subst hs₁_eq
      rw [liftH_bind_run] at hw
      rcases runPubIdeal_bind_support_false _ _ rc σ hw with ⟨w_sd, hw_sd, hw_fin⟩
      dsimp only [runPubIdeal] at hw_sd hw_fin
      unfold vSend at hw_sd
      rw [hfs_eq] at hw_sd
      simp only [pure_bind, hwf.hid P, hwf.htcur P, ← hu_def, hsIn1, Bool.false_eq_true,
        ↓reduceIte] at hw_sd
      cases hvSP : (es.g.st P).vS with
      | none =>
        simp only [hvSP, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw_sd
        subst hw_sd
        simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
        subst hw_fin
        dsimp only
        refine Or.inr ⟨hwf.hwin, rfl, ?_, ?_⟩
        · refine {
            habort := hwf.habort, hwin := hwf.hwin,
            hid := fun Q => by simp [GameState.record, hwf.hid Q],
            htcur := fun Q => by simp [GameState.record, hwf.htcur Q],
            htL_mem := hwf.htL_mem, hsess_zero := hwf.hsess_zero,
            hsess_pos := fun u' hu' => by dsimp only; have := hwf.hsess_pos u' hu'; omega,
            hcache_blk := hwf.hcache_blk,
            hvR_blk := fun Q u' sIdx hvR => by
              by_cases hQ : Q = P
              · rw [hQ] at hvR; simp only [GameState.record, Function.update_self] at hvR
                exact hwf.hvR_blk P u' sIdx hvR
              · simp only [GameState.record, Function.update_of_ne hQ] at hvR
                exact hwf.hvR_blk Q u' sIdx hvR,
            hvS_blk := fun Q sIdx hvS => by
              by_cases hQ : Q = P
              · rw [hQ] at hvS; simp [GameState.record, hvSP] at hvS
              · simp only [GameState.record, Function.update_of_ne hQ] at hvS
                rcases hwf.hvS_blk Q sIdx hvS with ⟨u0, hle0, hs0, hP0, hb0, hq0, hd0⟩
                exact ⟨u0, by simpa [GameState.record] using hle0,
                  by simpa [GameState.record] using hs0, hP0, hb0, hq0, hd0⟩,
            htrans_wf := fun r0 hr0 => by
              simp only [GameState.record, List.mem_cons] at hr0
              rcases hr0 with rfl | hr_old
              · exact ⟨hu_def.symm, by rw [← hu_def]; exact hP_sender, le_rfl, fun _ => by simp [GameState.record]⟩
              · rcases hwf.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4⟩
                refine ⟨h1, h2, h3, ?_⟩
                by_cases hS : r0.pos.sender = P
                · intro hEq; have hle_idx := h4 hEq; rw [hS] at hle_idx
                  simp only [GameState.record, hS, Function.update_self]; omega
                · simpa [GameState.record, Function.update_of_ne hS] using h4 }
        · intro t ht
          by_cases heq_ut : u = t
          · subst heq_ut
            rcases hep_inv u ht with hbad | hcomp | hpre | ⟨s₀, hidl⟩
            · exact Or.inl (EpochBad.of_sub_leaks hbad fun lk hlk => by simp [GameState.record, hlk])
            · rcases hcomp.2.1 with ⟨cur_u, hcur_u, hu_le_cur⟩
              have hnot_heal_u : healedBy es.g.tL (2 + Δcka) u = false := by
                simp only [hcur_u, healedBy, decide_eq_false_iff_not]; omega
              refine Or.inr (Or.inl ⟨hcomp.1, ⟨cur_u, hcur_u, hu_le_cur⟩, ?_, ?_, ?_, hcomp.2.2.2.2.2⟩)
              · intro r0 hr0 hep0
                simp only [GameState.record, List.mem_cons] at hr0
                rcases hr0 with rfl | hr_old
                · simp [GameState.record, GameState.safeCh, ← hu_def, hnot_heal_u]
                · have hc0 := hcomp.2.2.1 r0 hr_old hep0
                  simp only [GameState.record]; split_ifs <;> simp [hc0]
              · intro Q sIdx hblk hvS
                by_cases hQ : Q = P
                · rw [hQ] at hvS; simp [GameState.record, hvSP] at hvS
                · simp only [GameState.record, Function.update_of_ne hQ] at hvS
                  exact hcomp.2.2.2.1 Q sIdx hblk hvS
              · intro Q sIdx
                simp [GameState.record, hcomp.2.2.2.2.1 Q]
            · exfalso; have := hpre.1 P; omega
            · exfalso
              have hvS_s₀ := hidl.2.2.2.1 (by rw [← hP_sender]; exact hu_def.symm)
              rw [← hP_sender, hvSP] at hvS_s₀; cases hvS_s₀
          · refine record_ne_maxOpt ht heq_ut (hep_inv t ht) rfl rfl rfl hu_def.symm
              (fun _ _ => rfl) (fun _ => le_rfl) (Nat.le_succ _) (fun _ _ => rfl)
              (Or.inl ⟨rfl, rfl⟩) rfl ?_ rfl (fun _ _ => rfl)
            intro _ _ h; simp [hvSP] at h
      | some vS0 =>
        cases vS0 with
        | inl ss_inl =>
          rw [hvSP] at hw_sd
          dsimp only [hooksFSMultiDFBucketPaper] at hw_sd
          simp only [StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_sd
          subst hw_sd
          simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
          subst hw_fin
          dsimp only
          refine Or.inr ⟨hwf.hwin, rfl, ?_, ?_⟩
          · refine {
              habort := hwf.habort, hwin := hwf.hwin,
              hid := fun Q => by
                by_cases hQ : Q = P
                · rw [hQ]; simp [GameState.record]
                · simp [GameState.record, Function.update_of_ne hQ, hwf.hid Q],
              htcur := fun Q => by
                by_cases hQ : Q = P
                · rw [hQ]; simp [GameState.record, hu_def]
                · simp [GameState.record, Function.update_of_ne hQ, hwf.htcur Q],
              htL_mem := hwf.htL_mem, hsess_zero := hwf.hsess_zero,
              hsess_pos := fun u' hu' => by dsimp only; have := hwf.hsess_pos u' hu'; omega,
              hcache_blk := hwf.hcache_blk,
              hvR_blk := fun Q u' sIdx hvR => by
                by_cases hQ : Q = P
                · rw [hQ] at hvR; simp only [GameState.record, Function.update_self] at hvR
                  exact hwf.hvR_blk P u' sIdx hvR
                · simp only [GameState.record, Function.update_of_ne hQ] at hvR
                  exact hwf.hvR_blk Q u' sIdx hvR,
              hvS_blk := fun Q sIdx hvS => by
                by_cases hQ : Q = P
                · rw [hQ] at hvS; simp [GameState.record] at hvS
                · simp only [GameState.record, Function.update_of_ne hQ] at hvS
                  rcases hwf.hvS_blk Q sIdx hvS with ⟨u0, hle0, hs0, hP0, hb0, hq0, hd0⟩
                  exact ⟨u0, by simpa [GameState.record] using hle0,
                    by simpa [GameState.record] using hs0, hP0, hb0, hq0, hd0⟩,
              htrans_wf := fun r0 hr0 => by
                simp only [GameState.record, List.mem_cons] at hr0
                rcases hr0 with rfl | hr_old
                · exact ⟨hu_def.symm, by rw [← hu_def]; exact hP_sender, le_rfl, fun _ => by simp [GameState.record]⟩
                · rcases hwf.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4⟩
                  refine ⟨h1, h2, h3, ?_⟩
                  by_cases hS : r0.pos.sender = P
                  · intro hEq; have hle_idx := h4 hEq; rw [hS] at hle_idx
                    simp only [GameState.record, hS, Function.update_self]; omega
                  · simpa [GameState.record, Function.update_of_ne hS] using h4 }
          · intro t ht
            by_cases heq_ut : u = t
            · subst heq_ut
              rcases hep_inv u ht with hbad | hcomp | hpre | ⟨s₀, hidl⟩
              · exact Or.inl (EpochBad.of_sub_leaks hbad fun lk hlk => by simp [GameState.record, hlk])
              · rcases hcomp.2.1 with ⟨cur_u, hcur_u, hu_le_cur⟩
                have hnot_heal_u : healedBy es.g.tL (2 + Δcka) u = false := by
                  simp only [hcur_u, healedBy, decide_eq_false_iff_not]; omega
                refine Or.inr (Or.inl ⟨hcomp.1, ⟨cur_u, hcur_u, hu_le_cur⟩, ?_, ?_, ?_, hcomp.2.2.2.2.2⟩)
                · intro r0 hr0 hep0
                  simp only [GameState.record, List.mem_cons] at hr0
                  rcases hr0 with rfl | hr_old
                  · simp [GameState.record, GameState.safeCh, ← hu_def, hnot_heal_u]
                  · have hc0 := hcomp.2.2.1 r0 hr_old hep0
                    simp only [GameState.record]; split_ifs <;> simp [hc0]
                · intro Q sIdx hblk hvS
                  by_cases hQ : Q = P
                  · rw [hQ] at hvS; simp [GameState.record] at hvS
                  · simp only [GameState.record, Function.update_of_ne hQ] at hvS
                    exact hcomp.2.2.2.1 Q sIdx hblk hvS
                · intro Q sIdx
                  by_cases hQ : Q = P
                  · rw [hQ]; simp [GameState.record, hcomp.2.2.2.2.1 P]
                  · simp [GameState.record, Function.update_of_ne hQ, hcomp.2.2.2.2.1 Q]
              · exfalso; have := hpre.1 P; omega
              · exfalso
                have hvS_s₀ := hidl.2.2.2.1 (by rw [← hP_sender]; exact hu_def.symm)
                rw [← hP_sender, hvSP] at hvS_s₀; cases hvS_s₀
            · refine record_ne_maxOpt ht heq_ut (hep_inv t ht) rfl rfl rfl hu_def.symm
                (fun _ _ => rfl) (fun _ => le_rfl) (Nat.le_succ _) (fun _ _ => rfl)
                (Or.inl ⟨rfl, rfl⟩) rfl ?_ rfl (fun _ _ => rfl)
              intro _ _ h; simp at h
        | inr sIdx =>
          rcases hwf.hvS_blk P sIdx hvSP with ⟨u0, _, hs0, _, hbuck_u, hu_le_qep, hdiv_sIdx⟩
          have hu0_eq : u0 = u := (hs0 (hu_def ▸ hsIn0)).trans hu_def.symm
          subst u0
          by_cases htarget_u : IsTargetEpoch Δcka Δbucket qep tL par u ∧ ¬ EpochBad tL u es.g
          · -- Subcase T2b-1: `u` is a clean target epoch (`EpochIdealAt` at `s₀ = sIdx`).
            rcases htarget_u with ⟨ht_u, hnot_bad_u⟩
            have hidl_u : EpochIdeal q Δcka tL u es σ := by
              rcases hep_inv u ht_u with hbad | hcomp | hpre | hidl
              · exact (hnot_bad_u hbad).elim
              · exact (hcomp.2.2.2.1 P sIdx hdiv_sIdx hvSP).elim
              · exfalso; have := hpre.1 P; omega
              · exact hidl
            rcases hidl_u with ⟨s₀, hdiv_s₀, hep_s₀, hct_idx, hvS_eq, hvS_all, hunused, hnone_tr, hsome, hvR, hvR_ge, hpin⟩
            rcases hvS_all P sIdx hdiv_sIdx hvSP with ⟨_, rfl, hsends⟩
            rcases hsends (by rw [← hP_sender, ← hu_def]; exact hsIn0) with ⟨_, hpre_idx⟩
            simp only [hvSP, StateT.run_bind, simulateQ_bind,
              MonadAttach.mem_support_bind] at hw_sd
            rcases hw_sd with ⟨w_fs, hw_fs, hw_ret⟩
            rcases fsSend_inr_bucket_step_post C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
                u sIdx es.g (u, (es.g.st P).curCkaMsg) pm es.h rc σ
                (by rw [← hP_sender]; exact hu_def.symm)
                (by
                  rcases hpre_idx with ⟨hnone, hidx0⟩ | ⟨st₀, hsome0, hls0⟩
                  · exact Or.inl ⟨hnone, hidx0, hnone_tr hnone⟩
                  · have h5 := hsome st₀ hsome0
                    exact Or.inr ⟨st₀, hsome0, h5.1, hls0, h5.2.1, h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2⟩)
                w_fs
                (by convert hw_fs using 5; exact hP_sender.symm) with hsd_none |
              ⟨rawCt, st₂, hsd_ok, hc_sd, hse_sd, hσ_upd, hend₂, hls₂, hit₂, hrec₂⟩
            · simp only [hsd_none, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw_ret
              subst hw_ret
              simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin; exact Or.inl rfl
            · simp only [hsd_ok, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw_ret
              subst hw_ret
              simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin
              dsimp only
              subst hP_sender
              rcases hrec₂ _ with ⟨hrec_idx, hrec_heal, hrec_unc⟩
              refine Or.inr ⟨hwf.hwin, rfl, ?_, ?_⟩
              · refine {
                  habort := hwf.habort, hwin := hwf.hwin,
                  hid := fun Q => by
                    by_cases hQ : Q = Party.senderOf u
                    · rw [hQ]; simp [GameState.record]
                    · simp [GameState.record, Function.update_of_ne hQ, hwf.hid Q],
                  htcur := fun Q => by
                    by_cases hQ : Q = Party.senderOf u
                    · rw [hQ]; simp [GameState.record, ← hu_def]
                    · simp [GameState.record, Function.update_of_ne hQ, hwf.htcur Q],
                  htL_mem := hwf.htL_mem,
                  hsess_zero := fun ik hik => by rw [hse_sd] at hik ⊢; exact hwf.hsess_zero ik hik,
                  hsess_pos := fun u' hu' => by rw [hse_sd]; have := hwf.hsess_pos u' hu'; omega,
                  hcache_blk := fun u' Tc σc k idx hc => hwf.hcache_blk u' Tc σc k idx (hc_sd ▸ hc),
                  hvR_blk := fun Q u' idx hvR => by
                    by_cases hQ : Q = Party.senderOf u
                    · rw [hQ] at hvR; simp only [GameState.record, Function.update_self] at hvR
                      exact hwf.hvR_blk _ u' idx hvR
                    · simp only [GameState.record, Function.update_of_ne hQ] at hvR
                      exact hwf.hvR_blk Q u' idx hvR,
                  hvS_blk := fun Q idx hvS => by
                    by_cases hQ : Q = Party.senderOf u
                    · rw [hQ] at hvS ⊢
                      simp only [GameState.record, Function.update_self, Option.some.injEq,
                        Sum.inr.injEq] at hvS
                      subst hvS
                      exact ⟨u, by simp [GameState.record, ← hu_def], fun _ => hu_def, rfl,
                        hbuck_u, hu_le_qep, hdiv_sIdx⟩
                    · simp only [GameState.record, Function.update_of_ne hQ] at hvS
                      rcases hwf.hvS_blk Q idx hvS with ⟨u1, hle1, hs1, hP1, hb1, hq1, hd1⟩
                      exact ⟨u1, by simpa [GameState.record] using hle1,
                        by simpa [GameState.record] using hs1, hP1, hb1, hq1, hd1⟩,
                  htrans_wf := fun r0 hr0 => by
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old
                    · exact ⟨hu_def.symm, by simp [← hu_def], le_rfl, fun _ => by simp [GameState.record]⟩
                    · rcases hwf.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4⟩
                      refine ⟨h1, h2, h3, ?_⟩
                      by_cases hS : r0.pos.sender = Party.senderOf u
                      · intro hEq; have hle_idx := h4 hEq; rw [hS] at hle_idx
                        simp only [GameState.record, hS, Function.update_self]; omega
                      · simpa [GameState.record, Function.update_of_ne hS] using h4 }
              · intro t ht
                by_cases heq_ut : u = t
                · subst heq_ut
                  rw [hσ_upd]
                  refine Or.inr (Or.inr (Or.inr ⟨sIdx, hdiv_sIdx, hep_s₀, ?_,
                    fun _ => by simp [GameState.record], ?_, ?_,
                    by intro h; simp at h, ?_, ?_, ?_, ?_⟩))
                  · intro r0 hr0 hep0
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old
                    · rfl
                    · exact hct_idx r0 hr_old hep0
                  · intro Q idx hblkQ hvSQ
                    by_cases hQ : Q = Party.senderOf u
                    · rw [hQ] at hvSQ ⊢
                      simp only [GameState.record, Function.update_self, Option.some.injEq,
                        Sum.inr.injEq] at hvSQ
                      subst hvSQ
                      refine ⟨rfl, rfl, fun _ => ⟨hu_def.symm, Or.inr ⟨st₂, by simp, ?_⟩⟩⟩
                      simp [GameState.record, hls₂]
                    · simp only [GameState.record, Function.update_of_ne hQ] at hvSQ
                      exact ((hvS_all Q idx hblkQ hvSQ).1 |> hQ).elim
                  · intro idx st hblk_i hne_i hst_i
                    rw [Function.update_of_ne hne_i] at hst_i
                    exact hunused idx st hblk_i hne_i hst_i
                  · intro st hst
                    simp only [Function.update_self, Option.some.injEq] at hst; subst hst
                    simp only [← hu_def] at hrec_idx hrec_heal hrec_unc ⊢
                    exact ⟨hend₂, hit₂, hrec_idx, hrec_heal, hrec_unc⟩
                  · intro Q v0 hv0
                    by_cases hQ : Q = Party.senderOf u
                    · rw [hQ] at hv0; simp only [GameState.record, Function.update_self] at hv0
                      exact hvR _ v0 hv0
                    · simp only [GameState.record, Function.update_of_ne hQ] at hv0
                      exact hvR Q v0 hv0
                  · intro hle_rec
                    have hne_rs : Party.receiverOf u ≠ Party.senderOf u := by
                      cases h : Party.senderOf u <;> simp [Party.receiverOf, Party.other, h]
                    simp only [GameState.record] at hle_rec
                    simpa only [GameState.record, Function.update_of_ne hne_rs] using hvR_ge hle_rec
                  · intro ht_pos
                    rcases hpin ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
                    refine ⟨Tc, σc, k, hc_sd ▸ hc_Tc,
                      fun _ => by simpa [GameState.record] using hcur_Tc hu_def.symm, ?_⟩
                    intro r0 hr0 hep0
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old
                    · exact hcur_Tc hu_def.symm
                    · exact htr_Tc r0 hr_old hep0
                · refine record_ne_maxOpt ht heq_ut (hep_inv t ht) rfl rfl rfl hu_def.symm
                    (fun _ _ => rfl) (fun _ => le_rfl) (Nat.le_succ _) (fun _ _ => rfl)
                    (Or.inl ⟨rfl, rfl⟩) rfl ?_ ?_ ?_
                  · intro idx hblk_t hvS
                    simp only [Option.some.injEq, Sum.inr.injEq] at hvS; subst hvS
                    exact heq_ut (block_eq_imp_epoch_eq hΔb hbuck_u ht.1 hdiv_sIdx hblk_t)
                  · exact congrFun hc_sd t
                  · intro idx hblk_t
                    rw [hσ_upd]
                    have hne_s : idx ≠ sIdx := fun hEq_s =>
                      heq_ut (block_eq_imp_epoch_eq hΔb hbuck_u ht.1 hdiv_sIdx (hEq_s ▸ hblk_t))
                    exact Function.update_of_ne hne_s _ _
          · -- Subcase T2b-2: `¬ (IsTargetEpoch ... u ∧ ¬ EpochBad tL u es.g)`.
            simp only [hvSP, StateT.run_bind, simulateQ_bind,
              MonadAttach.mem_support_bind] at hw_sd
            rcases hw_sd with ⟨w_fs, hw_fs, hw_ret⟩
            rcases fsSend_inr_bucket_any_support C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
                P u sIdx es.g (u, (es.g.st P).curCkaMsg) pm es.h rc σ w_fs hw_fs with
              ⟨hc_sd, hse_sd, hσ_ne, hsd_none | ⟨e_out, hsd_ok⟩⟩
            · simp only [hsd_none, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw_ret
              subst hw_ret
              simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin; exact Or.inl rfl
            · simp only [hsd_ok, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw_ret
              subst hw_ret
              simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin
              dsimp only
              refine Or.inr ⟨hwf.hwin, rfl, ?_, ?_⟩
              · refine {
                  habort := hwf.habort, hwin := hwf.hwin,
                  hid := fun Q => by
                    by_cases hQ : Q = P
                    · rw [hQ]; simp [GameState.record]
                    · simp [GameState.record, Function.update_of_ne hQ, hwf.hid Q],
                  htcur := fun Q => by
                    by_cases hQ : Q = P
                    · rw [hQ]; simp [GameState.record, hu_def]
                    · simp [GameState.record, Function.update_of_ne hQ, hwf.htcur Q],
                  htL_mem := hwf.htL_mem,
                  hsess_zero := fun ik hik => by rw [hse_sd] at hik ⊢; exact hwf.hsess_zero ik hik,
                  hsess_pos := fun u' hu' => by rw [hse_sd]; have := hwf.hsess_pos u' hu'; omega,
                  hcache_blk := fun u' Tc σc k idx hc => hwf.hcache_blk u' Tc σc k idx (hc_sd ▸ hc),
                  hvR_blk := fun Q u' idx hvR => by
                    by_cases hQ : Q = P
                    · rw [hQ] at hvR; simp only [GameState.record, Function.update_self] at hvR
                      exact hwf.hvR_blk P u' idx hvR
                    · simp only [GameState.record, Function.update_of_ne hQ] at hvR
                      exact hwf.hvR_blk Q u' idx hvR,
                  hvS_blk := fun Q idx hvS => by
                    by_cases hQ : Q = P
                    · rw [hQ] at hvS ⊢
                      simp only [GameState.record, Function.update_self, Option.some.injEq,
                        Sum.inr.injEq] at hvS
                      subst hvS
                      exact ⟨u, by simp [GameState.record, ← hu_def], fun _ => hu_def, hP_sender,
                        hbuck_u, hu_le_qep, hdiv_sIdx⟩
                    · simp only [GameState.record, Function.update_of_ne hQ] at hvS
                      rcases hwf.hvS_blk Q idx hvS with ⟨u1, hle1, hs1, hP1, hb1, hq1, hd1⟩
                      exact ⟨u1, by simpa [GameState.record] using hle1,
                        by simpa [GameState.record] using hs1, hP1, hb1, hq1, hd1⟩,
                  htrans_wf := fun r0 hr0 => by
                    simp only [GameState.record, List.mem_cons] at hr0
                    rcases hr0 with rfl | hr_old
                    · exact ⟨hu_def.symm, by rw [← hu_def]; exact hP_sender, le_rfl, fun _ => by simp [GameState.record]⟩
                    · rcases hwf.htrans_wf r0 hr_old with ⟨h1, h2, h3, h4⟩
                      refine ⟨h1, h2, h3, ?_⟩
                      by_cases hS : r0.pos.sender = P
                      · intro hEq; have hle_idx := h4 hEq; rw [hS] at hle_idx
                        simp only [GameState.record, hS, Function.update_self]; omega
                      · simpa [GameState.record, Function.update_of_ne hS] using h4 }
              · intro t ht
                by_cases heq_ut : u = t
                · subst heq_ut
                  have hbad_u : EpochBad tL u es.g := by
                    by_contra hnb; exact htarget_u ⟨ht, hnb⟩
                  exact Or.inl (EpochBad.of_sub_leaks hbad_u fun lk hlk => by simp [GameState.record, hlk])
                · refine record_ne_maxOpt ht heq_ut (hep_inv t ht) rfl rfl rfl hu_def.symm
                    (fun _ _ => rfl) (fun _ => le_rfl) (Nat.le_succ _) (fun _ _ => rfl)
                    (Or.inl ⟨rfl, rfl⟩) rfl ?_ ?_ ?_
                  · intro idx hblk_t hvS
                    simp only [Option.some.injEq, Sum.inr.injEq] at hvS; subst hvS
                    exact heq_ut (block_eq_imp_epoch_eq hΔb hbuck_u ht.1 hdiv_sIdx hblk_t)
                  · exact congrFun hc_sd t
                  · intro idx hblk_t
                    have hne_s : idx ≠ sIdx := fun hEq_s =>
                      heq_ut (block_eq_imp_epoch_eq hΔb hbuck_u ht.1 hdiv_sIdx (hEq_s ▸ hblk_t))
                    exact hσ_ne idx hne_s

end BucketStep

end

end Computational.Proofs.E2E.SessionAuthMultiEndBucketTransmit

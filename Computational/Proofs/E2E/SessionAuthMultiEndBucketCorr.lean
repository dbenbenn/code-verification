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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions


/-!
# `GameState.leak` / `record` Helpers & `corrEPaperBucket` Step Preservation for `DeliverForgePaperMultiBucket`

Proves `EpochInv.record_ne` and `corrEPaperBucket_bucket_step` (`la = false`, `1 ≤ q`, `2 ≤ Δbucket`).-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEndBucketCorr

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


/-! ## 1. `GameState.leak`, `record`, and `afterCorr` Helpers on `EpochInv` -/

theorem healedBy_of_leak {St Msg C : Type} (g : GameState St Msg C) (l Δ t : ℕ)
    (hh : healedBy (g.leak l).tL Δ t = true) :
    healedBy g.tL Δ t = true := by
  cases htL : g.tL with
  | none => rfl
  | some l0 =>
    simp only [GameState.leak, maxOpt, htL, healedBy, decide_eq_true_eq] at hh ⊢
    omega

theorem tL_mem_of_leak {St Msg C : Type} {g : GameState St Msg C} (l : ℕ)
    (hmem : ∀ cur, g.tL = some cur → cur ∈ g.leaks) :
    ∀ cur, (g.leak l).tL = some cur → cur ∈ (g.leak l).leaks := by
  let _ := hmem
  intro cur hcur
  simp only [GameState.leak, Option.some.injEq] at hcur ⊢
  subst hcur
  exact List.mem_cons_self

theorem EpochBad.of_sub_leaks {St₁ St₂ Msg C₁ C₂ : Type}
    {tL : Option ℕ} {t : ℕ} {g₁ : GameState St₁ Msg C₁} {g₂ : GameState St₂ Msg C₂}
    (h : EpochBad tL t g₁) (hsub : ∀ lk ∈ g₁.leaks, lk ∈ g₂.leaks) :
    EpochBad tL t g₂ := by
  rcases h with ⟨lk, hlk, hlt, hlt_t⟩
  exact ⟨lk, hsub lk hlk, hlt, hlt_t⟩

theorem block_eq_imp_epoch_eq {q Δbucket : ℕ} {tL : Option ℕ} {par : Bool}
    {u t sIdx : ℕ}
    (hΔb : 2 ≤ Δbucket)
    (hb_u : inStage2BucketGen Δbucket tL par u = true)
    (hb_t : inStage2BucketGen Δbucket tL par t = true)
    (hdiv_u : sIdx / q = u - healEpoch tL)
    (hdiv_t : sIdx / q = t - healEpoch tL) :
    u = t := by
  have hle_u := healEpoch_le_of_inStage2BucketGen hΔb hb_u
  have hle_t := healEpoch_le_of_inStage2BucketGen hΔb hb_t
  omega

/-- Off-epoch (`u ≠ t`) preservation of `EpochInv q Δcka tL t` across `s₁.record`. -/
theorem EpochInv.record_ne {ℓ : ℕ}
    {q Δcka Δbucket qep : ℕ} {tL : Option ℕ} {par : Bool} {u t : ℕ}
    {P : Party}
    {es : BucketEState Pt ℓ}
    {s₁ : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    {st' : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)}
    {pm : LibsignalMsgPublicPart × Plain ℓ}
    {c : Fig8C Pt}
    {hs' : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    {σ σ' : ℕ → Option (IdealHSt Pt ℓ)}
    (ht : IsTargetEpoch Δcka Δbucket qep tL par t)
    (hne_ut : u ≠ t)
    (hinv : EpochInv q Δcka tL t es σ)
    (hs₁_st : s₁.st = es.g.st)
    (hs₁_tr : s₁.trans = es.g.trans)
    (hs₁_cp : s₁.comp = es.g.comp)
    (hs₁_epP : s₁.epoch P = u)
    (hs₁_epQ : ∀ Q, Q ≠ P → s₁.epoch Q = es.g.epoch Q)
    (hs₁_ep_mono : ∀ Q, es.g.epoch Q ≤ s₁.epoch Q)
    (hs₁_ep_le_succ : s₁.epoch P ≤ es.g.epoch P + 1)
    (hs₁_idxQ : ∀ Q, Q ≠ P → s₁.idx Q = es.g.idx Q)
    (hs₁_leak_cases :
      (s₁.leaks = es.g.leaks ∧ s₁.tL = es.g.tL) ∨
      (s₁.leaks = u :: es.g.leaks ∧ s₁.tL = some (maxOpt es.g.tL u)))
    (hvR' : st'.vR = (es.g.st P).vR)
    (hvS'_blk : ∀ sIdx, sIdx / q = t - healEpoch tL → st'.vS ≠ some (.inr sIdx))
    (hc_t : hs'.cache t = es.h.cache t)
    (hσ_t : ∀ sIdx, sIdx / q = t - healEpoch tL → σ' sIdx = σ sIdx) :
    EpochInv q Δcka tL t
      { es with
          g := s₁.record (2 + Δcka) P st' ⟨⟨P, u, s₁.idx P + 1⟩, pm, c⟩ false
          h := hs' } σ' := by
  have hleaks_sub : ∀ lk ∈ es.g.leaks, lk ∈ s₁.leaks := by
    intro lk hlk
    rcases hs₁_leak_cases with ⟨hL, _⟩ | ⟨hL, _⟩
    · rw [hL]; exact hlk
    · rw [hL]; exact List.mem_cons_of_mem _ hlk
  have hs₁_heal : healedBy s₁.tL (2 + Δcka) t = true → healedBy es.g.tL (2 + Δcka) t = true := by
    rcases hs₁_leak_cases with ⟨_, htL_eq⟩ | ⟨_, htL_eq⟩
    · rw [htL_eq]; exact id
    · rw [htL_eq]
      intro hh
      exact healedBy_of_leak es.g u (2 + Δcka) t hh
  rcases hinv with hbad | hcomp | hpre | ⟨s₀, hidl⟩
  · exact Or.inl (EpochBad.of_sub_leaks hbad fun lk hlk => by simp [GameState.record, hleaks_sub lk hlk])
  · refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)
    · simp only [GameState.record]
      exact le_trans hcomp.1 (hs₁_ep_mono (Party.senderOf t))
    · rcases hcomp.2.1 with ⟨cur0, hcur0, hle0⟩
      rcases hs₁_leak_cases with ⟨_, htL_eq⟩ | ⟨_, htL_eq⟩
      · exact ⟨cur0, by simp [GameState.record, htL_eq, hcur0], hle0⟩
      · refine ⟨max cur0 u, by simp [GameState.record, htL_eq, maxOpt, hcur0], le_trans hle0 (Nat.le_max_left _ _)⟩
    · intro r0 hr0 hep0
      simp only [GameState.record, List.mem_cons] at hr0
      rcases hr0 with rfl | hr_old
      · exact (hne_ut hep0).elim
      · have hc_old := hcomp.2.2.1 r0 (hs₁_tr ▸ hr_old) hep0
        simp only [GameState.record, hs₁_cp]; split_ifs <;> simp [hc_old]
    · intro Q sIdx hblk hvS
      by_cases hQ : Q = P
      · subst Q; simp only [GameState.record, Function.update_self] at hvS
        exact hvS'_blk sIdx hblk hvS
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
        exact hcomp.2.2.2.1 Q sIdx hblk hvS
    · intro Q sIdx
      by_cases hQ : Q = P
      · subst Q; simp only [GameState.record, Function.update_self, hvR']
        exact hcomp.2.2.2.2.1 P sIdx
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st]
        exact hcomp.2.2.2.2.1 Q sIdx
    · simpa only [hc_t] using hcomp.2.2.2.2.2
  · have hu_lt_t : u < t := by
      have hepP_lt := hpre.1 P
      omega
    have hep'_lt : ∀ Q, (s₁.record (2 + Δcka) P st' ⟨⟨P, u, s₁.idx P + 1⟩, pm, c⟩ false).epoch Q < t := by
      intro Q
      simp only [GameState.record]
      by_cases hQ : Q = P
      · subst Q; rw [hs₁_epP]; exact hu_lt_t
      · rw [hs₁_epQ Q hQ]; exact hpre.1 Q
    have hvR'_none : ∀ Q, ((s₁.record (2 + Δcka) P st' ⟨⟨P, u, s₁.idx P + 1⟩, pm, c⟩ false).st Q).vR t = none := by
      intro Q
      by_cases hQ : Q = P
      · subst Q; simp [GameState.record, hvR', hpre.2.2.2.1 P]
      · simp [GameState.record, Function.update_of_ne hQ, hs₁_st, hpre.2.2.2.1 Q]
    have hvS'_ne : ∀ Q sIdx, sIdx / q = t - healEpoch tL →
        ((s₁.record (2 + Δcka) P st' ⟨⟨P, u, s₁.idx P + 1⟩, pm, c⟩ false).st Q).vS ≠ some (.inr sIdx) := by
      intro Q sIdx hblk hvS
      by_cases hQ : Q = P
      · subst Q; simp only [GameState.record, Function.update_self] at hvS
        exact hvS'_blk sIdx hblk hvS
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
        exact hpre.2.2.2.2.1 Q sIdx hblk hvS
    have hσ'_clean : ∀ sIdx st, sIdx / q = t - healEpoch tL → σ' sIdx = some st →
        st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
        st.1.inTransit = [] ∧ st.1.lastSentIdx = 0 := by
      intro sIdx st hblk hst
      exact hpre.2.2.2.2.2.2 sIdx st hblk ((hσ_t sIdx hblk) ▸ hst)
    rcases hs₁_leak_cases with ⟨_, htL_eq⟩ | ⟨hL_eq, htL_eq⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hep'_lt,
        by simpa only [GameState.record, htL_eq] using hpre.2.1,
        by simpa only [postLeakDFBucket, GameState.record, htL_eq] using hpre.2.2.1,
        hvR'_none, hvS'_ne, hc_t.trans hpre.2.2.2.2.2.1, hσ'_clean⟩))
    · cases hlt_u : ltOpt tL u with
      | true =>
        exact Or.inl ⟨u, by simp [GameState.record, hL_eq], hlt_u, hu_lt_t⟩
      | false =>
        refine Or.inr (Or.inr (Or.inl ⟨hep'_lt, ?_, ?_, hvR'_none, hvS'_ne,
          hc_t.trans hpre.2.2.2.2.2.1, hσ'_clean⟩))
        · intro cur' hcur'
          simp only [GameState.record, htL_eq, Option.some.injEq] at hcur'
          subst hcur'
          cases htL_es : es.g.tL with
          | none => simpa [maxOpt] using hu_lt_t
          | some cur0 =>
            have h0 := hpre.2.1 cur0 htL_es
            simp only [maxOpt]; omega
        · cases tL with
          | none => simp [ltOpt] at hlt_u
          | some l =>
            simp only [ltOpt, decide_eq_false_iff_not, not_lt] at hlt_u
            cases htL_es : es.g.tL with
            | none =>
              simp [postLeakDFBucket, GameState.record, htL_eq, htL_es, maxOpt, ltOpt,
                Nat.not_lt.mpr hlt_u]
            | some cur0 =>
              have hpl0 := hpre.2.2.1
              simp only [postLeakDFBucket, htL_es, ltOpt, decide_eq_false_iff_not, not_lt] at hpl0
              simp only [postLeakDFBucket, GameState.record, htL_eq, htL_es, maxOpt, ltOpt,
                decide_eq_false_iff_not, not_lt]
              omega
  · rcases hidl with ⟨hdiv, hep, hct_idx, hvS_eq, hvS_all, hunused, hnone_tr, hsome, hvR, hvR_ge, hpin⟩
    have hs₀_eq : σ' s₀ = σ s₀ := hσ_t s₀ hdiv
    refine Or.inr (Or.inr (Or.inr ⟨s₀, hdiv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
    · simp only [GameState.record]
      exact le_trans hep (hs₁_ep_mono (Party.senderOf t))
    · intro r0 hr0 hep0
      simp only [GameState.record, List.mem_cons] at hr0
      rcases hr0 with rfl | hr_old
      · exact (hne_ut hep0).elim
      · exact hct_idx r0 (hs₁_tr ▸ hr_old) hep0
    · intro hep_rec
      simp only [GameState.record] at hep_rec
      by_cases hS : Party.senderOf t = P
      · exfalso; rw [hS, hs₁_epP] at hep_rec; exact hne_ut hep_rec
      · simp only [GameState.record, Function.update_of_ne hS, hs₁_st]
        rw [hs₁_epQ _ hS] at hep_rec
        exact hvS_eq hep_rec
    · intro Q sIdx hblk hvS
      by_cases hQ : Q = P
      · subst Q; simp only [GameState.record, Function.update_self] at hvS
        exact (hvS'_blk sIdx hblk hvS).elim
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hvS
        rcases hvS_all Q sIdx hblk hvS with ⟨rfl, rfl, hsends⟩
        refine ⟨rfl, rfl, fun hsIn => ?_⟩
        simp only [GameState.record, Function.update_of_ne hQ, hs₁_epQ _ hQ, hs₁_idxQ _ hQ, hs₀_eq] at hsIn ⊢
        exact hsends hsIn
    · intro sIdx st hblk hne hst
      exact hunused sIdx st hblk hne ((hσ_t sIdx hblk) ▸ hst)
    · intro hnone r0 hr0 hep0
      simp only [GameState.record, List.mem_cons] at hr0
      rcases hr0 with rfl | hr_old
      · exact hne_ut hep0
      · exact hnone_tr (hs₀_eq ▸ hnone) r0 (hs₁_tr ▸ hr_old) hep0
    · intro st hst
      have h5 := hsome st (hs₀_eq ▸ hst)
      refine ⟨h5.1, h5.2.1, ?_, ?_, ?_⟩
      · intro r0 hr0 hep0
        simp only [GameState.record, List.mem_cons] at hr0
        rcases hr0 with rfl | hr_old
        · exact (hne_ut hep0).elim
        · exact h5.2.2.1 r0 (hs₁_tr ▸ hr_old) hep0
      · intro hheal_g'
        simp only [GameState.record] at hheal_g'
        rcases h5.2.2.2.1 (hs₁_heal hheal_g') with ⟨hsc0, htr0⟩
        refine ⟨hsc0, fun r_fs hr_fs => ?_⟩
        rcases htr0 r_fs hr_fs with ⟨m0, hm0⟩
        exact ⟨m0, by simp [GameState.record, hs₁_tr, hm0]⟩
      · intro r0 hr0 hep0 hnc0
        simp only [GameState.record, List.mem_cons] at hr0
        rcases hr0 with rfl | hr_old
        · exact (hne_ut hep0).elim
        · have hnc_old : r0.pos ∉ es.g.comp := by
            intro hc; apply hnc0
            simp only [GameState.record, hs₁_cp]; split_ifs <;> simp [hc]
          exact h5.2.2.2.2 r0 (hs₁_tr ▸ hr_old) hep0 hnc_old
    · intro Q v0 hv0
      by_cases hQ : Q = P
      · subst Q; simp only [GameState.record, Function.update_self, hvR'] at hv0
        exact hvR P v0 hv0
      · simp only [GameState.record, Function.update_of_ne hQ, hs₁_st] at hv0
        exact hvR Q v0 hv0
    · intro hle_rec
      simp only [GameState.record] at hle_rec
      by_cases hR : Party.receiverOf t = P
      · have hle_old : t ≤ es.g.epoch P := by
          have h1 : t ≤ s₁.epoch P := hR ▸ hle_rec
          have h2 := hs₁_ep_le_succ
          have h3 : s₁.epoch P ≠ t := hs₁_epP ▸ hne_ut
          omega
        have hv0 := hvR_ge (hR.symm ▸ hle_old)
        simpa [GameState.record, hR, hvR'] using hv0
      · have hv0 := hvR_ge ((hs₁_epQ _ hR) ▸ hle_rec)
        simpa [GameState.record, Function.update_of_ne hR, hs₁_st] using hv0
    · intro ht_pos
      rcases hpin ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
      refine ⟨Tc, σc, k, hc_t ▸ hc_Tc, ?_, ?_⟩
      · intro hep_rec
        simp only [GameState.record] at hep_rec
        by_cases hS : Party.senderOf t = P
        · exfalso; rw [hS, hs₁_epP] at hep_rec; exact hne_ut hep_rec
        · simp only [GameState.record, Function.update_of_ne hS, hs₁_st]
          rw [hs₁_epQ _ hS] at hep_rec
          exact hcur_Tc hep_rec
      · intro r0 hr0 hep0
        simp only [GameState.record, List.mem_cons] at hr0
        rcases hr0 with rfl | hr_old
        · exact (hne_ut hep0).elim
        · exact htr_Tc r0 (hs₁_tr ▸ hr_old) hep0

/-! ## 2. `corrEPaperBucket` Step Preservation -/

theorem corrEPaperBucket_bucket_step
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
    (hrv_spec : ∀ ctx P vp hs rc σ w,
      w ∈ support (runPubIdeal C ℓ encT idOf N false ((hk.reveal ctx P vp).run hs) rc σ) →
      (w.1.1.1 = none) ∨
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).reveal
          ctx P vp).run hs) rc σ))
    (rem' : ℕ) (P : Party)
    (es : BucketEState Pt ℓ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hact : BucketActive q Δcka Δbucket qep tL par (rem' + 1) (es, none) σ)
    (w : ((Option (Fig8St Pt) × BucketEState Pt ℓ) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((corrEPaperBucket hk P).run es) rc σ)) :
    w.1.1.2.abort = true ∨
    (w.1.1.2.g.win = false ∧ BucketActive q Δcka Δbucket qep tL par rem' (w.1.1.2, none) w.2) := by
  let _ := hq
  dsimp only [BucketActive] at hact ⊢
  rcases hact with ⟨_, hwf, hep_inv⟩
  simp only [corrEPaperBucket, StateT.run_bind, StateT.run_get, pure_bind] at hw
  split_ifs at hw with hguard
  · simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hw
    subst hw
    exact Or.inr ⟨hwf.hwin, rfl, GlobalBucketWF_mono_rem hwf (Nat.le_succ rem'), hep_inv⟩
  · have h_liftH : (liftH (hk.reveal es.g P (es.g.st P))).run es =
        ((hk.reveal es.g P (es.g.st P)).run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl
    simp only [StateT.run_bind, h_liftH, runPubIdeal, simulateQ_bind,
      MonadAttach.mem_support_bind] at hw
    rcases hw with ⟨w_rv, ⟨w_h, hw_h, hw_lp⟩, hw_fin⟩
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_lp
    subst hw_lp
    rcases hrv_spec es.g P (es.g.st P) es.h rc σ w_h hw_h with hnone_rv | hw_h_std
    · simp only [hnone_rv, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
      subst hw_fin; exact Or.inl rfl
    · dsimp only [hooksFSMultiDFBucketPaper] at hw_h_std
      let l_corr := max (es.g.epoch .A) (es.g.epoch .B)
      have hafter_tL_mem : ∀ cur, (es.g.afterCorr P).tL = some cur → cur ∈ (es.g.afterCorr P).leaks := by
        intro cur hcur
        unfold GameState.afterCorr at hcur ⊢
        exact tL_mem_of_leak l_corr hwf.htL_mem cur hcur
      have hafter_heal : ∀ t, healedBy (es.g.afterCorr P).tL (2 + Δcka) t = true →
          healedBy es.g.tL (2 + Δcka) t = true := by
        intro t hh
        unfold GameState.afterCorr at hh
        exact healedBy_of_leak _ l_corr (2 + Δcka) t hh
      -- Helper preserving `EpochInv` at `t` when `σ'` agrees with `σ` on block `t - healEpoch tL`:
      have hpres_untouched : ∀ (hs' : FSMultiDFBucketState Pt _ _ _ _)
          (σ' : ℕ → Option (IdealHSt Pt ℓ)) (t : ℕ),
          IsTargetEpoch Δcka Δbucket qep tL par t →
          hs'.cache = es.h.cache →
          (∀ sIdx, sIdx / q = t - healEpoch tL → σ' sIdx = σ sIdx) →
          EpochInv q Δcka tL t { es with g := es.g.afterCorr P, h := hs' } σ' := by
        intro hs' σ' t ht hc_eq hσ_blk
        rcases hep_inv t ht with hbad | hcomp | hpre | ⟨s₀, hidl⟩
        · exact Or.inl (EpochBad.of_sub_leaks hbad fun lk hlk => by
            simp [GameState.afterCorr, GameState.leak, hlk])
        · refine Or.inr (Or.inl ⟨hcomp.1, ?_, ?_, hcomp.2.2.2.1, hcomp.2.2.2.2.1,
            by simpa only [hc_eq] using hcomp.2.2.2.2.2⟩)
          · rcases hcomp.2.1 with ⟨cur0, hcur0, hle0⟩
            exact ⟨max cur0 l_corr, by simp [GameState.afterCorr, GameState.leak, maxOpt, hcur0, l_corr],
              le_trans hle0 (Nat.le_max_left _ _)⟩
          · intro r0 hr0 hep0
            have hc0 := hcomp.2.2.1 r0 hr0 hep0
            simp [GameState.afterCorr, GameState.leak, hc0]
        · have hl_lt_t : l_corr < t :=
            Nat.max_lt.mpr ⟨hpre.1 .A, hpre.1 .B⟩
          have hlk'_lt_t : maxOpt es.g.tL l_corr < t := by
            cases htL_es : es.g.tL with
            | none => simpa [maxOpt] using hl_lt_t
            | some cur0 => simpa [maxOpt] using Nat.max_lt.mpr ⟨hpre.2.1 cur0 htL_es, hl_lt_t⟩
          cases hlt_c : ltOpt tL (maxOpt es.g.tL l_corr) with
          | true =>
            exact Or.inl ⟨maxOpt es.g.tL l_corr,
              by simp [GameState.afterCorr, GameState.leak, l_corr], hlt_c, hlk'_lt_t⟩
          | false =>
            refine Or.inr (Or.inr (Or.inl ⟨hpre.1, ?_,
              by simpa [postLeakDFBucket, GameState.afterCorr, GameState.leak, l_corr] using hlt_c,
              hpre.2.2.2.1, hpre.2.2.2.2.1,
              by simpa only [hc_eq] using hpre.2.2.2.2.2.1,
              fun sIdx st hblk hst => hpre.2.2.2.2.2.2 sIdx st hblk ((hσ_blk sIdx hblk) ▸ hst)⟩))
            intro cur' hcur'
            simp only [GameState.afterCorr, GameState.leak, Option.some.injEq] at hcur'
            subst hcur'
            exact hlk'_lt_t
        · rcases hidl with ⟨hdiv, hep, hct_idx, hvS_eq, hvS_all, hunused, hnone_tr, hsome, hvR, hvR_ge, hpin⟩
          have hs₀_eq : σ' s₀ = σ s₀ := hσ_blk s₀ hdiv
          refine Or.inr (Or.inr (Or.inr ⟨s₀, hdiv, hep, hct_idx, hvS_eq, ?_, ?_,
            hs₀_eq ▸ hnone_tr, ?_, hvR, hvR_ge,
            fun hpos => by simpa only [hc_eq, GameState.afterCorr, GameState.leak] using hpin hpos⟩))
          · intro Q sIdx hblk hvS
            rcases hvS_all Q sIdx hblk hvS with ⟨hQ, hsIdx, hsends⟩
            exact ⟨hQ, hsIdx, hs₀_eq ▸ hsends⟩
          · intro sIdx st hblk hne hst
            exact hunused sIdx st hblk hne ((hσ_blk sIdx hblk) ▸ hst)
          · intro st hst
            have h5 := hsome st (hs₀_eq ▸ hst)
            refine ⟨h5.1, h5.2.1, h5.2.2.1, fun hh => h5.2.2.2.1 (hafter_heal t hh),
              fun r0 hr0 hep0 hnc0 => h5.2.2.2.2 r0 hr0 hep0 ?_⟩
            intro hc; apply hnc0; simp [GameState.afterCorr, GameState.leak, hc]
      cases hvSP : (es.g.st P).vS with
      | none =>
        simp only [hvSP, pure_bind] at hw_h_std
        split at hw_h_std <;> simp only [StateT.run_pure, runPubIdeal, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hw_h_std <;> subst hw_h_std
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
          subst hw_fin; exact Or.inl rfl
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
          subst hw_fin; dsimp only
          refine Or.inr ⟨hwf.hwin, rfl, {
            habort := hwf.habort, hwin := hwf.hwin, hid := hwf.hid, htcur := hwf.htcur,
            htL_mem := hafter_tL_mem, hsess_zero := hwf.hsess_zero,
            hsess_pos := fun u hu => by dsimp only; have := hwf.hsess_pos u hu; omega,
            hcache_blk := hwf.hcache_blk, hvR_blk := hwf.hvR_blk, hvS_blk := hwf.hvS_blk,
            htrans_wf := hwf.htrans_wf },
            fun t ht => hpres_untouched es.h σ t ht rfl (fun _ _ => rfl)⟩
      | some vS0 =>
        cases vS0 with
        | inl ss =>
          simp only [hvSP, pure_bind] at hw_h_std
          split at hw_h_std <;> simp only [StateT.run_pure, runPubIdeal, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hw_h_std <;> subst hw_h_std
          · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
            subst hw_fin; exact Or.inl rfl
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
            subst hw_fin; dsimp only
            refine Or.inr ⟨hwf.hwin, rfl, {
              habort := hwf.habort, hwin := hwf.hwin, hid := hwf.hid, htcur := hwf.htcur,
              htL_mem := hafter_tL_mem, hsess_zero := hwf.hsess_zero,
              hsess_pos := fun u hu => by dsimp only; have := hwf.hsess_pos u hu; omega,
              hcache_blk := hwf.hcache_blk, hvR_blk := hwf.hvR_blk, hvS_blk := hwf.hvS_blk,
              htrans_wf := hwf.htrans_wf },
              fun t ht => hpres_untouched es.h σ t ht rfl (fun _ _ => rfl)⟩
        | inr sIdx =>
          rcases hwf.hvS_blk P sIdx hvSP with ⟨u_P, huP_le, _, hP_eq, hbuck_uP, hle_qep_uP, hdiv_uP⟩
          simp only [hvSP, StateT.run_bind] at hw_h_std
          rcases runPubIdeal_liftFSMultiDFBucket_corruptSender_support C ℓ encT idOf N sIdx es.h _
              rc σ w_h hw_h_std with ⟨u, hu, hwu⟩
          rcases u with ⟨res_cs, st_cs⟩
          cases res_cs with
          | none =>
            simp only [StateT.run_pure, pure_bind, runPubIdeal, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hwu
            subst hwu
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
            subst hw_fin; exact Or.inl rfl
          | some ss_out =>
            simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hwu
            split at hwu <;> simp only [StateT.run_pure, runPubIdeal, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hwu <;> subst hwu
            · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin; exact Or.inl rfl
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fin
              subst hw_fin; dsimp only
              refine Or.inr ⟨hwf.hwin, rfl, {
                habort := hwf.habort, hwin := hwf.hwin, hid := hwf.hid, htcur := hwf.htcur,
                htL_mem := hafter_tL_mem, hsess_zero := hwf.hsess_zero,
                hsess_pos := fun u' hu' => by dsimp only; have := hwf.hsess_pos u' hu'; omega,
                hcache_blk := hwf.hcache_blk, hvR_blk := hwf.hvR_blk, hvS_blk := hwf.hvS_blk,
                htrans_wf := hwf.htrans_wf }, ?_⟩
              intro t ht
              by_cases heq_ut : u_P = t
              · subst heq_ut
                rcases hep_inv u_P ht with hbad | hcomp | hpre | ⟨s₀, hidl⟩
                · exact Or.inl (EpochBad.of_sub_leaks hbad fun lk hlk => by
                    simp [GameState.afterCorr, GameState.leak, hlk])
                · exact (hcomp.2.2.2.1 P sIdx hdiv_uP hvSP).elim
                · exact (hpre.2.2.2.2.1 P sIdx hdiv_uP hvSP).elim
                · rcases hidl with ⟨hdiv, hep, hct_idx, hvS_eq, hvS_all, hunused, hnone_tr, hsome, hvR, hvR_ge, hpin⟩
                  rcases hvS_all P sIdx hdiv_uP hvSP with ⟨_, rfl, _⟩
                  have hnot_heal_after : healedBy (es.g.afterCorr P).tL (2 + Δcka) u_P = false := by
                    have hle_c : u_P ≤ l_corr := by
                      cases P <;> simp only [l_corr] <;> omega
                    cases htL_es : es.g.tL <;>
                      simp [GameState.afterCorr, GameState.leak, maxOpt, htL_es, healedBy] <;> omega
                  -- Extract `corruptSenderH` postcondition on `sIdx`:
                  let bk1 :=
                    let bk0 := (es.h.book sIdx).getD {}
                    some { bk0 with sCorr := true }
                  have hcs_clean : ∀ (st₀ st_new : IdealHSt Pt ℓ),
                      st_cs = some st_new →
                      st₀.1.ended = false →
                      (σ sIdx = none → st₀.1.lastSentIdx = 0 ∧ ∀ r0 ∈ es.g.trans, r0.pos.epoch ≠ u_P) →
                      (∀ st_ex, σ sIdx = some st_ex → st₀ = st_ex) →
                      (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) →
                      (∀ r0 ∈ es.g.trans, r0.pos.epoch = u_P → r0.pos.idx ≤ st₀.1.lastSentIdx) →
                      (∀ r0 ∈ es.g.trans, r0.pos.epoch = u_P → r0.pos ∉ es.g.comp →
                        st₀.1.isCompromised r0.pos.idx = false ∧
                        (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r0.pos.idx → (r_fs.ad.1, r_fs.ct) = r0.ct)) →
                      (some ss_out, st_new) ∈ support (StateT.run (m := ProbComp) (corruptSenderH (lChainPRG C.F) (hpIdeal N false) ()) st₀) →
                      EpochInv q Δcka tL u_P
                        { es with
                            g := es.g.afterCorr P,
                            h := { es.h with book := Function.update es.h.book sIdx bk1 } }
                        (Function.update σ sIdx st_cs) := by
                    intro st₀ st_new hcs_eq hend₀ hif_none hif_some hit₀ hidx₀ hunc₀ hu_cs
                    subst hcs_eq
                    rcases corruptSenderH_hpIdeal_false_step_spec (lChainPRG C.F) N st₀ st_new (some ss_out)
                        hend₀ hu_cs with ⟨_, hend₁, hsc₁, hls₁, hit₁⟩
                    refine Or.inr (Or.inr (Or.inr ⟨sIdx, hdiv, hep, hct_idx, hvS_eq, ?_, ?_,
                      by intro h; simp at h, ?_, hvR, hvR_ge,
                      fun hpos => by simpa only [GameState.afterCorr, GameState.leak] using hpin hpos⟩))
                    · intro Q idx hblkQ hvSQ
                      rcases hvS_all Q idx hblkQ hvSQ with ⟨rfl, rfl, hsendQ⟩
                      refine ⟨rfl, rfl, fun hsIn => ?_⟩
                      rcases hsendQ hsIn with ⟨hep_t, ⟨hnone, hidx0⟩ | ⟨st_ex, hsome_ex, hls_ex⟩⟩
                      · exact ⟨hep_t, Or.inr ⟨st_new, by simp, hls₁.trans ((hif_none hnone).1.trans hidx0.symm)⟩⟩
                      · cases hif_some st_ex hsome_ex
                        exact ⟨hep_t, Or.inr ⟨st_new, by simp, hls₁.trans hls_ex⟩⟩
                    · intro idx st hblk_i hne_i hst_i
                      rw [Function.update_of_ne hne_i] at hst_i
                      exact hunused idx st hblk_i hne_i hst_i
                    · intro st hst
                      simp only [Function.update_self, Option.some.injEq] at hst
                      subst hst
                      refine ⟨hend₁, ?_, ?_, ?_, ?_⟩
                      · intro r_fs hr_fs; rw [hit₁] at hr_fs; rw [hls₁]; exact hit₀ r_fs hr_fs
                      · intro r0 hr0 hep0
                        dsimp only at hr0
                        exact hls₁ ▸ hidx₀ r0 hr0 hep0
                      · intro hh
                        dsimp only at hh
                        rw [hnot_heal_after] at hh
                        cases hh
                      · intro r0 hr0 hep0 hnc0
                        dsimp only at hr0 hnc0
                        have hnc_old : r0.pos ∉ es.g.comp := by
                          intro hc; apply hnc0; simp [GameState.afterCorr, GameState.leak, hc]
                        rcases hunc₀ r0 hr0 hep0 hnc_old with ⟨hc_f, hct_m⟩
                        have hle_ls := hidx₀ r0 hr0 hep0
                        refine ⟨?_, fun r_fs hr_fs => hct_m r_fs (hit₁ ▸ hr_fs)⟩
                        cases hsc0 : st₀.1.senderCorruptedAt with
                        | none => simp [HState.isCompromised, hsc₁, hsc0, Nat.not_lt.mpr hle_ls]
                        | some j0 => simpa [HState.isCompromised, hsc₁, hsc0] using hc_f
                  cases hσ0 : σ sIdx with
                  | none =>
                    rw [hσ0] at hu
                    simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
                      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
                    rcases hu with ⟨b, _, ⟨v0_1, v0_2⟩, hv0, hpair⟩
                    injection hpair with hv0_1 hv0_2
                    subst hv0_1
                    exact hcs_clean (hInit b .unknown) v0_2 hv0_2 rfl
                      (fun _ => ⟨rfl, hnone_tr hσ0⟩) (fun _ h => by simp [hσ0] at h) (by simp [hInit])
                      (fun r0 hr0 hep0 => (hnone_tr hσ0 r0 hr0 hep0).elim)
                      (fun r0 hr0 hep0 _ => (hnone_tr hσ0 r0 hr0 hep0).elim) hv0
                  | some st₀ =>
                    rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
                    rcases hu with ⟨⟨v0_1, v0_2⟩, hv0, hvu⟩
                    simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
                    injection hvu with hv0_1 hv0_2
                    subst hv0_1
                    have h5 := hsome st₀ hσ0
                    exact hcs_clean st₀ v0_2 hv0_2 h5.1 (fun h => by simp [hσ0] at h)
                      (fun _ h => Option.some.inj (hσ0.symm.trans h)) h5.2.1 h5.2.2.1 h5.2.2.2.2 hv0
              · apply hpres_untouched _ _ t ht rfl
                intro j hj_blk
                have hne_j : j ≠ sIdx := by
                  intro rfl
                  exact heq_ut (block_eq_imp_epoch_eq hΔb hbuck_uP ht.1 hdiv_uP hj_blk)
                exact Function.update_of_ne hne_j _ _

end BucketStep

end

end Computational.Proofs.E2E.SessionAuthMultiEndBucketCorr

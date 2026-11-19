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

/-!
# Ideal-Cutoff `fsSend` and Unified `vRecv` Step Lemmas for `DeliverForgePaperMultiBucket`

Proves:
1. `GlobalBucketWF_mono_rem` and `BucketActive_mono_rem`.
2. `fsSend_inr_bucket_step_post`: target-epoch ideal `fsSend` step lemma (`la = false`).
3. `EpochInv.accept_ne` and `vRecv_bucket_step`: unified `vRecv` + `accept` preservation of
   `BucketActive` (`rem' + 1 → rem'`) for both `hooksFSMultiDFBucketPaper` and
   `hooksFSMultiDFBucketPaperMode`.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEndBucketRecv

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.SM (Pos Record GameState healedBy)
open _root_.CryptoGames.SM.Construction (
  Header FSMultiSpec FSMultiDFBucketState FSMultiBook
  liftFSMultiDFBucket hooksFSMultiDFBucketPaper
  inStage2BucketGen postLeakDFBucket healEpoch)
open _root_.CryptoGames.SM.Engine (Ctx VP Hooks vRecv)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (
  LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lFS lIdeal lAeadR lChainPRG)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (
  lazyInit_run_none' lazyInit_run_some')
open _root_.CryptoVerification.E2E.Signed.SessionWire (hpIdeal)
open _root_.CryptoGames.FSAEAD.Thm5 (
  HState DG transmitHWith corruptSenderH hInit)
open Computational.Proofs.E2E.SessionAuthMultiEnd (
  IdealHSt runPubIdeal isCompromised_of_senderCorruptedAt_none)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketLa (CoinOnly)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketSteps (
  BucketEState IsTargetEpoch EpochBad EpochCompEntry EpochPre EpochIdealAt EpochIdeal EpochInv
  GlobalBucketWF BucketActive BucketInv
  healEpoch_le_of_inStage2BucketGen healedBy_iff_postLeakDFBucket_false
  transmitHWith_hpIdeal_false_step_spec corruptSenderH_hpIdeal_false_step_spec
  runPubIdeal_liftFSMultiDFBucket_transmit_support
  runPubIdeal_liftFSMultiDFBucket_corruptSender_support)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketHooks (
  EpochCleanAt fsRecv_inr_bucket_any_support
  fsRecv_inr_bucket_forged_not_nontrivial fsRecv_inr_bucket_step_post)

section BucketRecv

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## 1. Budget Weakening & Target-Epoch `fsSend` Step Lemma -/

theorem GlobalBucketWF_mono_rem {ℓ : ℕ}
    {q Δbucket qep : ℕ} {tL : Option ℕ} {par : Bool} {rem₁ rem₂ : ℕ}
    {es : BucketEState Pt ℓ}
    (h : GlobalBucketWF q Δbucket qep tL par rem₂ es) (hle : rem₁ ≤ rem₂) :
    GlobalBucketWF q Δbucket qep tL par rem₁ es where
  habort := h.habort
  hwin := h.hwin
  hid := h.hid
  htcur := h.htcur
  htL_mem := h.htL_mem
  hsess_zero := h.hsess_zero
  hsess_pos := fun u hu => by have := h.hsess_pos u hu; omega
  hcache_blk := h.hcache_blk
  hvR_blk := h.hvR_blk
  hvS_blk := h.hvS_blk
  htrans_wf := h.htrans_wf

theorem BucketActive_mono_rem {ℓ : ℕ}
    {q Δcka Δbucket qep : ℕ} {tL : Option ℕ} {par : Bool} {rem₁ rem₂ : ℕ}
    {st : BucketEState Pt ℓ × Option ℕ} {σ : ℕ → Option (IdealHSt Pt ℓ)}
    (h : BucketActive q Δcka Δbucket qep tL par rem₂ st σ) (hle : rem₁ ≤ rem₂) :
    BucketActive q Δcka Δbucket qep tL par rem₁ st σ :=
  ⟨h.1, GlobalBucketWF_mono_rem h.2.1 hle, h.2.2⟩

theorem BucketInv_mono_rem {ℓ : ℕ}
    {q Δcka Δbucket qep : ℕ} {tL : Option ℕ} {par : Bool} {rem₁ rem₂ : ℕ}
    {st : BucketEState Pt ℓ × Option ℕ} {σ : ℕ → Option (IdealHSt Pt ℓ)}
    (h : BucketInv q Δcka Δbucket qep tL par rem₂ st σ) (hle : rem₁ ≤ rem₂) :
    BucketInv q Δcka Δbucket qep tL par rem₁ st σ := by
  rcases h with hab | hwon | hact
  · exact Or.inl hab
  · exact Or.inr (Or.inl hwon)
  · exact Or.inr (Or.inr (BucketActive_mono_rem hact hle))

theorem fsSend_inr_bucket_step_post
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t s₀ : ℕ)
    (s₁ : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (hs₁ : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hep_s₁ : s₁.epoch (Party.senderOf t) = t)
    (hs₀_pre :
      (σ s₀ = none ∧ s₁.idx (Party.senderOf t) = 0 ∧ (∀ r ∈ s₁.trans, r.pos.epoch ≠ t)) ∨
      (∃ st₀, σ s₀ = some st₀ ∧
        st₀.1.ended = false ∧
        st₀.1.lastSentIdx = s₁.idx (Party.senderOf t) ∧
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
        (healedBy s₁.tL (2 + Δcka) t = true →
          st₀.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₀.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ s₁.trans)) ∧
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos ∉ s₁.comp →
          st₀.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))))
    (w : ((Option ((RatchetSenderState (BitVec 256) ⊕ ℕ) ×
        (ℕ × LibsignalCiphertextWithSalt32)) × _) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).fsSend
        s₁ (Party.senderOf t) t (.inr s₀) hdr pm none).run hs₁) rc σ)) :
    w.1.1.1 = none ∨
    ∃ rawCt st₂,
      let e := (s₁.idx (Party.senderOf t) + 1, rawCt)
      w.1.1.1 = some (.inr s₀, e) ∧
      w.1.1.2.cache = hs₁.cache ∧
      w.1.1.2.sessions = hs₁.sessions ∧
      w.2 = Function.update σ s₀ (some st₂) ∧
      st₂.1.ended = false ∧
      st₂.1.lastSentIdx = s₁.idx (Party.senderOf t) + 1 ∧
      (∀ r_fs ∈ st₂.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₂.1.lastSentIdx) ∧
      (∀ st',
        let g' := s₁.record (2 + Δcka) (Party.senderOf t) st'
          ⟨⟨Party.senderOf t, t, s₁.idx (Party.senderOf t) + 1⟩, pm, (hdr, e)⟩ false
        (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos.idx ≤ st₂.1.lastSentIdx) ∧
        (healedBy g'.tL (2 + Δcka) t = true →
          st₂.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₂.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ g'.trans)) ∧
        (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos ∉ g'.comp →
          st₂.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₂.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) := by
  let PostSend : Prop := w.1.1.1 = none ∨ ∃ rawCt st₂,
    let e := (s₁.idx (Party.senderOf t) + 1, rawCt);
    w.1.1.1 = some (.inr s₀, e) ∧ w.1.1.2.cache = hs₁.cache ∧ w.1.1.2.sessions = hs₁.sessions ∧
    w.2 = Function.update σ s₀ (some st₂) ∧ st₂.1.ended = false ∧
    st₂.1.lastSentIdx = s₁.idx (Party.senderOf t) + 1 ∧
    (∀ r_fs ∈ st₂.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₂.1.lastSentIdx) ∧
    (∀ st',
      let g' := s₁.record (2 + Δcka) (Party.senderOf t) st'
        ⟨⟨Party.senderOf t, t, s₁.idx (Party.senderOf t) + 1⟩, pm, (hdr, e)⟩ false;
      (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos.idx ≤ st₂.1.lastSentIdx) ∧
      (healedBy g'.tL (2 + Δcka) t = true → st₂.1.senderCorruptedAt = none ∧
        (∀ r_fs ∈ st₂.1.inTransit, ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ g'.trans)) ∧
      (∀ r ∈ g'.trans, r.pos.epoch = t → r.pos ∉ g'.comp → st₂.1.isCompromised r.pos.idx = false ∧
        (∀ r_fs ∈ st₂.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)))
  dsimp only [hooksFSMultiDFBucketPaper] at hw
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
  have htr_tail : ∀ hs_mid rc_mid σ_mid,
      hs_mid.cache = hs₁.cache → hs_mid.sessions = hs₁.sessions → (∀ j, j ≠ s₀ → σ_mid j = σ j) →
      ((σ_mid s₀ = none ∧ s₁.idx (Party.senderOf t) = 0 ∧ (∀ r ∈ s₁.trans, r.pos.epoch ≠ t)) ∨
        ∃ st₁, σ_mid s₀ = some st₁ ∧ st₁.1.ended = false ∧ st₁.1.lastSentIdx = s₁.idx (Party.senderOf t) ∧
          (∀ r_fs ∈ st₁.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₁.1.lastSentIdx) ∧
          (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos.idx ≤ st₁.1.lastSentIdx) ∧
          (healedBy s₁.tL (2 + Δcka) t = true → st₁.1.senderCorruptedAt = none ∧
            (∀ r_fs ∈ st₁.1.inTransit, ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ s₁.trans)) ∧
          (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos ∉ s₁.comp → st₁.1.isCompromised r.pos.idx = false ∧
            (∀ r_fs ∈ st₁.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) →
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        ((liftFSMultiDFBucket s₀ (CryptoGames.FSAEAD.transmitQuery hdr pm)).run hs_mid >>= fun p =>
          StateT.run (match p.1 with
          | none => pure none
          | some e => do
            modify fun (s : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) =>
              let b := (s.book s₀).getD {}
              let cnt' := b.fsCount + 1
              let b' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
              { s with book := Function.update s.book s₀ (some b') }
            pure (some ((Sum.inr s₀ : RatchetSenderState (BitVec 256) ⊕ ℕ), e))) p.2) rc_mid σ_mid) → PostSend := by
    intro hs_mid rc_mid σ_mid hcache_mid hse_mid hσ_ne hst₁_pre hw_tr
    rcases runPubIdeal_liftFSMultiDFBucket_transmit_support C ℓ encT idOf N s₀ hdr pm hs_mid _
        rc_mid σ_mid w hw_tr with ⟨u, hu, hwu⟩
    have htr_from : ∀ (st₁ : IdealHSt Pt ℓ) (v0 : Option (ℕ × LibsignalCiphertextWithSalt32) × IdealHSt Pt ℓ),
        u = (v0.1, some v0.2) → st₁.1.ended = false → st₁.1.lastSentIdx = s₁.idx (Party.senderOf t) →
        (∀ r_fs ∈ st₁.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₁.1.lastSentIdx) →
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos.idx ≤ st₁.1.lastSentIdx) →
        (healedBy s₁.tL (2 + Δcka) t = true → st₁.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₁.1.inTransit, ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ s₁.trans)) →
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos ∉ s₁.comp → st₁.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₁.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)) →
        (v0.1, v0.2) ∈ support (StateT.run (m := ProbComp) (transmitHWith (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F)
          (hpIdeal N false) (DG (lChainPRG C.F)) none ((hdr, pm.1), pm.2)) st₁) → PostSend := by
      intro st₁ v0 hu_eq hend₁ hls₁ hit₁ hidx₁ hheal₁ huncomp₁ hu_spec
      subst hu_eq
      rcases transmitHWith_hpIdeal_false_step_spec _ _ _ N ((hdr, pm.1), pm.2) st₁ v0.2 v0.1
          hend₁ hu_spec with ⟨rawCt, hu1, hend₂, hsc₂, hls₂, hit₂⟩
      simp only [hu1, hls₁, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hwu
      subst hwu
      have hupd_eq : Function.update σ_mid s₀ (some v0.2) = Function.update σ s₀ (some v0.2) := by
        ext j; by_cases hj : j = s₀
        · subst hj; simp
        · simp [Function.update_of_ne hj, hσ_ne j hj]
      refine Or.inr ⟨rawCt, v0.2, rfl, hcache_mid, hse_mid, hupd_eq, hend₂,
        hls₂.trans (congrArg (· + 1) hls₁), ?_, ?_⟩
      · intro r_fs hr_fs
        rw [hit₂, List.mem_cons] at hr_fs
        rcases hr_fs with rfl | hr_old
        · exact ⟨rfl, by rw [hls₂]⟩
        · rcases hit₁ r_fs hr_old with ⟨h1, h2⟩
          exact ⟨h1, by rw [hls₂]; omega⟩
      · intro st'
        refine ⟨?_, ?_, ?_⟩
        · intro r hr hep
          simp only [GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr_old
          · rw [hls₂, hls₁]
          · have := hidx₁ r hr_old hep; rw [hls₂]; omega
        · intro hheal_g'
          rcases hheal₁ hheal_g' with ⟨hsc₁, htr₁⟩
          refine ⟨hsc₂.trans hsc₁, fun r_fs hr_fs => ?_⟩
          rw [hit₂, List.mem_cons] at hr_fs
          rcases hr_fs with rfl | hr_old
          · exact ⟨pm, by simp [GameState.record, hls₁]⟩
          · rcases htr₁ r_fs hr_old with ⟨m0, hm0⟩
            exact ⟨m0, by simp [GameState.record, hm0]⟩
        · intro r hr hep hnc
          simp only [GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr_old
          · have hsafe : s₁.safeCh (2 + Δcka) (Party.senderOf t) = true := by
              by_contra hns; simp only [Bool.not_eq_true] at hns; simp [GameState.record, hns] at hnc
            have hheal_s₁ : healedBy s₁.tL (2 + Δcka) t = true := by
              simpa [GameState.safeCh, hep_s₁] using hsafe
            have hsc₁ := (hheal₁ hheal_s₁).1
            refine ⟨isCompromised_of_senderCorruptedAt_none v0.2.1 (hsc₂.trans hsc₁) _, ?_⟩
            intro r_fs hr_fs hidx_eq
            rw [hit₂, List.mem_cons] at hr_fs
            rcases hr_fs with rfl | hr_old
            · simp [hls₁]
            · have := (hit₁ r_fs hr_old).2
              simp only [hls₁] at this hidx_eq; omega
          · have hnc_s₁ : r.pos ∉ s₁.comp := by
              intro hc; apply hnc
              simp only [GameState.record]; split_ifs <;> simp [hc]
            rcases huncomp₁ r hr_old hep hnc_s₁ with ⟨hc_false, hct_match⟩
            refine ⟨by simpa [HState.isCompromised, hsc₂] using hc_false, ?_⟩
            intro r_fs hr_fs hidx_eq
            rw [hit₂, List.mem_cons] at hr_fs
            rcases hr_fs with rfl | hr_fs_old
            · have := hidx₁ r hr_old hep
              simp only at hidx_eq; omega
            · exact hct_match r_fs hr_fs_old hidx_eq
    rcases hst₁_pre with ⟨hnone, hidx0, hno_t⟩ | ⟨st₁, hsome, h1, h2, h3, h4, h5, h6⟩
    · rw [hnone] at hu
      simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
      rcases hu with ⟨b, _, v0, hv0, hu_eq⟩
      exact htr_from (hInit b .unknown) v0 hu_eq rfl hidx0.symm (by simp [hInit])
        (fun r hr hep => (hno_t r hr hep).elim) (fun _ => ⟨rfl, by simp [hInit]⟩)
        (fun r hr hep _ => (hno_t r hr hep).elim) hv0
    · rw [hsome, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
      rcases hu with ⟨v0, hv0, hvu⟩
      simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
      exact htr_from st₁ v0 hvu h1 h2 h3 h4 h5 h6 hv0
  by_cases hcond : (!(s₁.safeCh (2 + Δcka) (Party.senderOf t)) && !((hs₁.book s₀).getD {}).sCorr) = true
  · have hnot_heal : healedBy s₁.tL (2 + Δcka) t = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      simpa [GameState.safeCh, hep_s₁] using hcond.1
    simp only [hcond, ↓reduceIte, StateT.run_bind] at hw
    rcases runPubIdeal_liftFSMultiDFBucket_corruptSender_support C ℓ encT idOf N s₀ hs₁ _ rc σ w hw with
      ⟨u, hu, hwu⟩
    have hcs_from : ∀ (st₀ : IdealHSt Pt ℓ) (v0 : Option (RatchetSenderState (BitVec 256)) × IdealHSt Pt ℓ),
        u = (v0.1, some v0.2) → st₀.1.ended = false → st₀.1.lastSentIdx = s₁.idx (Party.senderOf t) →
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) →
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) →
        (∀ r ∈ s₁.trans, r.pos.epoch = t → r.pos ∉ s₁.comp → st₀.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)) →
        (v0.1, v0.2) ∈ support (StateT.run (m := ProbComp)
          (corruptSenderH (lChainPRG C.F) (hpIdeal N false) ()) st₀) → PostSend := by
      intro st₀ v0 hu_eq hend₀ hls₀ hit₀ hidx₀ huncomp₀ hu_cs
      subst hu_eq
      rcases corruptSenderH_hpIdeal_false_step_spec (lChainPRG C.F) N st₀ v0.2 v0.1 hend₀ hu_cs with
        ⟨hsome_res, hend₁, hsc₁, hls₁, hit₁⟩
      rcases Option.isSome_iff_exists.mp hsome_res with ⟨ss_out, hu1⟩
      simp only [hu1, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_modify, pure_bind] at hwu
      let hs_mid := { hs₁ with
        book := Function.update hs₁.book s₀ (some { (hs₁.book s₀).getD {} with sCorr := true }) }
      refine htr_tail hs_mid rc (Function.update σ s₀ (some v0.2)) rfl rfl
        (fun j hj => by simp [Function.update_of_ne hj])
        (Or.inr ⟨v0.2, by simp, hend₁, hls₁.trans hls₀, ?_, ?_, ?_, ?_⟩) (by
          refine Eq.mp (congrArg (fun k => w ∈ support (runPubIdeal C ℓ encT idOf N false k rc
            (Function.update σ s₀ (some v0.2)))) ?_) hwu
          congr 1; funext p; rcases p with ⟨_ | e, hs'⟩ <;>
            simp [StateT.run_map, StateT.run_modify, StateT.run_pure])
      · intro r_fs hr_fs; rw [hit₁] at hr_fs; rw [hls₁]; exact hit₀ r_fs hr_fs
      · intro r hr hep; rw [hls₁]; exact hidx₀ r hr hep
      · intro hheal; rw [hnot_heal] at hheal; cases hheal
      · intro r hr hep hnc
        rcases huncomp₀ r hr hep hnc with ⟨hc_false, hct_m⟩
        have hle_ls : r.pos.idx ≤ st₀.1.lastSentIdx := hidx₀ r hr hep
        refine ⟨?_, fun r_fs hr_fs => hct_m r_fs (hit₁ ▸ hr_fs)⟩
        cases hsc0 : st₀.1.senderCorruptedAt with
        | none => simp [HState.isCompromised, hsc₁, hsc0, Nat.not_lt.mpr hle_ls]
        | some _ => simpa [HState.isCompromised, hsc₁, hsc0] using hc_false
    rcases hs₀_pre with ⟨hnone, hidx0, hno_t⟩ | ⟨st₀, hsome, h1, h2, h3, h4, _, h6⟩
    · rw [hnone] at hu
      simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
      rcases hu with ⟨b, _, v0, hv0, hu_eq⟩
      exact hcs_from (hInit b .unknown) v0 hu_eq rfl hidx0.symm (by simp [hInit])
        (fun r hr hep => (hno_t r hr hep).elim) (fun r hr hep _ => (hno_t r hr hep).elim) hv0
    · rw [hsome, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
      rcases hu with ⟨v0, hv0, hvu⟩
      simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
      exact hcs_from st₀ v0 hvu h1 h2 h3 h4 h6 hv0
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hw
    rw [StateT.run_bind] at hw
    refine htr_tail hs₁ rc σ rfl rfl (fun _ _ => rfl) hs₀_pre ?_
    refine Eq.mp (congrArg (fun k => w ∈ support (runPubIdeal C ℓ encT idOf N false k rc σ)) ?_) hw
    congr 1; funext p; rcases p with ⟨_ | e, hs'⟩ <;>
      simp [StateT.run_map, StateT.run_modify, StateT.run_pure]

/-! ## 2. Off-Epoch `accept` Invariant Preservation & Unified `vRecv` Step Lemma -/

theorem EpochInv.accept_ne {ℓ : ℕ}
    {q Δcka : ℕ} {tL : Option ℕ} {t u : ℕ} {P : Party}
    {es : BucketEState Pt ℓ}
    {st' : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)}
    {pos : Pos}
    {hs' : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    {σ σ' : ℕ → Option (IdealHSt Pt ℓ)}
    (hne : t ≠ u)
    (hpos_ep : pos.epoch = u)
    (hle_ep1 : u ≤ es.g.epoch P + 1)
    (hnot_sends : P.sendsIn u = false)
    (hvS : st'.vS = (es.g.st P).vS)
    (hvR_t : st'.vR t = (es.g.st P).vR t)
    (hcur : u ≤ es.g.epoch P → st'.curCkaMsg = (es.g.st P).curCkaMsg)
    (hc : hs'.cache t = es.h.cache t)
    (hσ : ∀ j, j / q = t - healEpoch tL → σ' j = σ j)
    (hinv : EpochInv q Δcka tL t es σ) :
    EpochInv q Δcka tL t { es with g := es.g.accept P st' pos, h := hs' } σ' := by
  have hpos_ne_t : ∀ r : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt),
      r.pos.epoch = t → r.pos ≠ pos := by
    intro r hr_ep hp; apply hne; rw [← hr_ep, hp, hpos_ep]
  rcases hinv.congr_block hc hσ with hbad | hcomp | hpre | ⟨s₀, hidl⟩
  · exact Or.inl hbad
  · refine Or.inr (Or.inl ⟨?_, hcomp.2.1, ?_, ?_, ?_, hcomp.2.2.2.2.2⟩)
    · by_cases hS : Party.senderOf t = P
      · simp only [GameState.accept, GameState.delete, hS, Function.update_self]
        have h1 : t ≤ es.g.epoch (Party.senderOf t) := hcomp.1
        rw [hS] at h1; omega
      · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using hcomp.1
    · intro r hr hep
      simp only [GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne] at hr ⊢
      exact ⟨hcomp.2.2.1 r hr.1 hep, hpos_ne_t r hep⟩
    · intro Q sIdx hblk
      by_cases hQ : Q = P
      · rw [hQ]; simpa [GameState.accept, GameState.delete, hvS] using hcomp.2.2.2.1 P sIdx hblk
      · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hcomp.2.2.2.1 Q sIdx hblk
    · intro Q sIdx
      by_cases hQ : Q = P
      · rw [hQ]; simpa [GameState.accept, GameState.delete, hvR_t] using hcomp.2.2.2.2.1 P sIdx
      · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hcomp.2.2.2.2.1 Q sIdx
  · refine Or.inr (Or.inr (Or.inl ⟨?_, hpre.2.1, hpre.2.2.1, ?_, ?_, hpre.2.2.2.2.2.1, hpre.2.2.2.2.2.2⟩))
    · intro Q; by_cases hQ : Q = P
      · rw [hQ]; simp only [GameState.accept, GameState.delete, Function.update_self, hpos_ep]
        have hltP : es.g.epoch P < t := hpre.1 P; omega
      · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hpre.1 Q
    · intro Q; by_cases hQ : Q = P
      · rw [hQ]; simpa [GameState.accept, GameState.delete, hvR_t] using hpre.2.2.2.1 P
      · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hpre.2.2.2.1 Q
    · intro Q sIdx hblk; by_cases hQ : Q = P
      · rw [hQ]; simpa [GameState.accept, GameState.delete, hvS] using hpre.2.2.2.2.1 P sIdx hblk
      · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hpre.2.2.2.2.1 Q sIdx hblk
  · rcases hidl with ⟨hdiv, hep, hct_idx, hvS_eq, hvS_all, hunused, hnone_tr, hsome, hvR, hvR_ge, hpin⟩
    dsimp only at hep hct_idx hvS_eq hvS_all hnone_tr hsome hvR hvR_ge hpin
    refine Or.inr (Or.inr (Or.inr ⟨s₀, hdiv, ?_, ?_, ?_, ?_, hunused, ?_, ?_, ?_, ?_, ?_⟩))
    · by_cases hS : Party.senderOf t = P
      · simp only [GameState.accept, GameState.delete, hS, Function.update_self]; rw [hS] at hep; omega
      · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using hep
    · intro r hr hr_ep; simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
      exact hct_idx r hr.1 hr_ep
    · intro hep_acc
      by_cases hS : Party.senderOf t = P
      · simp only [GameState.accept, GameState.delete, hS, Function.update_self, hpos_ep, hvS] at hep_acc ⊢
        rw [hS] at hep
        have hep_eq : es.g.epoch P = t := by omega
        exact hS ▸ hvS_eq (hS.symm ▸ hep_eq)
      · simp only [GameState.accept, GameState.delete, Function.update_of_ne hS] at hep_acc ⊢
        exact hvS_eq hep_acc
    · intro Q idx hblk hvSQ
      have hvS_old : (es.g.st Q).vS = some (.inr idx) := by
        by_cases hQ : Q = P
        · rw [hQ] at hvSQ ⊢; simpa [GameState.accept, GameState.delete, hvS] using hvSQ
        · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hvSQ
      rcases hvS_all Q idx hblk hvS_old with ⟨rfl, rfl, hsend⟩
      refine ⟨rfl, rfl, fun hsIn => ?_⟩
      by_cases hS : Party.senderOf t = P
      · simp only [GameState.accept, GameState.delete, hS, Function.update_self, hpos_ep] at hsIn ⊢
        have heq_ep : max (es.g.epoch P) u = es.g.epoch P := by
          rcases Nat.le_total (es.g.epoch P) u with hle | hle
          · rw [Nat.max_eq_right hle, hnot_sends] at hsIn; cases hsIn
          · exact Nat.max_eq_left hle
        rw [heq_ep] at hsIn ⊢
        have hres := hsend (by simpa [hS] using hsIn)
        simpa [hS] using hres
      · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using
          hsend (by simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using hsIn)
    · intro hnone r hr hr_ep; simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
      exact hnone_tr hnone r hr.1 hr_ep
    · intro st hst; rcases hsome st hst with ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, ?_, ?_, ?_⟩
      · intro r hr hr_ep; simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        exact h3 r hr.1 hr_ep
      · intro hheal; rcases h4 hheal with ⟨hsc0, htr0⟩
        refine ⟨hsc0, fun r_fs hr_fs => ?_⟩
        rcases htr0 r_fs hr_fs with ⟨m0, hm0⟩
        have hne_p : (⟨Party.senderOf t, t, r_fs.idx⟩ : Pos) ≠ pos :=
          hpos_ne_t ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m0, (r_fs.ad.1, r_fs.ct)⟩ rfl
        exact ⟨m0, by simp [GameState.accept, GameState.delete, hm0, hne_p]⟩
      · intro r hr hr_ep hnc
        simp only [GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne] at hr
        exact h5 r hr.1 hr_ep (fun hc0 => hnc (by simp [GameState.accept, GameState.delete, hc0, hr.2]))
    · intro Q v0 hv0; by_cases hQ : Q = P
      · rw [hQ] at hv0; simp only [GameState.accept, GameState.delete, Function.update_self, hvR_t] at hv0
        exact hvR P v0 hv0
      · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hv0; exact hvR Q v0 hv0
    · intro hge; by_cases hR : Party.receiverOf t = P
      · simp only [GameState.accept, GameState.delete, hR, Function.update_self, hpos_ep, hvR_t] at hge ⊢
        have hge_old : t ≤ es.g.epoch P := by omega
        exact hR ▸ hvR_ge (hR.symm ▸ hge_old)
      · simp only [GameState.accept, GameState.delete, Function.update_of_ne hR] at hge ⊢; exact hvR_ge hge
    · intro ht_pos; rcases hpin ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
      refine ⟨Tc, σc, k, hc_Tc, ?_, ?_⟩
      · intro hep_acc; by_cases hS : Party.senderOf t = P
        · simp only [GameState.accept, GameState.delete, hS, Function.update_self, hpos_ep] at hep_acc ⊢
          rw [hS] at hep
          have hle_ep : u ≤ es.g.epoch P := by omega
          have hep_eq : es.g.epoch P = t := by omega
          rw [hcur hle_ep]; exact hS ▸ hcur_Tc (hS.symm ▸ hep_eq)
        · simp only [GameState.accept, GameState.delete, Function.update_of_ne hS] at hep_acc ⊢; exact hcur_Tc hep_acc
      · intro r hr hr_ep; simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        exact htr_Tc r hr.1 hr_ep

theorem vRecv_bucket_step
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
    (hfr_eq : hk.fsRecv = (hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).fsRecv)
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
    (rem' : ℕ) (P : Party)
    (es : BucketEState Pt ℓ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hact : BucketActive q Δcka Δbucket qep tL par (rem' + 1) (es, none) σ)
    (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hcall : es.g.safeInj (2 + Δcka) = true ∨ ∃ r_hdr ∈ es.g.trans, r_hdr.ct.1 = c.1)
    (w : ((Option (Option (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
          (RatchetSenderState (BitVec 256) ⊕ ℕ)
          (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
        ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × _) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((vRecv hk es.g P (es.g.st P) c rec).run es.h) rc σ)) :
    w.1.1.1 = none ∨
    (w.1.1.1 = some none ∧
      BucketActive q Δcka Δbucket qep tL par rem' ({ es with h := w.1.1.2 }, none) w.2) ∨
    ∃ st' i' m',
      w.1.1.1 = some (some (st', c.1.1, i', m')) ∧
      (rec = none → (es.g.inTransit P.other c).isSome = false →
        IsTargetEpoch Δcka Δbucket qep tL par c.1.1 → ¬ EpochBad tL c.1.1 es.g →
        es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true) ∧
      (rec = none → (es.g.inTransit P.other c).isSome = false →
        BucketActive q Δcka Δbucket qep tL par rem' ({ es with h := w.1.1.2 }, none) w.2) ∧
      (∀ pos : Pos,
        pos.epoch = c.1.1 →
        ((rec = none ∧ (es.g.inTransit P.other c).isSome = false) ∨
          (∃ r ∈ es.g.trans, rec = some r ∧ r.pos = pos ∧ r.ct = c)) →
        BucketActive q Δcka Δbucket qep tL par rem'
          ({ es with g := es.g.accept P st' pos, h := w.1.1.2 }, none) w.2) := by
  have _ := hq
  let PostRecv : Prop := w.1.1.1 = none ∨
    (w.1.1.1 = some none ∧ BucketActive q Δcka Δbucket qep tL par rem' ({ es with h := w.1.1.2 }, none) w.2) ∨
    ∃ st' i' m', w.1.1.1 = some (some (st', c.1.1, i', m')) ∧
      (rec = none → (es.g.inTransit P.other c).isSome = false →
        IsTargetEpoch Δcka Δbucket qep tL par c.1.1 → ¬ EpochBad tL c.1.1 es.g →
        es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true) ∧
      (rec = none → (es.g.inTransit P.other c).isSome = false →
        BucketActive q Δcka Δbucket qep tL par rem' ({ es with h := w.1.1.2 }, none) w.2) ∧
      (∀ pos : Pos, pos.epoch = c.1.1 →
        ((rec = none ∧ (es.g.inTransit P.other c).isSome = false) ∨
          (∃ r ∈ es.g.trans, rec = some r ∧ r.pos = pos ∧ r.ct = c)) →
        BucketActive q Δcka Δbucket qep tL par rem'
          ({ es with g := es.g.accept P st' pos, h := w.1.1.2 }, none) w.2)
  rcases hact with ⟨_, hwf, hep_inv⟩
  dsimp only at hwf hep_inv
  unfold vRecv at hw
  have hidP : (es.g.st P).id = P := hwf.hid P
  have htcurP : (es.g.st P).tcur = es.g.epoch P := hwf.htcur P
  set u := c.1.1 with hu_def
  by_cases hguard : (P.sendsIn u || decide (es.g.epoch P + 1 < u)) = true
  · simp only [hidP, htcurP, hguard, ↓reduceIte, StateT.run_pure, runPubIdeal,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact Or.inr (Or.inl ⟨rfl, ⟨rfl, GlobalBucketWF_mono_rem hwf (Nat.le_succ rem'), hep_inv⟩⟩)
  · simp only [hidP, htcurP] at hw
    have hguard' : (P.sendsIn u || decide (es.g.epoch P + 1 < u)) = false :=
      Bool.eq_false_iff.mpr hguard
    rcases Bool.or_eq_false_iff.mp hguard' with ⟨hnot_sends, hnot_gt⟩
    have hle_ep1 : u ≤ es.g.epoch P + 1 := Nat.le_of_not_lt (of_decide_eq_false hnot_gt)
    have hP_recv : P = Party.receiverOf u ∧ P.other = Party.senderOf u := by
      rcases Nat.mod_two_eq_zero_or_one u with hmod | hmod <;>
        cases P <;>
        simp [Party.sendsIn, Party.receiverOf, Party.senderOf, Party.other, hmod] at hnot_sends ⊢
    have hP_ne_send : P ≠ Party.senderOf u := by
      rw [hP_recv.1]
      rcases Nat.mod_two_eq_zero_or_one u with hmod | hmod <;>
        simp [Party.receiverOf, Party.senderOf, Party.other, hmod]
    simp only [hnot_sends, Bool.false_or, hnot_gt, Bool.false_eq_true, ↓reduceIte] at hw
    have hwf_accept_base : ∀ (st' : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (pos : Pos) (hs' : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt
          (ℕ × LibsignalCiphertextWithSalt32)),
        pos.epoch = u →
        GlobalBucketWF q Δbucket qep tL par rem' { es with h := hs' } →
        st'.id = P →
        st'.tcur = max (es.g.epoch P) u →
        st'.vS = (es.g.st P).vS →
        (∀ u', u' ≠ u → st'.vR u' = (es.g.st P).vR u') →
        (∀ sIdx, st'.vR u = some (.inr sIdx) →
          inStage2BucketGen Δbucket tL par u = true ∧ u ≤ qep + 1 ∧ sIdx / q = u - healEpoch tL) →
        GlobalBucketWF q Δbucket qep tL par rem'
          { es with g := es.g.accept P st' pos, h := hs' } := by
      intro st' pos hs' hpos_ep hwf' hid' htcur' hvS' hvR_ne' hvR_u'
      exact {
        habort := hwf'.habort
        hwin := hwf'.hwin
        hid := fun Q => by
          by_cases hQ : Q = P
          · rw [hQ]; simp [GameState.accept, GameState.delete, hid']
          · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ]
            exact hwf'.hid Q
        htcur := fun Q => by
          by_cases hQ : Q = P
          · rw [hQ]; simp [GameState.accept, GameState.delete, htcur', hpos_ep]
          · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ]
            exact hwf'.htcur Q
        htL_mem := hwf'.htL_mem
        hsess_zero := hwf'.hsess_zero
        hsess_pos := hwf'.hsess_pos
        hcache_blk := hwf'.hcache_blk
        hvR_blk := fun Q u' sIdx hvR => by
          by_cases hQ : Q = P
          · rw [hQ] at hvR
            simp only [GameState.accept, GameState.delete, Function.update_self] at hvR
            by_cases hu' : u' = u
            · rw [hu'] at hvR ⊢; exact hvR_u' sIdx hvR
            · rw [hvR_ne' u' hu'] at hvR; exact hwf'.hvR_blk P u' sIdx hvR
          · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hvR
            exact hwf'.hvR_blk Q u' sIdx hvR
        hvS_blk := fun Q sIdx hvSQ => by
          have hvS_old : (es.g.st Q).vS = some (.inr sIdx) := by
            by_cases hQ : Q = P
            · rw [hQ] at hvSQ ⊢; simpa [GameState.accept, GameState.delete, hvS'] using hvSQ
            · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hvSQ
          rcases hwf'.hvS_blk Q sIdx hvS_old with ⟨u0, hle0, hsends0, hP0, hbk0, hqep0, hdiv0⟩
          dsimp only at hle0 hsends0
          refine ⟨u0, ?_, ?_, hP0, hbk0, hqep0, hdiv0⟩
          · by_cases hQ : Q = P
            · rw [hQ] at hle0 ⊢
              simp only [GameState.accept, GameState.delete, Function.update_self]; omega
            · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hle0
          · intro hsIn
            by_cases hQ : Q = P
            · rw [hQ] at hsIn hsends0 ⊢
              simp only [GameState.accept, GameState.delete, Function.update_self, hpos_ep] at hsIn ⊢
              have hle_ep : u ≤ es.g.epoch P := by
                by_contra hgt
                have hmax : max (es.g.epoch P) u = u := by omega
                rw [hmax, hnot_sends] at hsIn; cases hsIn
              have hmax : max (es.g.epoch P) u = es.g.epoch P := Nat.max_eq_left hle_ep
              rw [hmax] at hsIn ⊢
              exact hsends0 hsIn
            · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using
                hsends0 (by simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hsIn)
        htrans_wf := fun r hr => by
          simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
          rcases hwf'.htrans_wf r hr.1 with ⟨h1, h2, h3, h4⟩
          dsimp only at h1 h2 h3 h4
          refine ⟨h1, h2, ?_, ?_⟩
          · by_cases hS : r.pos.sender = P
            · rw [hS] at h3
              simp only [GameState.accept, GameState.delete, hS, Function.update_self]; omega
            · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using h3
          · by_cases hS : r.pos.sender = P
            · intro hmax
              rw [hS] at h4
              simp only [GameState.accept, GameState.delete, hS, Function.update_self, hpos_ep] at hmax ⊢
              have hr_sends : P.sendsIn r.pos.epoch = true := by
                rw [← hS, h2]
                rcases Nat.mod_two_eq_zero_or_one r.pos.epoch with hmod | hmod <;>
                  simp [Party.senderOf, Party.sendsIn, hmod]
              have hne_ru : r.pos.epoch ≠ u := by
                intro he; rw [he, hnot_sends] at hr_sends; cases hr_sends
              exact h4 (by omega)
            · simpa [GameState.accept, GameState.delete, Function.update_of_ne hS] using h4
      }
    have hcont : ∀ (s₁ : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (hs₁ : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt
          (ℕ × LibsignalCiphertextWithSalt32)),
        GlobalBucketWF q Δbucket qep tL par rem' { es with h := hs₁ } →
        hs₁.cache = es.h.cache →
        s₁.id = P →
        s₁.tcur = max (es.g.epoch P) u →
        s₁.vS = (es.g.st P).vS →
        (u ≤ es.g.epoch P → s₁.curCkaMsg = (es.g.st P).curCkaMsg) →
        (∀ u', u' ≠ u → s₁.vR u' = (es.g.st P).vR u') →
        (∀ rs, s₁.vR u = some (Sum.inl rs) →
          IsTargetEpoch Δcka Δbucket qep tL par u → ¬ EpochBad tL u es.g →
          EpochCompEntry q tL u es) →
        (∀ sIdx, s₁.vR u = some (Sum.inr sIdx) →
          inStage2BucketGen Δbucket tL par u = true ∧ u ≤ qep + 1 ∧ sIdx / q = u - healEpoch tL ∧
          (IsTargetEpoch Δcka Δbucket qep tL par u → ¬ EpochBad tL u es.g →
            EpochCleanAt q Δcka tL u es σ ∧
            (healedBy es.g.tL (2 + Δcka) u = true ∨
              (∃ Q, (es.g.st Q).vR u = some (Sum.inr sIdx)) ∨
              (0 < u ∧ (∃ r_hdr ∈ es.g.trans, r_hdr.pos.epoch = u) ∧
                ∃ Tc σc k, es.h.cache u = some (Tc, σc, k, some sIdx))))) →
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          ((show _root_.CryptoGames.SM.Engine.HM _ _ _ from do
            match s₁.vR u with
            | none => return some none
            | some v =>
              match ← hk.fsRecv es.g P u v c.1 c.2 rec with
              | none => return none
              | some none => return some none
              | some (some (v', i, m)) =>
                return some (some ({ s₁ with vR := Function.update s₁.vR u (some v') }, u, i, m))).run hs₁)
          rc σ) → PostRecv := by
      intro s₁ hs₁ hwf₁ hc₁ hid₁ htcur₁ hvS₁ hcur₁ hvR₁_ne hvR₁_inl hvR₁_inr hw_fs
      have hact₁ : BucketActive q Δcka Δbucket qep tL par rem' ({ es with h := hs₁ }, none) σ :=
        ⟨rfl, hwf₁, fun t ht => (hep_inv t ht).congr_block (congrFun hc₁ t) (fun _ _ => rfl)⟩
      cases hvRu : s₁.vR u with
      | none =>
        rw [hvRu] at hw_fs
        simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw_fs
        subst hw_fs; exact Or.inr (Or.inl ⟨rfl, hact₁⟩)
      | some v =>
        cases v with
        | inl rs =>
          rw [hvRu, hfr_eq] at hw_fs
          dsimp only [hooksFSMultiDFBucketPaper] at hw_fs
          cases hdec : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs c.1 c.2 with
          | none =>
            simp only [hdec, Option.map_none, StateT.run_pure, pure_bind, runPubIdeal,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fs
            subst hw_fs; exact Or.inr (Or.inl ⟨rfl, hact₁⟩)
          | some out =>
            rcases out with ⟨rs', i', m'⟩
            simp only [hdec, Option.map_some, StateT.run_pure, pure_bind, runPubIdeal,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw_fs
            subst hw_fs
            refine Or.inr (Or.inr ⟨_, i', m', rfl, ?_, fun _ _ => hact₁, ?_⟩)
            · intro _ _ htarg hnbad
              have hcomp := hvR₁_inl rs hvRu htarg hnbad
              rcases hcomp.2.1 with ⟨cur, htL_cur, hle_cur⟩
              have hnot_heal : healedBy es.g.tL (2 + Δcka) u = false := by
                simp only [healedBy, htL_cur, decide_eq_false_iff_not]; omega
              by_cases hany : (es.g.trans.any (fun r => r.pos == ⟨P.other, u, i'⟩)) = true
              · rcases List.any_eq_true.mp hany with ⟨r, hr_mem, hr_eq⟩
                rw [beq_iff_eq] at hr_eq
                have hc_mem : (⟨P.other, u, i'⟩ : Pos) ∈ es.g.comp :=
                  hr_eq ▸ hcomp.2.2.1 r hr_mem (congrArg Pos.epoch hr_eq)
                unfold GameState.trivial
                rw [List.contains_iff_exists_mem_beq.mpr ⟨_, hc_mem, beq_self_eq_true _⟩, Bool.true_or]
              · simp only [Bool.not_eq_true] at hany
                unfold GameState.trivial; rw [hany, hnot_heal]; simp
            · intro pos hpos_ep _
              refine ⟨rfl,
                hwf_accept_base _ pos hs₁ hpos_ep hwf₁ hid₁ htcur₁ hvS₁
                  (fun u' hu' => by simp [Function.update_of_ne hu', hvR₁_ne u' hu'])
                  (fun sIdx h => by simp at h),
                fun t ht => ?_⟩
              by_cases htu : t = u
              · rw [htu] at ht ⊢
                by_cases hbad : EpochBad tL u es.g
                · exact Or.inl hbad
                · have hcomp := hvR₁_inl rs hvRu ht hbad
                  refine Or.inr (Or.inl ⟨?_, hcomp.2.1, ?_, ?_, ?_,
                    fun Tc σc k optIdx hc => hcomp.2.2.2.2.2 Tc σc k optIdx (hc₁ ▸ hc)⟩)
                  · simp only [GameState.accept, GameState.delete, Function.update_of_ne hP_ne_send.symm]
                    exact hcomp.1
                  · intro r hr hr_ep
                    simp only [GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne] at hr ⊢
                    exact ⟨hcomp.2.2.1 r hr.1 hr_ep, hr.2⟩
                  · intro Q sIdx hblk
                    by_cases hQ : Q = P
                    · rw [hQ]; simpa [GameState.accept, GameState.delete, hvS₁] using hcomp.2.2.2.1 P sIdx hblk
                    · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hcomp.2.2.2.1 Q sIdx hblk
                  · intro Q sIdx
                    by_cases hQ : Q = P
                    · rw [hQ]; simp [GameState.accept, GameState.delete]
                    · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hcomp.2.2.2.2.1 Q sIdx
              · exact EpochInv.accept_ne htu hpos_ep hle_ep1 hnot_sends hvS₁
                  (by simp [Function.update_of_ne htu, hvR₁_ne t htu])
                  (fun hle => hcur₁ hle) (congrFun hc₁ t) (fun _ _ => rfl) (hep_inv t ht)
        | inr sIdx =>
          rcases hvR₁_inr sIdx hvRu with ⟨hbuck_u, hqep_u, hdiv_u, hclean_u⟩
          have hle_tH_u : healEpoch tL ≤ u := healEpoch_le_of_inStage2BucketGen hΔb hbuck_u
          have hblk_ne : ∀ t, IsTargetEpoch Δcka Δbucket qep tL par t → t ≠ u →
              ∀ (σ' : ℕ → Option (IdealHSt Pt ℓ)), (∀ j, j ≠ sIdx → σ' j = σ j) →
              ∀ j, j / q = t - healEpoch tL → σ' j = σ j := by
            intro t ht htu σ' hσ_ne j hj_div
            have hle_tH_t : healEpoch tL ≤ t := healEpoch_le_of_inStage2BucketGen hΔb ht.1
            apply hσ_ne
            intro hjeq; subst hjeq
            have : t - healEpoch tL = u - healEpoch tL := hj_div.symm.trans hdiv_u
            omega
          rw [hvRu, hfr_eq] at hw_fs
          simp only [StateT.run_bind, runPubIdeal, simulateQ_bind,
            MonadAttach.mem_support_bind] at hw_fs
          rcases hw_fs with ⟨w_r, hw_r, hfin⟩
          by_cases hclean_cond : IsTargetEpoch Δcka Δbucket qep tL par u ∧ ¬ EpochBad tL u es.g
          · rcases hclean_cond with ⟨htarg_u, hnbad_u⟩
            rcases hclean_u htarg_u hnbad_u with ⟨hcl_u, hsp_u⟩
            rcases fsRecv_inr_bucket_step_post C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
                u sIdx P es rc σ hdiv_u hcl_u hsp_u c.1 c.2 rec hs₁ w_r hw_r with
              hr_none | ⟨hr_rej, hc_r, hse_r, hσ_ne_r, hr_cl⟩ |
              ⟨i', m', s₀, st₀, st'_fs, hr_acc, hc_r, hse_r, rfl,
               hdiv_s₀, hle_s₀, hct_idx, hvS_eq, hvS_all, hunused, hvR_s₀, hvR_ge_s₀, hpin_s₀,
               h5₀, hσ_upd, hend', hls', hsc', hsub', hheal_f⟩
            · simp only [hr_none, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hfin
              subst hfin; exact Or.inl rfl
            · simp only [hr_rej, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hfin
              subst hfin
              have hc_fin : w_r.1.1.2.cache = es.h.cache := hc_r.trans hc₁
              have hwf_r : GlobalBucketWF q Δbucket qep tL par rem' { es with h := w_r.1.1.2 } := {
                habort := hwf₁.habort, hwin := hwf₁.hwin, hid := hwf₁.hid, htcur := hwf₁.htcur,
                htL_mem := hwf₁.htL_mem,
                hsess_zero := hse_r ▸ hwf₁.hsess_zero,
                hsess_pos := fun u' hu' => hse_r ▸ hwf₁.hsess_pos u' hu',
                hcache_blk := fun u' Tc σc k idx hc => hwf₁.hcache_blk u' Tc σc k idx (hc_r ▸ hc),
                hvR_blk := hwf₁.hvR_blk, hvS_blk := hwf₁.hvS_blk, htrans_wf := hwf₁.htrans_wf
              }
              refine Or.inr (Or.inl ⟨rfl, rfl, hwf_r, fun t ht => ?_⟩)
              by_cases htu : t = u
              · rw [htu] at ht ⊢
                rcases hr_cl w_r.1.1.2 (congrFun hc_fin u) with hpre' | hidl'
                · exact Or.inr (Or.inr (Or.inl hpre'))
                · exact Or.inr (Or.inr (Or.inr hidl'))
              · exact (hep_inv t ht).congr_block (congrFun hc_fin t)
                  (hblk_ne t ht htu w_r.2 hσ_ne_r)
            · simp only [hr_acc, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hfin
              subst hfin
              have hc_fin : w_r.1.1.2.cache = es.h.cache := hc_r.trans hc₁
              have hwf_r : GlobalBucketWF q Δbucket qep tL par rem' { es with h := w_r.1.1.2 } := {
                habort := hwf₁.habort, hwin := hwf₁.hwin, hid := hwf₁.hid, htcur := hwf₁.htcur,
                htL_mem := hwf₁.htL_mem,
                hsess_zero := hse_r ▸ hwf₁.hsess_zero,
                hsess_pos := fun u' hu' => hse_r ▸ hwf₁.hsess_pos u' hu',
                hcache_blk := fun u' Tc σc k idx hc => hwf₁.hcache_blk u' Tc σc k idx (hc_r ▸ hc),
                hvR_blk := hwf₁.hvR_blk, hvS_blk := hwf₁.hvS_blk, htrans_wf := hwf₁.htrans_wf
              }
              have hσ_ne_upd : ∀ j, j ≠ sIdx → w_r.2 j = σ j := by
                intro j hj; rw [hσ_upd, Function.update_of_ne hj]
              refine Or.inr (Or.inr ⟨_, i', m', rfl, ?_, ?_, ?_⟩)
              · intro hrec_none hnot_tr _ _
                subst hrec_none
                have hkill := fsRecv_inr_bucket_forged_not_nontrivial C ℓ Dh encPt encT idOf
                  q N Δcka Δbucket qep tL par u sIdx P es rc σ hdiv_u hcl_u hsp_u
                  c.1 c.2 hu_def.symm (hP_recv.2 ▸ hnot_tr) hs₁ w_r hw_r (.inr sIdx) i' m' hr_acc
                exact hP_recv.2 ▸ hkill.2.2
              · intro _ hnot_tr
                refine ⟨rfl, hwf_r, fun t ht => ?_⟩
                by_cases htu : t = u
                · rw [htu] at ht ⊢
                  rw [hσ_upd]
                  refine Or.inr (Or.inr (Or.inr ⟨sIdx, hdiv_s₀, hle_s₀, hct_idx, hvS_eq, ?_, ?_,
                    by intro hnone; simp at hnone, ?_, hvR_s₀, hvR_ge_s₀,
                    fun hpos => by dsimp only; rw [hc_fin]; exact hpin_s₀ hpos⟩))
                  · intro Q idx hblk hvSQ
                    rcases hvS_all Q idx hblk hvSQ with ⟨rfl, rfl, hsend⟩
                    refine ⟨rfl, rfl, fun hsIn => ?_⟩
                    rcases hsend hsIn with ⟨hep_t, hls_s⟩
                    exact ⟨hep_t, Or.inr ⟨st'_fs, by simp, hls'.trans hls_s⟩⟩
                  · intro idx st hblk hne_idx hst_j
                    rw [Function.update_of_ne hne_idx] at hst_j
                    exact hunused idx st hblk hne_idx hst_j
                  · intro st hst
                    simp only [Function.update_self, Option.some.injEq] at hst; subst hst
                    refine ⟨hend', ?_, fun r hr hep => hls' ▸ h5₀.2.2.1 r hr hep, ?_, ?_⟩
                    · intro r_fs hr_fs
                      rcases h5₀.2.1 r_fs (hsub' r_fs hr_fs) with ⟨h1, h2⟩
                      exact ⟨h1, hls' ▸ h2⟩
                    · intro hheal
                      rcases hheal_f hheal with ⟨r_fs₀, hr_fs₀, had₀, hct₀, _⟩
                      rcases (h5₀.2.2.2.1 hheal).2 r_fs₀ hr_fs₀ with ⟨m_c, hm_c⟩
                      rw [had₀, hct₀] at hm_c
                      have hit_some : (es.g.inTransit P.other c).isSome = true := by
                        rw [hP_recv.2]; unfold GameState.inTransit
                        rw [Option.isSome_iff_ne_none]; intro hfn
                        have := List.find?_eq_none.mp hfn _ hm_c; simp at this
                      rw [hnot_tr] at hit_some; cases hit_some
                    · intro r hr hep hnc
                      rcases h5₀.2.2.2.2 r hr hep hnc with ⟨hc_f, hct_m⟩
                      exact ⟨by simpa [HState.isCompromised, hsc'] using hc_f,
                        fun r_fs hr_fs => hct_m r_fs (hsub' r_fs hr_fs)⟩
                · exact (hep_inv t ht).congr_block (congrFun hc_fin t)
                    (hblk_ne t ht htu w_r.2 hσ_ne_upd)
              · intro pos hpos_ep hcase_u
                refine ⟨rfl,
                  hwf_accept_base _ pos w_r.1.1.2 hpos_ep hwf_r hid₁ htcur₁ hvS₁
                    (fun u' hu' => by simp [Function.update_of_ne hu', hvR₁_ne u' hu'])
                    (fun idx h => by
                      simp only [Function.update_self, Option.some.injEq, Sum.inr.injEq] at h
                      subst h; exact ⟨hbuck_u, hqep_u, hdiv_u⟩),
                  fun t ht => ?_⟩
                by_cases htu : t = u
                · rw [htu] at ht ⊢
                  rw [hσ_upd]
                  refine Or.inr (Or.inr (Or.inr ⟨sIdx, hdiv_s₀, ?_, ?_, ?_, ?_, ?_,
                    by intro hnone; simp at hnone, ?_, ?_, ?_, ?_⟩))
                  · simpa [GameState.accept, GameState.delete, Function.update_of_ne hP_ne_send.symm]
                      using hle_s₀
                  · intro r hr hr_ep
                    simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                    exact hct_idx r hr.1 hr_ep
                  · intro hep_acc
                    simp only [GameState.accept, GameState.delete,
                      Function.update_of_ne hP_ne_send.symm] at hep_acc ⊢
                    exact hvS_eq hep_acc
                  · intro Q idx hblk hvSQ
                    have hvS_old : (es.g.st Q).vS = some (.inr idx) := by
                      by_cases hQ : Q = P
                      · rw [hQ] at hvSQ ⊢; simpa [GameState.accept, GameState.delete, hvS₁] using hvSQ
                      · simpa [GameState.accept, GameState.delete, Function.update_of_ne hQ] using hvSQ
                    rcases hvS_all Q idx hblk hvS_old with ⟨rfl, rfl, hsend⟩
                    refine ⟨rfl, rfl, fun hsIn => ?_⟩
                    simp only [GameState.accept, GameState.delete,
                      Function.update_of_ne hP_ne_send.symm] at hsIn ⊢
                    rcases hsend hsIn with ⟨hep_t, hls_s⟩
                    exact ⟨hep_t, Or.inr ⟨st'_fs, by simp, hls'.trans hls_s⟩⟩
                  · intro idx st hblk hne_idx hst_j
                    rw [Function.update_of_ne hne_idx] at hst_j
                    exact hunused idx st hblk hne_idx hst_j
                  · intro st hst
                    simp only [Function.update_self, Option.some.injEq] at hst; subst hst
                    refine ⟨hend', ?_, ?_, ?_, ?_⟩
                    · intro r_fs hr_fs
                      rcases h5₀.2.1 r_fs (hsub' r_fs hr_fs) with ⟨h1, h2⟩
                      exact ⟨h1, hls' ▸ h2⟩
                    · intro r hr hr_ep
                      simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                      exact hls' ▸ h5₀.2.2.1 r hr.1 hr_ep
                    · intro hheal
                      have hheal0 : healedBy es.g.tL (2 + Δcka) u = true := hheal
                      rcases h5₀.2.2.2.1 hheal0 with ⟨hsc0, htr0⟩
                      rcases hheal_f hheal0 with ⟨r_fs₀, hr_fs₀, had₀, hct₀, hit_filt⟩
                      refine ⟨hsc'.trans hsc0, fun r_fs hr_fs => ?_⟩
                      rw [hit_filt, List.mem_filter, bne_iff_ne] at hr_fs
                      rcases htr0 r_fs hr_fs.1 with ⟨m0, hm0⟩
                      rcases hcase_u with ⟨_, hnot_tr⟩ | ⟨r_rec, hr_rec_mem, _, rfl, hct_rec⟩
                      · rcases htr0 r_fs₀ hr_fs₀ with ⟨m_c, hm_c⟩
                        rw [had₀, hct₀] at hm_c
                        have hit_some : (es.g.inTransit P.other c).isSome = true := by
                          rw [hP_recv.2]; unfold GameState.inTransit
                          rw [Option.isSome_iff_ne_none]; intro hfn
                          have := List.find?_eq_none.mp hfn _ hm_c; simp at this
                        rw [hnot_tr] at hit_some; cases hit_some
                      · have hidx_rec : r_fs₀.idx = r_rec.pos.idx := by
                          have hc1 := (h5₀.2.1 r_fs₀ hr_fs₀).1
                          have hc2 := hct_idx r_rec hr_rec_mem hpos_ep
                          calc r_fs₀.idx = r_fs₀.ct.1 := hc1.symm
                            _ = c.2.1 := congrArg Prod.fst hct₀
                            _ = r_rec.ct.2.1 := (congrArg (fun x => x.2.1) hct_rec).symm
                            _ = r_rec.pos.idx := hc2
                        have hpos_ne : (⟨Party.senderOf u, u, r_fs.idx⟩ : Pos) ≠ r_rec.pos := by
                          intro hp_eq
                          have := congrArg Pos.idx hp_eq
                          exact hr_fs.2 (this.trans hidx_rec.symm)
                        exact ⟨m0, List.mem_filter.mpr ⟨hm0, bne_iff_ne.mpr hpos_ne⟩⟩
                    · intro r hr hr_ep hnc
                      simp only [GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne] at hr
                      have hnc0 : r.pos ∉ es.g.comp := by
                        intro hc0; apply hnc
                        simp [GameState.accept, GameState.delete, hc0, hr.2]
                      rcases h5₀.2.2.2.2 r hr.1 hr_ep hnc0 with ⟨hc_f, hct_m⟩
                      exact ⟨by simpa [HState.isCompromised, hsc'] using hc_f,
                        fun r_fs hr_fs => hct_m r_fs (hsub' r_fs hr_fs)⟩
                  · intro Q v0 hv0
                    by_cases hQ : Q = P
                    · rw [hQ] at hv0; simp [GameState.accept, GameState.delete] at hv0; exact hv0.symm
                    · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ] at hv0
                      exact hvR_s₀ Q v0 hv0
                  · intro _
                    simp [← hP_recv.1, GameState.accept, GameState.delete]
                  · intro ht_pos
                    rcases hpin_s₀ ht_pos with ⟨Tc, σc, k, hc_Tc, hcur_Tc, htr_Tc⟩
                    refine ⟨Tc, σc, k, (congrFun hc_fin u) ▸ hc_Tc, ?_, ?_⟩
                    · intro hep_acc
                      simp only [GameState.accept, GameState.delete,
                        Function.update_of_ne hP_ne_send.symm] at hep_acc ⊢
                      exact hcur_Tc hep_acc
                    · intro r hr hr_ep
                      simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
                      exact htr_Tc r hr.1 hr_ep
                · exact EpochInv.accept_ne htu hpos_ep hle_ep1 hnot_sends hvS₁
                    (by simp [Function.update_of_ne htu, hvR₁_ne t htu])
                    (fun hle => hcur₁ hle) (congrFun hc_fin t)
                    (hblk_ne t ht htu w_r.2 hσ_ne_upd) (hep_inv t ht)
          · -- `¬ IsTargetEpoch ... u ∨ EpochBad tL u es.g`: off-target or post-leak epoch!
            rcases fsRecv_inr_bucket_any_support C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
                P u sIdx es.g c.1 c.2 rec hs₁ rc σ w_r hw_r with
              ⟨hc_r, hse_r, hσ_ne_r, hr_res⟩
            have hc_fin : w_r.1.1.2.cache = es.h.cache := hc_r.trans hc₁
            have hwf_r : GlobalBucketWF q Δbucket qep tL par rem' { es with h := w_r.1.1.2 } := {
              habort := hwf₁.habort, hwin := hwf₁.hwin, hid := hwf₁.hid, htcur := hwf₁.htcur,
              htL_mem := hwf₁.htL_mem,
              hsess_zero := hse_r ▸ hwf₁.hsess_zero,
              hsess_pos := fun u' hu' => hse_r ▸ hwf₁.hsess_pos u' hu',
              hcache_blk := fun u' Tc σc k idx hc => hwf₁.hcache_blk u' Tc σc k idx (hc_r ▸ hc),
              hvR_blk := hwf₁.hvR_blk, hvS_blk := hwf₁.hvS_blk, htrans_wf := hwf₁.htrans_wf
            }
            have hact_r : BucketActive q Δcka Δbucket qep tL par rem'
                ({ es with h := w_r.1.1.2 }, none) w_r.2 := by
              refine ⟨rfl, hwf_r, fun t ht => ?_⟩
              by_cases htu : t = u
              · rw [htu] at ht ⊢
                exact Or.inl (Classical.byContradiction fun hnb => hclean_cond ⟨ht, hnb⟩)
              · exact (hep_inv t ht).congr_block (congrFun hc_fin t)
                  (hblk_ne t ht htu w_r.2 hσ_ne_r)
            rcases hr_res with hr_none | hr_rej | ⟨i', m', hr_acc⟩
            · simp only [hr_none, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hfin
              subst hfin; exact Or.inl rfl
            · simp only [hr_rej, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hfin
              subst hfin; exact Or.inr (Or.inl ⟨rfl, hact_r⟩)
            · simp only [hr_acc, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hfin
              subst hfin
              refine Or.inr (Or.inr ⟨_, i', m', rfl,
                fun _ _ ht hnb => (hclean_cond ⟨ht, hnb⟩).elim,
                fun _ _ => hact_r, ?_⟩)
              intro pos hpos_ep _
              refine ⟨rfl,
                hwf_accept_base _ pos w_r.1.1.2 hpos_ep hwf_r hid₁ htcur₁ hvS₁
                  (fun u' hu' => by simp [Function.update_of_ne hu', hvR₁_ne u' hu'])
                  (fun idx h => by
                    simp only [Function.update_self, Option.some.injEq, Sum.inr.injEq] at h
                    subst h; exact ⟨hbuck_u, hqep_u, hdiv_u⟩),
                fun t ht => ?_⟩
              by_cases htu : t = u
              · rw [htu] at ht ⊢
                exact Or.inl (Classical.byContradiction fun hnb => hclean_cond ⟨ht, hnb⟩)
              · exact EpochInv.accept_ne htu hpos_ep hle_ep1 hnot_sends hvS₁
                  (by simp [Function.update_of_ne htu, hvR₁_ne t htu])
                  (fun hle => hcur₁ hle) (congrFun hc_fin t)
                  (hblk_ne t ht htu w_r.2 hσ_ne_r) (hep_inv t ht)
    -- Dispatch `if u = es.g.epoch P + 1` in `vRecv`:
    by_cases hnext : u = es.g.epoch P + 1
    · simp only [hnext, ↓reduceIte] at hw
      cases hc2 : c.1.2 with
      | none =>
        simp only [hc2, pure_bind, StateT.run_pure, runPubIdeal, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact Or.inr (Or.inl ⟨rfl, ⟨rfl, GlobalBucketWF_mono_rem hwf (Nat.le_succ rem'), hep_inv⟩⟩)
      | some Tn =>
        simp only [hc2, StateT.run_bind, runPubIdeal, simulateQ_bind,
          MonadAttach.mem_support_bind] at hw
        rcases hw with ⟨w_sr, hw_sr, hw_tail⟩
        have hu_pos : 1 ≤ es.g.epoch P + 1 := by omega
        have hlen_u : (es.h.sessions (es.g.epoch P + 1)).length < q := by
          have := hwf.hsess_pos (es.g.epoch P + 1) hu_pos; omega
        rcases hsr_spec (es.g.epoch P + 1) P es.g (es.g.st P).γ (es.g.st P).root Tn es.h
            hlen_u rc σ w_sr hw_sr with
          ⟨⟨hc_sr, hbk_sr, hlen_sr, hse_sr, hres_sr⟩, hrc_sr, hσ_sr⟩
        rw [hrc_sr, hσ_sr] at hw_tail
        have hwf₁ : GlobalBucketWF q Δbucket qep tL par rem' { es with h := w_sr.1.1.2 } := {
          habort := hwf.habort, hwin := hwf.hwin, hid := hwf.hid, htcur := hwf.htcur,
          htL_mem := hwf.htL_mem,
          hsess_zero := by rw [hse_sr 0 (by omega)]; exact hwf.hsess_zero,
          hsess_pos := fun u' hu' => by
            dsimp only
            by_cases heq : u' = es.g.epoch P + 1
            · rw [heq]; have := hwf.hsess_pos (es.g.epoch P + 1) hu_pos; omega
            · rw [hse_sr u' heq]; have := hwf.hsess_pos u' hu'; omega,
          hcache_blk := fun u' Tc σc k idx hc => hwf.hcache_blk u' Tc σc k idx (hc_sr ▸ hc),
          hvR_blk := hwf.hvR_blk, hvS_blk := hwf.hvS_blk, htrans_wf := hwf.htrans_wf
        }
        rcases hres_sr with hr_none | hr_snone | ⟨γ', σr', rsv, hr_ok, hr_cases⟩
        · simp only [hr_none, StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw_tail
          subst hw_tail; exact Or.inl rfl
        · simp only [hr_snone, StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw_tail
          subst hw_tail
          exact Or.inr (Or.inl ⟨rfl, ⟨rfl, hwf₁,
            fun t ht => (hep_inv t ht).congr_block (congrFun hc_sr t) (fun _ _ => rfl)⟩⟩)
        · simp only [hr_ok, pure_bind] at hw_tail
          let s₁' : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
              (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) :=
            { id := P, root := σr', vS := (es.g.st P).vS,
              vR := Function.update (es.g.st P).vR (es.g.epoch P + 1) (some rsv),
              γ := γ', curCkaMsg := (es.g.st P).curCkaMsg, tcur := es.g.epoch P + 1 }
          refine hcont s₁' w_sr.1.1.2 hwf₁ hc_sr rfl (by dsimp [s₁']; rw [hnext]; omega) rfl
            (fun hle => absurd hle (by omega))
            (fun u' hu' => by dsimp [s₁']; simp [Function.update_of_ne (hnext ▸ hu')])
            ?_ ?_ (by
              dsimp only [runPubIdeal, s₁']; rw [hnext]
              refine Eq.mp (congrArg (fun k => w ∈ support (runPubIdeal C ℓ encT idOf N false k rc σ)) ?_) hw_tail
              cases Function.update (es.g.st P).vR (es.g.epoch P + 1) (some rsv) (es.g.epoch P + 1) with
              | none => simp [StateT.run_pure]
              | some v =>
                simp only [StateT.run_bind]; congr 1; funext r
                rcases r with ⟨_ | ⟨_ | ⟨v', i, m⟩⟩, hs'⟩ <;> simp [StateT.run_pure])
          · intro rs hvRu htarg_u hnbad_u
            simp only [s₁', hnext, Function.update_self, Option.some.injEq] at hvRu
            subst hvRu
            rcases hep_inv u htarg_u with hbad | hcomp | hpre | ⟨s₀, hidl⟩
            · exact (hnbad_u hbad).elim
            · exact hcomp
            · exfalso
              rcases hr_cases with ⟨σc, k, optIdx, hc_hit, _⟩ | ⟨_, _, _, hpl_or⟩
              · rw [← hnext, hpre.2.2.2.2.2.1] at hc_hit; cases hc_hit
              · rcases hpl_or with ⟨hpl_t, _⟩ | ⟨_, _, h_eq, _⟩
                · rw [hpre.2.2.1] at hpl_t; cases hpl_t
                · cases h_eq
            · exfalso
              rcases hidl.2.2.2.2.2.2.2.2.2.2 (by omega) with ⟨Tc, σc_i, k_i, hc_Tc, _, htr_Tc⟩
              rcases hr_cases with ⟨σc, k, optIdx, hc_hit, hopt_or⟩ | ⟨hne_c, _, _, hpl_or⟩
              · rw [← hnext, hc_Tc] at hc_hit
                injection hc_hit with hq_eq
                rcases hopt_or with ⟨hnone_opt, _⟩ | ⟨_, _, h_eq⟩
                · have := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hq_eq).2).2).2
                  rw [hnone_opt] at this; cases this
                · cases h_eq
              · rcases hpl_or with ⟨hpl_t, _⟩ | ⟨_, _, h_eq, _⟩
                · rcases hcall with hsafe | ⟨r_hdr, hr_mem, hr_ct1⟩
                  · have hheal_u : healedBy es.g.tL (2 + Δcka) u = true := by
                      cases htL : es.g.tL with
                      | none => rfl
                      | some l0 =>
                        unfold GameState.safeInj healedBy at hsafe
                        unfold healedBy
                        rw [htL] at hsafe
                        rw [hnext]; rw [decide_eq_true_eq] at hsafe ⊢
                        cases P <;> simp at hsafe <;> omega
                    have hpl_f := (healedBy_iff_postLeakDFBucket_false htarg_u.2.1 hwf.htL_mem hnbad_u).mp hheal_u
                    rw [hpl_f] at hpl_t; cases hpl_t
                  · have hr_ep : r_hdr.pos.epoch = u :=
                      (hwf.htrans_wf r_hdr hr_mem).1.trans (congrArg Prod.fst hr_ct1)
                    have hTc_eq : Tn = Tc := by
                      have h1 : r_hdr.ct.1.2 = some Tc := htr_Tc r_hdr hr_mem hr_ep
                      have h2 : r_hdr.ct.1.2 = some Tn := (congrArg Prod.snd hr_ct1).trans hc2
                      exact Option.some.inj (h2.symm.trans h1)
                    subst hTc_eq
                    exact hne_c σc_i k_i (some s₀) (hnext ▸ hc_Tc)
                · cases h_eq
          · intro sIdx hvRu
            simp only [s₁', hnext, Function.update_self, Option.some.injEq] at hvRu
            subst hvRu
            rcases hr_cases with ⟨σc, k, optIdx, hc_hit, ⟨_, _, h_eq⟩ | ⟨s₀, rfl, h_eq⟩⟩ |
                ⟨_, hle_q, hbk_q, ⟨_, _, h_eq⟩ | ⟨hpl_f, sIdx', h_eq, hdiv_q⟩⟩
            · cases h_eq
            · injection h_eq with hs_eq; subst hs_eq
              rcases hwf.hcache_blk (es.g.epoch P + 1) Tn σc k sIdx hc_hit with ⟨_, hbk_c, hqep_c, hdiv_c⟩
              refine ⟨hnext ▸ hbk_c, hnext ▸ hqep_c, hnext ▸ hdiv_c, fun htarg_u hnbad_u => ?_⟩
              have hcl_u : EpochCleanAt q Δcka tL u es σ := by
                rcases hep_inv u htarg_u with hbad | hcomp | hpre | hidl
                · exact (hnbad_u hbad).elim
                · exfalso
                  have := hcomp.2.2.2.2.2 Tn σc k (some sIdx) (hnext ▸ hc_hit)
                  cases this
                · exact Or.inl hpre
                · exact Or.inr hidl
              refine ⟨hcl_u, ?_⟩
              rcases hcall with hsafe | ⟨r_hdr, hr_mem, hr_ct1⟩
              · left
                cases htL : es.g.tL with
                | none => rfl
                | some l0 =>
                  unfold GameState.safeInj healedBy at hsafe
                  unfold healedBy
                  rw [htL] at hsafe
                  rw [hnext]; rw [decide_eq_true_eq] at hsafe ⊢
                  cases P <;> simp at hsafe <;> omega
              · have hr_ep : r_hdr.pos.epoch = u :=
                  (hwf.htrans_wf r_hdr hr_mem).1.trans (congrArg Prod.fst hr_ct1)
                exact Or.inr (Or.inr ⟨by omega, ⟨r_hdr, hr_mem, hr_ep⟩, Tn, σc, k, hnext ▸ hc_hit⟩)
            · cases h_eq
            · injection h_eq with hs_eq; subst hs_eq
              refine ⟨hnext ▸ hbk_q, hnext ▸ hle_q, hnext ▸ hdiv_q, fun htarg_u hnbad_u => ?_⟩
              have hheal_u : healedBy es.g.tL (2 + Δcka) u = true :=
                (healedBy_iff_postLeakDFBucket_false htarg_u.2.1 hwf.htL_mem hnbad_u).mpr hpl_f
              have hcl_u : EpochCleanAt q Δcka tL u es σ := by
                rcases hep_inv u htarg_u with hbad | hcomp | hpre | hidl
                · exact (hnbad_u hbad).elim
                · exfalso
                  rcases hcomp.2.1 with ⟨cur, htL_cur, hle_cur⟩
                  simp only [healedBy, htL_cur, decide_eq_true_eq] at hheal_u; omega
                · exact Or.inl hpre
                · exact Or.inr hidl
              exact ⟨hcl_u, Or.inl hheal_u⟩
    · have hle_cur : u ≤ es.g.epoch P := by omega
      simp only [hnext, ↓reduceIte, pure_bind] at hw
      refine hcont (es.g.st P) es.h (GlobalBucketWF_mono_rem hwf (Nat.le_succ rem')) rfl hidP
        (htcurP.trans (Nat.max_eq_left hle_cur).symm) rfl (fun _ => rfl) (fun _ _ => rfl) ?_ ?_ (by
          dsimp only
          refine Eq.mp (congrArg (fun k => w ∈ support (runPubIdeal C ℓ encT idOf N false k rc σ)) ?_) hw
          cases (es.g.st P).vR u with
          | none => simp [StateT.run_pure]
          | some v =>
            simp only [StateT.run_bind]; congr 1; funext r
            rcases r with ⟨_ | ⟨_ | ⟨v', i, m⟩⟩, hs'⟩ <;> simp [StateT.run_pure])
      · intro rs hvRu htarg_u hnbad_u
        rcases hep_inv u htarg_u with hbad | hcomp | hpre | ⟨s₀, hidl⟩
        · exact (hnbad_u hbad).elim
        · exact hcomp
        · exfalso; rw [hpre.2.2.2.1 P] at hvRu; cases hvRu
        · exfalso; cases hidl.2.2.2.2.2.2.2.2.1 P (.inl rs) hvRu
      · intro sIdx hvRu
        rcases hwf.hvR_blk P u sIdx hvRu with ⟨hbk_u, hqep_u, hdiv_u⟩
        refine ⟨hbk_u, hqep_u, hdiv_u, fun htarg_u hnbad_u => ?_⟩
        rcases hep_inv u htarg_u with hbad | hcomp | hpre | hidl
        · exact (hnbad_u hbad).elim
        · exfalso; exact hcomp.2.2.2.2.1 P sIdx hvRu
        · exact ⟨Or.inl hpre, Or.inr (Or.inl ⟨P, hvRu⟩)⟩
        · exact ⟨Or.inr hidl, Or.inr (Or.inl ⟨P, hvRu⟩)⟩

end BucketRecv

end

end Computational.Proofs.E2E.SessionAuthMultiEndBucketRecv

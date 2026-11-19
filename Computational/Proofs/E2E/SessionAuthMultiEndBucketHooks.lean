/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiEndBase -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiEndBucketSteps -- proof-setup: allow-public-import

/-!
# Ideal-Cutoff `fsSend` / `fsRecv` / `reveal` Hook Specs for `DeliverForgePaperMultiBucket`

Proves:
1. Generic off-epoch support preservation (`corruptSender_bucket_any_support`,
   `fsSend_inr_bucket_any_support`, `fsRecv_inr_bucket_any_support`) keeping `cache`, `sessions`,
   and all session indices `j ≠ sIdx` untouched.
2. Target-epoch (`EpochCleanAt`) hook theorems: `corruptSender_fsRecv_bucket_clean`,
   `fsRecv_inr_bucket_forged_not_nontrivial`, `fsRecv_inr_bucket_step_post`, and
   `fsSend_inr_bucket_step_post`.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEndBucketHooks

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.FSAEAD (ReceiveResult RatchetSenderState RatchetReceiverState withPub)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.SM (GameState Record healedBy)
open _root_.CryptoGames.SM.Construction (
  Header FSMultiDFBucketState FSMultiBook
  liftFSMultiDFBucket hooksFSMultiDFBucketPaper healEpoch)
open _root_.CryptoGames.SM.Engine (Ctx)
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
  HState DG transmitHWith corruptSenderH deliverH injectH hInit)
open Computational.Proofs.E2E.SessionAuthMultiEnd (IdealHSt PubMultiSpec runPubIdeal
  isCompromised_of_senderCorruptedAt_none)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketSteps (
  BucketEState EpochPre EpochIdealAt EpochIdeal
  injectH_hpIdeal_false_step_spec deliverH_hpIdeal_false_step_spec
  transmitHWith_hpIdeal_false_step_spec corruptSenderH_hpIdeal_false_step_spec
  runPubIdeal_liftFSMultiDFBucket_transmit_support
  runPubIdeal_liftFSMultiDFBucket_corruptSender_support
  runPubIdeal_liftFSMultiDFBucket_deliver_support
  runPubIdeal_liftFSMultiDFBucket_inject_support)

section BucketHooks

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## 1. Generic Session-Localized Support Lemmas (`j ≠ sIdx` Untouched) -/

theorem fsSend_inr_bucket_any_support
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (u sIdx : ℕ)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (hs₁ : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : ((Option ((RatchetSenderState (BitVec 256) ⊕ ℕ) ×
        (ℕ × LibsignalCiphertextWithSalt32)) × _) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).fsSend
        ctx P u (.inr sIdx) hdr pm none).run hs₁) rc σ)) :
    w.1.1.2.cache = hs₁.cache ∧
    w.1.1.2.sessions = hs₁.sessions ∧
    (∀ j, j ≠ sIdx → w.2 j = σ j) ∧
    (w.1.1.1 = none ∨ ∃ e, w.1.1.1 = some (.inr sIdx, e)) := by
  dsimp only [hooksFSMultiDFBucketPaper] at hw
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
  have htr_tail : ∀ hs_mid rc_mid (σ_mid : ℕ → Option (IdealHSt Pt ℓ)),
      hs_mid.cache = hs₁.cache →
      hs_mid.sessions = hs₁.sessions →
      (∀ j, j ≠ sIdx → σ_mid j = σ j) →
      ∀ (k_tr : Option (ℕ × LibsignalCiphertextWithSalt32) ×
          FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) →
        OracleComp (PubMultiSpec Pt ℓ)
          (Option ((RatchetSenderState (BitVec 256) ⊕ ℕ) × (ℕ × LibsignalCiphertextWithSalt32)) ×
            FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))),
      (∀ hs_k, k_tr (none, hs_k) = pure (none, hs_k)) →
      (∀ e hs_k, ∃ hs_k',
        k_tr (some e, hs_k) = pure (some (.inr sIdx, e), hs_k') ∧
        hs_k'.cache = hs_k.cache ∧ hs_k'.sessions = hs_k.sessions) →
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        ((liftFSMultiDFBucket sIdx (CryptoGames.FSAEAD.transmitQuery hdr pm)).run hs_mid >>= k_tr) rc_mid σ_mid) →
      w.1.1.2.cache = hs₁.cache ∧ w.1.1.2.sessions = hs₁.sessions ∧
      (∀ j, j ≠ sIdx → w.2 j = σ j) ∧
      (w.1.1.1 = none ∨ ∃ e, w.1.1.1 = some (.inr sIdx, e)) := by
    intro hs_mid rc_mid σ_mid hc_m hse_m hσ_m k_tr hk_none hk_some hw_tr
    rcases runPubIdeal_liftFSMultiDFBucket_transmit_support C ℓ encT idOf N sIdx hdr pm hs_mid k_tr
        rc_mid σ_mid w hw_tr with ⟨v, _, hwv⟩
    cases hv1 : v.1 with
    | none =>
      simp only [hv1, hk_none, runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hwv
      subst hwv; exact ⟨hc_m, hse_m, fun j hj => by simp [Function.update_of_ne hj, hσ_m j hj], Or.inl rfl⟩
    | some e =>
      rcases hk_some e hs_mid with ⟨hs_k', hk_eq, hc_k', hse_k'⟩
      simp only [hv1, hk_eq, runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hwv
      subst hwv
      exact ⟨hc_k'.trans hc_m, hse_k'.trans hse_m,
        fun j hj => by simp [Function.update_of_ne hj, hσ_m j hj], Or.inr ⟨e, rfl⟩⟩
  by_cases hcond : (!(ctx.safeCh (2 + Δcka) P) && !((hs₁.book sIdx).getD {}).sCorr) = true
  · simp only [hcond, ↓reduceIte, StateT.run_bind] at hw
    rcases runPubIdeal_liftFSMultiDFBucket_corruptSender_support C ℓ encT idOf N sIdx hs₁ _ rc σ w hw with ⟨v, _, hwv⟩
    cases hv1 : v.1 with
    | none =>
      simp only [hv1, StateT.run_pure, Bool.not_false, ↓reduceIte,
        runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hwv
      subst hwv; exact ⟨rfl, rfl, fun j hj => Function.update_of_ne hj v.2 σ, Or.inl rfl⟩
    | some _ =>
      simp only [hv1, StateT.run_bind, StateT.run_modify, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hwv
      refine htr_tail _ rc (Function.update σ sIdx v.2) ?_ ?_
        (fun j hj => Function.update_of_ne hj v.2 σ) _ (fun _ => rfl) ?_ hwv
      · rfl
      · rfl
      · intro e hs_k; simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
        exact ⟨_, rfl, rfl, rfl⟩
  · have hcf : (!(ctx.safeCh (2 + Δcka) P) && !((hs₁.book sIdx).getD {}).sCorr) = false :=
      Bool.not_eq_true _ |>.mp hcond
    simp only [hcf, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, Bool.not_true] at hw
    refine htr_tail hs₁ rc σ rfl rfl (fun _ _ => rfl) _ (fun _ => rfl) ?_ hw
    intro e hs_k; simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
    exact ⟨_, rfl, rfl, rfl⟩

theorem fsRecv_inr_bucket_any_support
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (u sIdx : ℕ)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hs₁ : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : ((Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
        ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × _) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).fsRecv
        ctx P u (.inr sIdx) hdr e rec).run hs₁) rc σ)) :
    w.1.1.2.cache = hs₁.cache ∧
    w.1.1.2.sessions = hs₁.sessions ∧
    (∀ j, j ≠ sIdx → w.2 j = σ j) ∧
    (w.1.1.1 = none ∨ w.1.1.1 = some none ∨
      ∃ i' m', w.1.1.1 = some (some (.inr sIdx, i', m'))) := by
  dsimp only [hooksFSMultiDFBucketPaper] at hw
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
  generalize ((hs₁.book sIdx).getD {}).fsTrans.find? _ = matched at hw
  let KFin := Option (ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) ×
      FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) →
    OracleComp (PubMultiSpec Pt ℓ)
      (Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
        ℕ × (LibsignalMsgPublicPart × Plain ℓ))) ×
        FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
  let KGood (k_fin : KFin) : Prop :=
    (∀ hs_0, k_fin (none, hs_0) = pure (none, hs_0)) ∧
    (∀ hs_0, k_fin (some .rejected, hs_0) = pure (some none, hs_0)) ∧
    (∀ i mo' hs_0, ∃ hs_0',
      k_fin (some (.accepted i mo'), hs_0) =
        pure (match mo', rec with
          | some m, _ => some (some (.inr sIdx, i, m))
          | none, some r => some (some (.inr sIdx, i, r.msg))
          | none, none => none, hs_0') ∧
      hs_0'.cache = hs_0.cache ∧ hs_0'.sessions = hs_0.sessions)
  let Goal : Prop := w.1.1.2.cache = hs₁.cache ∧ w.1.1.2.sessions = hs₁.sessions ∧
    (∀ j, j ≠ sIdx → w.2 j = σ j) ∧
    (w.1.1.1 = none ∨ w.1.1.1 = some none ∨ ∃ i' m', w.1.1.1 = some (some (.inr sIdx, i', m')))
  show Goal
  have hfin_k : ∀ res hs_k rc_k (σ_k : ℕ → Option (IdealHSt Pt ℓ)) (k_fin : KFin),
      hs_k.cache = hs₁.cache → hs_k.sessions = hs₁.sessions → (∀ j, j ≠ sIdx → σ_k j = σ j) →
      KGood k_fin → w ∈ support (runPubIdeal C ℓ encT idOf N false (k_fin (res, hs_k)) rc_k σ_k) → Goal := by
    rintro res hs_k rc_k σ_k k_fin hc_k hse_k hσ_k ⟨hk_none, hk_rej, hk_acc⟩ hw_k
    cases res with
    | none =>
      simp only [hk_none, runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_k
      subst hw_k; exact ⟨hc_k, hse_k, hσ_k, Or.inl rfl⟩
    | some rr =>
      cases rr with
      | rejected =>
        simp only [hk_rej, runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_k
        subst hw_k; exact ⟨hc_k, hse_k, hσ_k, Or.inr (Or.inl rfl)⟩
      | accepted i mo' =>
        rcases hk_acc i mo' hs_k with ⟨hs_0', hk_eq, hc_0', hse_0'⟩
        rw [hk_eq] at hw_k
        cases mo' with
        | some m =>
          simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_k
          subst hw_k; exact ⟨hc_0'.trans hc_k, hse_0'.trans hse_k, hσ_k, Or.inr (Or.inr ⟨i, m, rfl⟩)⟩
        | none =>
          cases rec with
          | some r =>
            simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_k
            subst hw_k; exact ⟨hc_0'.trans hc_k, hse_0'.trans hse_k, hσ_k, Or.inr (Or.inr ⟨i, r.msg, rfl⟩)⟩
          | none =>
            simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_k
            subst hw_k; exact ⟨hc_0'.trans hc_k, hse_0'.trans hse_k, hσ_k, Or.inl rfl⟩
  cases matched with
  | some m0 =>
    have hdl_run : ∀ (k_fin : KFin), KGood k_fin →
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          ((liftFSMultiDFBucket sIdx (CryptoGames.FSAEAD.deliverQuery hdr e)).run hs₁ >>= k_fin) rc σ) → Goal := by
      intro k_fin hkg hw_dl
      rcases runPubIdeal_liftFSMultiDFBucket_deliver_support C ℓ encT idOf N sIdx hdr e hs₁ k_fin rc σ w hw_dl with
        ⟨_, hw_none⟩ | ⟨p, _, v, _, hwv⟩
      · exact hfin_k none hs₁ rc σ k_fin rfl rfl (fun _ _ => rfl) hkg hw_none
      · exact hfin_k (v.1.map (withPub p)) hs₁ rc (Function.update σ sIdx v.2) k_fin
          rfl rfl (fun j hj => Function.update_of_ne hj v.2 σ) hkg hwv
    simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, Bool.not_true, Option.isSome_some] at hw
    refine hdl_run _ ⟨fun _ => rfl, fun _ => rfl, ?_⟩ hw
    intro i mo' hs_0; cases mo' <;> cases rec <;>
      simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_modify, StateT.run_pure] <;>
      exact ⟨_, rfl, rfl, rfl⟩
  | none =>
    have hij_run : ∀ hs_m rc_m (σ_m : ℕ → Option (IdealHSt Pt ℓ)) (k_fin : KFin),
        hs_m.cache = hs₁.cache → hs_m.sessions = hs₁.sessions → (∀ j, j ≠ sIdx → σ_m j = σ j) → KGood k_fin →
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          ((liftFSMultiDFBucket sIdx (CryptoGames.FSAEAD.injectQuery hdr e)).run hs_m >>= k_fin) rc_m σ_m) → Goal := by
      intro hs_m rc_m σ_m k_fin hc_m hse_m hσ_m hkg hw_ij
      rcases runPubIdeal_liftFSMultiDFBucket_inject_support C ℓ encT idOf N sIdx hdr e hs_m k_fin
          rc_m σ_m w hw_ij with ⟨_, hw_none⟩ | ⟨p, _, v, _, hwv⟩
      · exact hfin_k (if rc_m sIdx then none else some .rejected) hs_m rc_m σ_m k_fin
          hc_m hse_m hσ_m hkg hw_none
      · exact hfin_k (v.1.map (withPub p)) hs_m rc_m (Function.update σ_m sIdx v.2) k_fin
          hc_m hse_m (fun j hj => by simp [Function.update_of_ne hj, hσ_m j hj]) hkg hwv
    by_cases hcond : (!(healedBy ctx.tL (2 + Δcka) u) && !((hs₁.book sIdx).getD {}).sCorr) = true
    · simp only [Option.isNone_none, Bool.true_and, hcond, ↓reduceIte, StateT.run_bind] at hw
      rcases runPubIdeal_liftFSMultiDFBucket_corruptSender_support C ℓ encT idOf N sIdx hs₁ _ rc σ w hw with ⟨v, _, hwv⟩
      cases hv1 : v.1 with
      | none =>
        simp only [hv1, StateT.run_pure, Bool.not_false, ↓reduceIte,
          runPubIdeal, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hwv
        subst hwv; exact ⟨rfl, rfl, fun j hj => Function.update_of_ne hj v.2 σ, Or.inl rfl⟩
      | some _ =>
        simp only [hv1, StateT.run_bind, StateT.run_modify, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hwv
        refine hij_run _ rc (Function.update σ sIdx v.2) _ ?_ ?_
          (fun j hj => Function.update_of_ne hj v.2 σ) ⟨fun _ => rfl, fun _ => rfl, ?_⟩ hwv
        · rfl
        · rfl
        · intro i mo' hs_0; cases mo' <;> cases rec <;>
            simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte, StateT.run_modify, StateT.run_pure] <;>
            exact ⟨_, rfl, rfl, rfl⟩
    · have hcf : (!(healedBy ctx.tL (2 + Δcka) u) && !((hs₁.book sIdx).getD {}).sCorr) = false :=
        Bool.not_eq_true _ |>.mp hcond
      simp only [Option.isNone_none, Bool.true_and, hcf, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, Bool.not_true, Option.isSome_none] at hw
      refine hij_run hs₁ rc σ _ rfl rfl (fun _ _ => rfl) ⟨fun _ => rfl, fun _ => rfl, ?_⟩ hw
      intro i mo' hs_0; cases mo' <;> cases rec <;>
        simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte, StateT.run_modify, StateT.run_pure] <;>
        exact ⟨_, rfl, rfl, rfl⟩

/-! ## 2. Target-Epoch (`EpochCleanAt`) `fsRecv` & `fsSend` Theorems -/

@[expose] def EpochCleanAt {ℓ : ℕ} (q Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (es : BucketEState Pt ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  EpochPre q tL t es σ ∨ EpochIdeal q Δcka tL t es σ

theorem corruptSender_fsRecv_bucket_clean
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka : ℕ) (tL : Option ℕ) (t sIdx : ℕ)
    (es : BucketEState Pt ℓ)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hcl : EpochCleanAt q Δcka tL t es σ)
    (hnot_heal : healedBy es.g.tL (2 + Δcka) t = false)
    (hsafe_or_pin :
      healedBy es.g.tL (2 + Δcka) t = true ∨
      (∃ P, (es.g.st P).vR t = some (.inr sIdx)) ∨
      (0 < t ∧ (∃ r_hdr ∈ es.g.trans, r_hdr.pos.epoch = t) ∧
        ∃ Tc σc k, es.h.cache t = some (Tc, σc, k, some sIdx)))
    {Sig K I β : Type}
    (hs : FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32))
    (k_cont : Option (RatchetSenderState (BitVec 256)) ×
      FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32) →
      OracleComp (PubMultiSpec Pt ℓ) β)
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMultiDFBucket sIdx CryptoGames.FSAEAD.corruptSenderQuery).run hs >>= k_cont) rc σ)) :
    ∃ ss_out st₁,
      EpochCleanAt q Δcka tL t es (Function.update σ sIdx (some st₁)) ∧
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        (k_cont (some ss_out, hs)) rc (Function.update σ sIdx (some st₁))) := by
  rcases hcl with hpre | ⟨s₀, hidl⟩
  · rcases hsafe_or_pin with hheal | ⟨P, hvR⟩ | ⟨_, _, Tc, σc, k, hcache⟩
    · rw [hnot_heal] at hheal; cases hheal
    · rw [hpre.2.2.2.1 P] at hvR; cases hvR
    · rw [hpre.2.2.2.2.2.1] at hcache; cases hcache
  · rcases hidl with ⟨hdiv, hep, hct_idx, hvS_eq, hvS_all, hunused, hnone_tr, hsome, hvR, hvR_ge, hpin⟩
    have hsIdx_eq : sIdx = s₀ := by
      rcases hsafe_or_pin with hheal | ⟨P, hvRp⟩ | ⟨hpos, _, Tc, σc, k, hcache⟩
      · rw [hnot_heal] at hheal; cases hheal
      · exact Sum.inr.inj (hvR P (.inr sIdx) hvRp)
      · rcases hpin hpos with ⟨Tc', σc', k', hcache', _⟩
        rw [hcache] at hcache'
        injection hcache' with hq
        exact Option.some.inj (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hq).2).2).2
    subst hsIdx_eq
    rcases runPubIdeal_liftFSMultiDFBucket_corruptSender_support C ℓ encT idOf N sIdx hs k_cont
        rc σ w hw with ⟨u, hu, hwu⟩
    have hcs_body : ∀ (st₀ st₁ : IdealHSt Pt ℓ),
        st₀.1.ended = false →
        (σ sIdx = none → st₀.1.lastSentIdx = 0 ∧ ∀ r0 ∈ es.g.trans, r0.pos.epoch ≠ t) →
        (∀ st_ex, σ sIdx = some st_ex → st₀ = st_ex) →
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) →
        (∀ r0 ∈ es.g.trans, r0.pos.epoch = t → r0.pos.idx ≤ st₀.1.lastSentIdx) →
        (∀ r0 ∈ es.g.trans, r0.pos.epoch = t → r0.pos ∉ es.g.comp →
          st₀.1.isCompromised r0.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r0.pos.idx → (r_fs.ad.1, r_fs.ct) = r0.ct)) →
        u.2 = some st₁ →
        (u.1, st₁) ∈ support (((corruptSenderH (lChainPRG C.F) (hpIdeal N false) ()).run st₀ : ProbComp _)) →
        ∃ ss_out st₁',
          EpochCleanAt q Δcka tL t es (Function.update σ sIdx (some st₁')) ∧
          w ∈ support (runPubIdeal C ℓ encT idOf N false
            (k_cont (some ss_out, hs)) rc (Function.update σ sIdx (some st₁'))) := by
      intro st₀ st₁ hend₀ hif_none hif_some hit₀ hidx₀ hunc₀ hu2 hu_cs
      rw [hu2] at hwu
      rcases corruptSenderH_hpIdeal_false_step_spec (lChainPRG C.F) N st₀ st₁ u.1 hend₀ hu_cs with
        ⟨hsome_res, hend₁, hsc₁, hls₁, hit₁⟩
      rcases Option.isSome_iff_exists.mp hsome_res with ⟨ss_out, hu1⟩
      refine ⟨ss_out, st₁, Or.inr ⟨sIdx, hdiv, hep, hct_idx, hvS_eq, ?_, ?_,
        by intro h; simp at h, ?_, hvR, hvR_ge, hpin⟩, hu1 ▸ hwu⟩
      · intro Q idx hblk hvSQ
        rcases hvS_all Q idx hblk hvSQ with ⟨rfl, rfl, hsendQ⟩
        refine ⟨rfl, rfl, fun hsIn => ?_⟩
        rcases hsendQ hsIn with ⟨hep_t, ⟨hnone, hidx0⟩ | ⟨st_ex, hsome_ex, hls_ex⟩⟩
        · exact ⟨hep_t, Or.inr ⟨st₁, by simp, hls₁.trans ((hif_none hnone).1.trans hidx0.symm)⟩⟩
        · have hst_eq := hif_some st_ex hsome_ex; subst hst_eq
          exact ⟨hep_t, Or.inr ⟨st₁, by simp, hls₁.trans hls_ex⟩⟩
      · intro idx st hblk hne_idx hst_j
        rw [Function.update_of_ne hne_idx] at hst_j
        exact hunused idx st hblk hne_idx hst_j
      · intro st hst
        simp only [Function.update_self, Option.some.injEq] at hst; subst hst
        refine ⟨hend₁, ?_, fun r0 hr0 hep0 => hls₁ ▸ hidx₀ r0 hr0 hep0,
          fun hh => (by rw [hnot_heal] at hh; cases hh), ?_⟩
        · intro r_fs hr_fs; rw [hit₁] at hr_fs; rw [hls₁]; exact hit₀ r_fs hr_fs
        · intro r0 hr0 hep0 hnc0
          rcases hunc₀ r0 hr0 hep0 hnc0 with ⟨hc_f, hct_m⟩
          have hle_ls := hidx₀ r0 hr0 hep0
          refine ⟨?_, fun r_fs hr_fs => hct_m r_fs (hit₁ ▸ hr_fs)⟩
          cases hsc0 : st₀.1.senderCorruptedAt with
          | none => simp [HState.isCompromised, hsc₁, hsc0, Nat.not_lt.mpr hle_ls]
          | some _ => simpa [HState.isCompromised, hsc₁, hsc0] using hc_f
    cases hσ0 : σ sIdx with
    | none =>
      rw [hσ0] at hu
      simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
      rcases hu with ⟨b, _, v0, hv0, rfl⟩
      exact hcs_body (hInit b .unknown) v0.2 rfl (fun _ => ⟨rfl, hnone_tr hσ0⟩)
        (fun _ h => by rw [hσ0] at h; cases h) (by simp [hInit])
        (fun r0 hr0 hep0 => (hnone_tr hσ0 r0 hr0 hep0).elim)
        (fun r0 hr0 hep0 _ => (hnone_tr hσ0 r0 hr0 hep0).elim) rfl hv0
    | some st₀ =>
      rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
      rcases hu with ⟨v0, hv0, hvu⟩
      simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
      subst hvu
      have h5 := hsome st₀ hσ0
      exact hcs_body st₀ v0.2 h5.1 (fun h => by rw [hσ0] at h; cases h)
        (fun _ h => Option.some.inj (hσ0.symm.trans h)) h5.2.1 h5.2.2.1 h5.2.2.2.2 rfl hv0

theorem fsRecv_inr_bucket_forged_not_nontrivial
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t sIdx : ℕ) (P : Party)
    (es : BucketEState Pt ℓ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hblk : sIdx / q = t - healEpoch tL)
    (hcl : EpochCleanAt q Δcka tL t es σ)
    (hsafe_or_pin :
      healedBy es.g.tL (2 + Δcka) t = true ∨
      (∃ Q, (es.g.st Q).vR t = some (.inr sIdx)) ∨
      (0 < t ∧ (∃ r_hdr ∈ es.g.trans, r_hdr.pos.epoch = t) ∧
        ∃ Tc σc k, es.h.cache t = some (Tc, σc, k, some sIdx)))
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (ht : hdr.1 = t)
    (hnot_tr : (es.g.inTransit (Party.senderOf t) (hdr, e)).isSome = false)
    (hs₁ : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (w : ((Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
        ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × _) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).fsRecv
        es.g P t (.inr sIdx) hdr e none).run hs₁) rc σ)) :
    ∀ v' i' m', w.1.1.1 = some (some (v', i', m')) →
      v' = .inr sIdx ∧
      healedBy es.g.tL (2 + Δcka) t = false ∧
      es.g.trivial (2 + Δcka) ⟨Party.senderOf t, t, i'⟩ = true := by
  let _ := ht
  dsimp only [hooksFSMultiDFBucketPaper] at hw
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
  have hsess_at :
      ∀ (σ_cur : ℕ → Option (IdealHSt Pt ℓ)), EpochCleanAt q Δcka tL t es σ_cur →
      ∀ st₀, (σ_cur sIdx = some st₀ ∨ (σ_cur sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx) ∧
        (healedBy es.g.tL (2 + Δcka) t = true →
          st₀.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₀.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
          st₀.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct)) := by
    intro σ_cur hcl_cur st₀ hst₀
    rcases hst₀ with hsome | ⟨_, b, rfl⟩
    · rcases hcl_cur with hpre | ⟨s₀, hidl⟩
      · rcases hpre.2.2.2.2.2.2 sIdx st₀ hblk hsome with ⟨_, hsc, hit, _⟩
        exact ⟨by simp [hit], fun _ => ⟨hsc, by simp [hit]⟩,
          fun _ _ _ _ => ⟨isCompromised_of_senderCorruptedAt_none st₀.1 hsc _, by simp [hit]⟩⟩
      · by_cases heq : sIdx = s₀
        · subst heq
          have hst := hidl.2.2.2.2.2.2.2.1 st₀ hsome
          exact ⟨fun r hr => (hst.2.1 r hr).1, hst.2.2.2.1, hst.2.2.2.2⟩
        · rcases hidl.2.2.2.2.2.1 sIdx st₀ hblk heq hsome with ⟨_, hsc, hit, _⟩
          exact ⟨by simp [hit], fun _ => ⟨hsc, by simp [hit]⟩,
            fun _ _ _ _ => ⟨isCompromised_of_senderCorruptedAt_none st₀.1 hsc _, by simp [hit]⟩⟩
    · exact ⟨by simp [hInit], fun _ => ⟨rfl, by simp [hInit]⟩, fun _ _ _ _ => ⟨rfl, by simp [hInit]⟩⟩
  have htriv_of_dl : ∀ st₀,
      (σ sIdx = some st₀ ∨ (σ sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
      ∀ r_fs ∈ st₀.1.inTransit, r_fs.ad.1 = hdr → r_fs.ct = e →
      healedBy es.g.tL (2 + Δcka) t = false ∧
      es.g.trivial (2 + Δcka) ⟨Party.senderOf t, t, r_fs.idx⟩ = true := by
    intro st₀ hst₀ r_fs hr_fs had hct
    have hst := hsess_at σ hcl st₀ hst₀
    by_cases hheal : healedBy es.g.tL (2 + Δcka) t = true
    · rcases (hst.2.1 hheal).2 r_fs hr_fs with ⟨m, hm_tr⟩
      rw [had, hct] at hm_tr
      have hit_some : (es.g.inTransit (Party.senderOf t) (hdr, e)).isSome = true := by
        unfold GameState.inTransit
        rw [Option.isSome_iff_ne_none]
        intro hfn
        have := List.find?_eq_none.mp hfn _ hm_tr
        simp at this
      rw [hnot_tr] at hit_some; cases hit_some
    · simp only [Bool.not_eq_true] at hheal
      refine ⟨hheal, ?_⟩
      by_cases hex : ∃ r ∈ es.g.trans, r.pos = ⟨Party.senderOf t, t, r_fs.idx⟩
      · rcases hex with ⟨r, hr_mem, hr_pos⟩
        by_cases hcomp : r.pos ∈ es.g.comp
        · simp [GameState.trivial, hr_pos ▸ hcomp]
        · have hct_eq := (hst.2.2 r hr_mem (by rw [hr_pos]) hcomp).2 r_fs hr_fs (by rw [hr_pos])
          rw [had, hct] at hct_eq
          have hit_some : (es.g.inTransit (Party.senderOf t) (hdr, e)).isSome = true := by
            unfold GameState.inTransit
            rw [Option.isSome_iff_ne_none]
            intro hfn
            have := List.find?_eq_none.mp hfn r hr_mem
            simp [hr_pos, hct_eq.symm] at this
          rw [hnot_tr] at hit_some; cases hit_some
      · simp only [GameState.trivial, hheal, Bool.not_false, Bool.and_true, Bool.or_eq_true]
        right
        rw [Bool.not_eq_true', List.any_eq_false]
        intro r hr_mem
        simp only [beq_iff_eq]
        intro hr_pos
        exact hex ⟨r, hr_mem, hr_pos⟩
  have htriv_of_ij : ∀ (σ_cur : ℕ → Option (IdealHSt Pt ℓ)), EpochCleanAt q Δcka tL t es σ_cur →
      ∀ st₀, (σ_cur sIdx = some st₀ ∨ (σ_cur sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
      ∀ i', st₀.1.isCompromised i' = true →
      healedBy es.g.tL (2 + Δcka) t = false ∧
      es.g.trivial (2 + Δcka) ⟨Party.senderOf t, t, i'⟩ = true := by
    intro σ_cur hcl_cur st₀ hst₀ i' hcomp_fs
    have hst := hsess_at σ_cur hcl_cur st₀ hst₀
    by_cases hheal : healedBy es.g.tL (2 + Δcka) t = true
    · have hsc := (hst.2.1 hheal).1
      rw [isCompromised_of_senderCorruptedAt_none st₀.1 hsc i'] at hcomp_fs
      cases hcomp_fs
    · simp only [Bool.not_eq_true] at hheal
      refine ⟨hheal, ?_⟩
      by_cases hex : ∃ r ∈ es.g.trans, r.pos = ⟨Party.senderOf t, t, i'⟩
      · rcases hex with ⟨r, hr_mem, hr_pos⟩
        by_cases hcomp : r.pos ∈ es.g.comp
        · simp [GameState.trivial, hr_pos ▸ hcomp]
        · have hc_false := (hst.2.2 r hr_mem (by rw [hr_pos]) hcomp).1
          rw [hr_pos] at hc_false
          dsimp only at hc_false
          rw [hc_false] at hcomp_fs; cases hcomp_fs
      · simp only [GameState.trivial, hheal, Bool.not_false, Bool.and_true, Bool.or_eq_true]
        right
        rw [Bool.not_eq_true', List.any_eq_false]
        intro r hr_mem
        simp only [beq_iff_eq]
        intro hr_pos
        exact hex ⟨r, hr_mem, hr_pos⟩
  generalize ((hs₁.book sIdx).getD {}).fsTrans.find? _ = matched at hw
  cases matched with
  | some m0 =>
    simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, Bool.not_true, Option.isSome_some] at hw
    rcases runPubIdeal_liftFSMultiDFBucket_deliver_support C ℓ encT idOf N sIdx hdr e hs₁ _ rc σ w hw with
      ⟨_, hw_none⟩ | ⟨p, _, u, hu, hwu⟩
    · simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hw_none
      subst hw_none; intro _ _ _ h; simp at h
    · have hdl : ∀ (st₀ st' : IdealHSt Pt ℓ),
          (σ sIdx = some st₀ ∨ (σ sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
          u.2 = some st' →
          (u.1, st') ∈ support (((deliverH (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hpIdeal N false) (DG (lChainPRG C.F))
            none ((hdr, p), e)).run st₀ : ProbComp _)) →
          ∀ v' i' m', w.1.1.1 = some (some (v', i', m')) →
            v' = .inr sIdx ∧
            healedBy es.g.tL (2 + Δcka) t = false ∧
            es.g.trivial (2 + Δcka) ⟨Party.senderOf t, t, i'⟩ = true := by
        intro st₀ st' hst₀ _ hu_dl v' i' m' hacc
        rcases deliverH_hpIdeal_false_step_spec _ _ maxForwardJumps N ((hdr, p), e) st₀ st' u.1
            (hsess_at σ hcl st₀ hst₀).1 hu_dl with ⟨hu1, _⟩ | ⟨r_fs, hr_fs, had, hct, _, _, _, hres⟩
        · simp only [hu1, Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hwu
          subst hwu; simp at hacc
        · rcases hres with ⟨hu1, _⟩ | ⟨mo', hu1, _⟩
          · simp only [hu1, Option.map_some, withPub, StateT.run_pure, runPubIdeal,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hwu
            subst hwu; simp at hacc
          · simp only [hu1, Option.map_some, withPub, StateT.run_bind, StateT.run_get, pure_bind,
              StateT.run_modify] at hwu
            cases mo' with
            | none =>
              simp only [Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hwu
              subst hwu; simp at hacc
            | some m_raw =>
              simp only [Option.map_some, StateT.run_pure, runPubIdeal, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hwu
              subst hwu
              injection hacc with h1; injection h1 with h2
              rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
              rcases Prod.mk.inj h3 with ⟨rfl, _⟩
              have htr := htriv_of_dl st₀ hst₀ r_fs hr_fs (congrArg Prod.fst had) hct
              exact ⟨rfl, htr.1, htr.2⟩
      cases hσ0 : σ sIdx with
      | none =>
        rw [hσ0] at hu
        simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
        rcases hu with ⟨b, _, v0, hv0, rfl⟩
        exact hdl (hInit b .unknown) v0.2 (Or.inr ⟨hσ0, b, rfl⟩) rfl hv0
      | some st₀ =>
        rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
        rcases hu with ⟨v0, hv0, hvu⟩
        simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
        subst hvu
        exact hdl st₀ v0.2 (Or.inl hσ0) rfl hv0
  | none =>
    have hij_tail : ∀ hs_cur (σ_cur : ℕ → Option (IdealHSt Pt ℓ)),
        EpochCleanAt q Δcka tL t es σ_cur →
        ∀ (k_ij : Option (ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) ×
            FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) →
          OracleComp (PubMultiSpec Pt ℓ)
            (Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
              ℕ × (LibsignalMsgPublicPart × Plain ℓ))) ×
              FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))),
        (∀ idx0 mo0 hs_k, ∃ hs_k',
          k_ij (some (.accepted idx0 mo0), hs_k) =
            pure (mo0.map (fun m => some (.inr sIdx, idx0, m)), hs_k')) →
        (∀ hs_k, k_ij (none, hs_k) = pure (none, hs_k)) →
        (∀ hs_k, k_ij (some .rejected, hs_k) = pure (some none, hs_k)) →
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          ((liftFSMultiDFBucket sIdx (CryptoGames.FSAEAD.injectQuery hdr e)).run hs_cur >>= k_ij) rc σ_cur) →
        ∀ v' i' m', w.1.1.1 = some (some (v', i', m')) →
          v' = .inr sIdx ∧
          healedBy es.g.tL (2 + Δcka) t = false ∧
          es.g.trivial (2 + Δcka) ⟨Party.senderOf t, t, i'⟩ = true := by
      intro hs_cur σ_cur hcl_cur k_ij hk_acc hk_none hk_rej hw_ij
      rcases runPubIdeal_liftFSMultiDFBucket_inject_support C ℓ encT idOf N sIdx hdr e hs_cur k_ij
          rc σ_cur w hw_ij with ⟨_, hw_none⟩ | ⟨p, _, u, hu, hwu⟩
      · cases hrc : rc sIdx with
        | false =>
          simp only [hrc, Bool.false_eq_true, ↓reduceIte, hk_rej, runPubIdeal, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_none
          subst hw_none; intro _ _ _ h; simp at h
        | true =>
          simp only [hrc, ↓reduceIte, hk_none, runPubIdeal, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hw_none
          subst hw_none; intro _ _ _ h; simp at h
      · have hij : ∀ (st₀ st' : IdealHSt Pt ℓ),
            (σ_cur sIdx = some st₀ ∨ (σ_cur sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
            u.2 = some st' →
            (u.1, st') ∈ support (((injectH (lAeadR C protoSignalCodec ℓ encT idOf)
              (lChainPRG C.F) maxForwardJumps (hpIdeal N false) (DG (lChainPRG C.F))
              none ((hdr, p), e)).run st₀ : ProbComp _)) →
            ∀ v' i' m', w.1.1.1 = some (some (v', i', m')) →
              v' = .inr sIdx ∧
              healedBy es.g.tL (2 + Δcka) t = false ∧
              es.g.trivial (2 + Δcka) ⟨Party.senderOf t, t, i'⟩ = true := by
          intro st₀ st' hst₀ _ hu_ij v' i' m' hacc
          have hspec := injectH_hpIdeal_false_step_spec _ _ maxForwardJumps N ((hdr, p), e)
            st₀ st' u.1 hu_ij
          cases hu1 : u.1 with
          | none =>
            simp only [hu1, Option.map_none, hk_none, runPubIdeal, simulateQ_pure, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hwu
            subst hwu; simp at hacc
          | some rr =>
            cases rr with
            | rejected =>
              simp only [hu1, Option.map_some, withPub, hk_rej, runPubIdeal,
                simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hwu
              subst hwu; simp at hacc
            | accepted idx0 mo0 =>
              have hcomp := (hspec.2.2.2.2.1 idx0 mo0 hu1).2
              simp only [hu1, Option.map_some, withPub] at hwu
              cases mo0 with
              | none =>
                rcases hk_acc idx0 none hs_cur with ⟨hs_k', hk_eq⟩
                simp only [Option.map_none, hk_eq, runPubIdeal, simulateQ_pure, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff] at hwu
                subst hwu; simp at hacc
              | some m_raw =>
                rcases hk_acc idx0 (some (p, m_raw)) hs_cur with ⟨hs_k', hk_eq⟩
                simp only [Option.map_some, hk_eq, runPubIdeal, simulateQ_pure, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff] at hwu
                subst hwu
                injection hacc with h1; injection h1 with h2
                rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
                rcases Prod.mk.inj h3 with ⟨rfl, _⟩
                have htr := htriv_of_ij σ_cur hcl_cur st₀ hst₀ idx0 hcomp
                exact ⟨rfl, htr.1, htr.2⟩
        cases hσ0 : σ_cur sIdx with
        | none =>
          rw [hσ0] at hu
          simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
          rcases hu with ⟨b, _, v0, hv0, rfl⟩
          exact hij (hInit b .unknown) v0.2 (Or.inr ⟨hσ0, b, rfl⟩) rfl hv0
        | some st₀ =>
          rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
          rcases hu with ⟨v0, hv0, hvu⟩
          simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
          subst hvu
          exact hij st₀ v0.2 (Or.inl hσ0) rfl hv0
    by_cases hguard_cs : (!(healedBy es.g.tL (2 + Δcka) t) && !((hs₁.book sIdx).getD {}).sCorr) = true
    · have hnot_heal : healedBy es.g.tL (2 + Δcka) t = false := by
        rcases Bool.and_eq_true_iff.mp hguard_cs with ⟨h1, _⟩
        exact Bool.not_eq_true' _ |>.mp h1
      simp only [Option.isNone_none, Bool.true_and, hguard_cs, ↓reduceIte,
        StateT.run_bind] at hw
      rcases corruptSender_fsRecv_bucket_clean C ℓ encT idOf q N Δcka tL t sIdx
          es rc σ hcl hnot_heal hsafe_or_pin hs₁ _ w hw with ⟨ss_out, st₁, hcl₁, hw_cs⟩
      simp only [StateT.run_bind, StateT.run_modify, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hw_cs
      exact hij_tail _ _ hcl₁ _
        (fun idx0 mo0 hs_k => by
          cases mo0 <;>
            simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte, StateT.run_modify, StateT.run_pure,
              Option.map_none, Option.map_some] <;>
            exact ⟨_, rfl⟩)
        (fun _ => rfl) (fun _ => rfl) hw_cs
    · have hgf : (!(healedBy es.g.tL (2 + Δcka) t) && !((hs₁.book sIdx).getD {}).sCorr) = false :=
        Bool.not_eq_true _ |>.mp hguard_cs
      simp only [Option.isNone_none, Bool.true_and, hgf, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, Bool.not_true, Option.isSome_none] at hw
      exact hij_tail hs₁ σ hcl _
        (fun idx0 mo0 hs_k => by
          cases mo0 <;>
            simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte, StateT.run_modify, StateT.run_pure,
              Option.map_none, Option.map_some] <;>
            exact ⟨_, rfl⟩)
        (fun _ => rfl) (fun _ => rfl) hw

theorem fsRecv_inr_bucket_step_post
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t sIdx : ℕ) (P : Party)
    (es : BucketEState Pt ℓ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (hblk : sIdx / q = t - healEpoch tL)
    (hcl : EpochCleanAt q Δcka tL t es σ)
    (hsafe_or_pin :
      healedBy es.g.tL (2 + Δcka) t = true ∨
      (∃ Q, (es.g.st Q).vR t = some (.inr sIdx)) ∨
      (0 < t ∧ (∃ r_hdr ∈ es.g.trans, r_hdr.pos.epoch = t) ∧
        ∃ Tc σc k, es.h.cache t = some (Tc, σc, k, some sIdx)))
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hs₁ : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (w : ((Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
        ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × _) × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).fsRecv
        es.g P t (.inr sIdx) hdr e rec).run hs₁) rc σ)) :
    w.1.1.1 = none ∨
    (w.1.1.1 = some none ∧ w.1.1.2.cache = hs₁.cache ∧ w.1.1.2.sessions = hs₁.sessions ∧
      (∀ j, j ≠ sIdx → w.2 j = σ j) ∧
      ∀ hs', hs'.cache t = es.h.cache t → EpochCleanAt q Δcka tL t { es with h := hs' } w.2) ∨
    (∃ i' m' s₀, ∃ st₀ st' : IdealHSt Pt ℓ,
      w.1.1.1 = some (some (.inr s₀, i', m')) ∧
      w.1.1.2.cache = hs₁.cache ∧
      w.1.1.2.sessions = hs₁.sessions ∧
      sIdx = s₀ ∧
      s₀ / q = t - healEpoch tL ∧
      t ≤ es.g.epoch (Party.senderOf t) ∧
      (∀ r ∈ es.g.trans, r.pos.epoch = t → r.ct.2.1 = r.pos.idx) ∧
      (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
      (∀ Q idx, idx / q = t - healEpoch tL → (es.g.st Q).vS = some (.inr idx) →
        Q = Party.senderOf t ∧ idx = s₀ ∧
        ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
          es.g.epoch (Party.senderOf t) = t ∧
          st₀.1.lastSentIdx = es.g.idx (Party.senderOf t))) ∧
      (∀ idx st, idx / q = t - healEpoch tL → idx ≠ s₀ → σ idx = some st →
        st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
        st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
      (∀ Q v, (es.g.st Q).vR t = some v → v = .inr s₀) ∧
      (t ≤ es.g.epoch (Party.receiverOf t) → (es.g.st (Party.receiverOf t)).vR t = some (.inr s₀)) ∧
      (0 < t → ∃ Tc σc k,
        es.h.cache t = some (Tc, σc, k, some s₀) ∧
        (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).curCkaMsg = some Tc) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.ct.1.2 = some Tc)) ∧
      (st₀.1.ended = false ∧
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
        (healedBy es.g.tL (2 + Δcka) t = true →
          st₀.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₀.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
          st₀.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) ∧
      w.2 = Function.update σ s₀ (some st') ∧
      st'.1.ended = false ∧
      st'.1.lastSentIdx = st₀.1.lastSentIdx ∧
      st'.1.senderCorruptedAt = st₀.1.senderCorruptedAt ∧
      (∀ r_fs ∈ st'.1.inTransit, r_fs ∈ st₀.1.inTransit) ∧
      (healedBy es.g.tL (2 + Δcka) t = true →
        ∃ r_fs ∈ st₀.1.inTransit, r_fs.ad.1 = hdr ∧ r_fs.ct = e ∧
          st'.1.inTransit = st₀.1.inTransit.filter (·.idx != r_fs.idx))) := by
  have hrej_pres : ∀ (σ_cur : ℕ → Option (IdealHSt Pt ℓ)), EpochCleanAt q Δcka tL t es σ_cur →
      ∀ st₀ st',
      (σ_cur sIdx = some st₀ ∨ (σ_cur sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
      st'.1.senderCorruptedAt = st₀.1.senderCorruptedAt →
      st'.1.lastSentIdx = st₀.1.lastSentIdx →
      st'.1.ended = st₀.1.ended →
      st'.1.inTransit = st₀.1.inTransit →
      ∀ hs', hs'.cache t = es.h.cache t →
        EpochCleanAt q Δcka tL t { es with h := hs' } (Function.update σ_cur sIdx (some st')) := by
    intro σ_cur hcl_cur st₀ st' hst₀ hsc hls hend hit hs' hcache
    rcases hcl_cur with hpre | ⟨s₀, hidl⟩
    · refine Or.inl ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2.1, hpre.2.2.2.2.1,
        hcache.trans hpre.2.2.2.2.2.1, fun j st hj_blk hj => ?_⟩
      by_cases heq : j = sIdx
      · subst heq; simp only [Function.update_self, Option.some.injEq] at hj; subst hj
        rcases hst₀ with hsome | ⟨_, b, rfl⟩
        · rcases hpre.2.2.2.2.2.2 j st₀ hj_blk hsome with ⟨he, hc, hi, hl⟩
          exact ⟨hend.trans he, hsc.trans hc, hit.trans hi, hls.trans hl⟩
        · exact ⟨hend, hsc, hit, hls⟩
      · rw [Function.update_of_ne heq] at hj
        exact hpre.2.2.2.2.2.2 j st hj_blk hj
    · rcases hidl with ⟨hdiv, hep, hct_idx, hvS_eq, hvS_all, hunused, hnone_tr, hsome_s₀, hvR, hvR_ge, hpin⟩
      refine Or.inr ⟨s₀, hdiv, hep, hct_idx, hvS_eq, ?_, ?_, ?_, ?_, hvR, hvR_ge,
        fun hpos => by simpa only [hcache] using hpin hpos⟩
      · intro Q idx hj_blk hvS
        rcases hvS_all Q idx hj_blk hvS with ⟨hQ, hidx, hsend⟩
        refine ⟨hQ, hidx, fun hsIn => ?_⟩
        rcases hsend hsIn with ⟨hep_t, ⟨hnone, hidx0⟩ | ⟨st, hsome, hl⟩⟩
        · refine ⟨hep_t, ?_⟩
          by_cases heq : s₀ = sIdx
          · subst heq
            rcases hst₀ with hsome | ⟨_, b, rfl⟩
            · rw [hnone] at hsome; cases hsome
            · exact Or.inr ⟨st', by simp, hls.trans hidx0.symm⟩
          · exact Or.inl ⟨by simp [Function.update_of_ne heq, hnone], hidx0⟩
        · refine ⟨hep_t, ?_⟩
          by_cases heq : s₀ = sIdx
          · subst heq
            rcases hst₀ with hsome' | ⟨hnone, _⟩
            · rw [hsome] at hsome'; injection hsome' with hst_eq; subst hst_eq
              exact Or.inr ⟨st', by simp, hls.trans hl⟩
            · rw [hsome] at hnone; cases hnone
          · exact Or.inr ⟨st, by simp [Function.update_of_ne heq, hsome], hl⟩
      · intro j st hj_blk hj_ne hj
        by_cases heq : j = sIdx
        · subst heq; simp only [Function.update_self, Option.some.injEq] at hj; subst hj
          rcases hst₀ with hsome | ⟨_, b, rfl⟩
          · rcases hunused j st₀ hj_blk hj_ne hsome with ⟨he, hc, hi, hl⟩
            exact ⟨hend.trans he, hsc.trans hc, hit.trans hi, hls.trans hl⟩
          · exact ⟨hend, hsc, hit, hls⟩
        · rw [Function.update_of_ne heq] at hj; exact hunused j st hj_blk hj_ne hj
      · intro hnone
        by_cases heq : s₀ = sIdx
        · subst heq; simp at hnone
        · rw [Function.update_of_ne heq] at hnone; exact hnone_tr hnone
      · intro st hst
        by_cases heq : s₀ = sIdx
        · subst heq; simp only [Function.update_self, Option.some.injEq] at hst; subst hst
          rcases hst₀ with hsome | ⟨hnone, b, rfl⟩
          · rw [hsc, hls, hend, hit]
            have h5 := hsome_s₀ st₀ hsome
            refine ⟨h5.1, h5.2.1, h5.2.2.1, h5.2.2.2.1, fun r hr hep_r hnc => ?_⟩
            have hr5 := h5.2.2.2.2 r hr hep_r hnc
            exact ⟨by simpa [HState.isCompromised, hsc] using hr5.1, hr5.2⟩
          · have hno_t := hnone_tr hnone
            refine ⟨hend, by simp [hit, hInit], fun r hr hep_r => (hno_t r hr hep_r).elim,
              fun _ => ⟨hsc, by simp [hit, hInit]⟩,
              fun r hr hep_r _ => (hno_t r hr hep_r).elim⟩
        · rw [Function.update_of_ne heq] at hst; exact hsome_s₀ st hst
  have hunchanged : ∀ (σ_cur : ℕ → Option (IdealHSt Pt ℓ)), EpochCleanAt q Δcka tL t es σ_cur →
      ∀ hs', hs'.cache t = es.h.cache t →
        EpochCleanAt q Δcka tL t { es with h := hs' } σ_cur := by
    intro σ_cur hcl_cur hs' hcache
    rcases hcl_cur with hpre | ⟨s₀, hidl⟩
    · exact Or.inl ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2.1, hpre.2.2.2.2.1,
        hcache.trans hpre.2.2.2.2.2.1, hpre.2.2.2.2.2.2⟩
    · exact Or.inr ⟨s₀, hidl.congr_block hcache (fun _ _ => rfl)⟩
  have hmust_s₀ : ∀ (σ_cur : ℕ → Option (IdealHSt Pt ℓ)), EpochCleanAt q Δcka tL t es σ_cur →
      (∀ idx, idx ≠ sIdx → σ_cur idx = σ idx) →
      ∀ st₀,
      (σ_cur sIdx = some st₀ ∨ (σ_cur sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
      ((∃ r_fs, r_fs ∈ st₀.1.inTransit) ∨ (∃ i', st₀.1.isCompromised i' = true)) →
      ∃ s₀, sIdx = s₀ ∧
        s₀ / q = t - healEpoch tL ∧
        t ≤ es.g.epoch (Party.senderOf t) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.ct.2.1 = r.pos.idx) ∧
        (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
        (∀ Q idx, idx / q = t - healEpoch tL → (es.g.st Q).vS = some (.inr idx) →
          Q = Party.senderOf t ∧ idx = s₀ ∧
          ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
            es.g.epoch (Party.senderOf t) = t ∧
            st₀.1.lastSentIdx = es.g.idx (Party.senderOf t))) ∧
        (∀ idx st, idx / q = t - healEpoch tL → idx ≠ s₀ → σ idx = some st →
          st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
          st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
        (∀ Q v, (es.g.st Q).vR t = some v → v = .inr s₀) ∧
        (t ≤ es.g.epoch (Party.receiverOf t) → (es.g.st (Party.receiverOf t)).vR t = some (.inr s₀)) ∧
        (0 < t → ∃ Tc σc k,
          es.h.cache t = some (Tc, σc, k, some s₀) ∧
          (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).curCkaMsg = some Tc) ∧
          (∀ r ∈ es.g.trans, r.pos.epoch = t → r.ct.1.2 = some Tc)) ∧
        (st₀.1.ended = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
          (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
          (healedBy es.g.tL (2 + Δcka) t = true →
            st₀.1.senderCorruptedAt = none ∧
            (∀ r_fs ∈ st₀.1.inTransit,
              ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
          (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
            st₀.1.isCompromised r.pos.idx = false ∧
            (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) := by
    intro σ_cur hcl_cur hσ_ne st₀ hst₀ hact_ev
    rcases hst₀ with hsome | ⟨_, b, rfl⟩
    · rcases hcl_cur with hpre | ⟨s₀, hidl⟩
      · rcases hpre.2.2.2.2.2.2 sIdx st₀ hblk hsome with ⟨_, hsc, hit, _⟩
        rcases hact_ev with ⟨r_fs, hr⟩ | ⟨i', hc⟩
        · simp [hit] at hr
        · rw [isCompromised_of_senderCorruptedAt_none st₀.1 hsc i'] at hc; cases hc
      · rcases hidl with ⟨hdiv, hep, hct_idx, hvS_eq, hvS_all, hunused, _, hsome_s₀, hvR, hvR_ge, hpin⟩
        by_cases heq : sIdx = s₀
        · subst heq
          refine ⟨sIdx, rfl, hdiv, hep, hct_idx, hvS_eq, fun Q idx hj_blk hvS => ?_, ?_,
            hvR, hvR_ge, hpin, hsome_s₀ st₀ hsome⟩
          · rcases hvS_all Q idx hj_blk hvS with ⟨hQ, hidx, hsend⟩
            refine ⟨hQ, hidx, fun hsIn => ?_⟩
            rcases hsend hsIn with ⟨hep_t, ⟨hnone, _⟩ | ⟨st_s, hst_s, hls_s⟩⟩
            · rw [hsome] at hnone; cases hnone
            · rw [hsome] at hst_s; injection hst_s with hst_eq; subst hst_eq
              exact ⟨hep_t, hls_s⟩
          · intro idx st hj_blk hne hst
            exact hunused idx st hj_blk hne ((hσ_ne idx hne).trans hst)
        · rcases hunused sIdx st₀ hblk heq hsome with ⟨_, hsc, hit, _⟩
          rcases hact_ev with ⟨r_fs, hr⟩ | ⟨i', hc⟩
          · simp [hit] at hr
          · rw [isCompromised_of_senderCorruptedAt_none st₀.1 hsc i'] at hc; cases hc
    · rcases hact_ev with ⟨r_fs, hr⟩ | ⟨i', hc⟩
      · simp [hInit] at hr
      · simp [hInit, HState.isCompromised] at hc
  have hct_idx_at : ∀ st₀,
      (σ sIdx = some st₀ ∨ (σ sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
      ∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx := by
    intro st₀ hst₀
    rcases hst₀ with hsome | ⟨_, b, rfl⟩
    · rcases hcl with hpre | ⟨s₀, hidl⟩
      · rcases hpre.2.2.2.2.2.2 sIdx st₀ hblk hsome with ⟨_, _, hit, _⟩; simp [hit]
      · by_cases heq : sIdx = s₀
        · subst heq; exact fun r hr => ((hidl.2.2.2.2.2.2.2.1 st₀ hsome).2.1 r hr).1
        · rcases hidl.2.2.2.2.2.1 sIdx st₀ hblk heq hsome with ⟨_, _, hit, _⟩; simp [hit]
    · simp [hInit]
  let Post (w : ((Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
      ℕ × (LibsignalMsgPublicPart × Plain ℓ))) ×
      FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) ×
      (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ))) : Prop :=
    w.1.1.1 = none ∨
    (w.1.1.1 = some none ∧ w.1.1.2.cache = hs₁.cache ∧ w.1.1.2.sessions = hs₁.sessions ∧
      (∀ j, j ≠ sIdx → w.2 j = σ j) ∧
      ∀ hs', hs'.cache t = es.h.cache t → EpochCleanAt q Δcka tL t { es with h := hs' } w.2) ∨
    (∃ i' m' s₀, ∃ st₀ st' : IdealHSt Pt ℓ,
      w.1.1.1 = some (some (.inr s₀, i', m')) ∧ w.1.1.2.cache = hs₁.cache ∧
      w.1.1.2.sessions = hs₁.sessions ∧ sIdx = s₀ ∧ s₀ / q = t - healEpoch tL ∧
      t ≤ es.g.epoch (Party.senderOf t) ∧
      (∀ r ∈ es.g.trans, r.pos.epoch = t → r.ct.2.1 = r.pos.idx) ∧
      (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
      (∀ Q idx, idx / q = t - healEpoch tL → (es.g.st Q).vS = some (.inr idx) →
        Q = Party.senderOf t ∧ idx = s₀ ∧
        ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
          es.g.epoch (Party.senderOf t) = t ∧ st₀.1.lastSentIdx = es.g.idx (Party.senderOf t))) ∧
      (∀ idx st, idx / q = t - healEpoch tL → idx ≠ s₀ → σ idx = some st →
        st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
        st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
      (∀ Q v, (es.g.st Q).vR t = some v → v = .inr s₀) ∧
      (t ≤ es.g.epoch (Party.receiverOf t) → (es.g.st (Party.receiverOf t)).vR t = some (.inr s₀)) ∧
      (0 < t → ∃ Tc σc k, es.h.cache t = some (Tc, σc, k, some s₀) ∧
        (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).curCkaMsg = some Tc) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.ct.1.2 = some Tc)) ∧
      (st₀.1.ended = false ∧
        (∀ r_fs ∈ st₀.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st₀.1.lastSentIdx) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st₀.1.lastSentIdx) ∧
        (healedBy es.g.tL (2 + Δcka) t = true → st₀.1.senderCorruptedAt = none ∧
          (∀ r_fs ∈ st₀.1.inTransit,
            ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
        (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
          st₀.1.isCompromised r.pos.idx = false ∧
          (∀ r_fs ∈ st₀.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) ∧
      w.2 = Function.update σ s₀ (some st') ∧ st'.1.ended = false ∧
      st'.1.lastSentIdx = st₀.1.lastSentIdx ∧ st'.1.senderCorruptedAt = st₀.1.senderCorruptedAt ∧
      (∀ r_fs ∈ st'.1.inTransit, r_fs ∈ st₀.1.inTransit) ∧
      (healedBy es.g.tL (2 + Δcka) t = true →
        ∃ r_fs ∈ st₀.1.inTransit, r_fs.ad.1 = hdr ∧ r_fs.ct = e ∧
          st'.1.inTransit = st₀.1.inTransit.filter (·.idx != r_fs.idx)))
  show Post w
  dsimp only [hooksFSMultiDFBucketPaper] at hw
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
  generalize ((hs₁.book sIdx).getD {}).fsTrans.find? _ = matched at hw
  cases matched with
  | some m0 =>
    simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, Bool.not_true, Option.isSome_some] at hw
    rcases runPubIdeal_liftFSMultiDFBucket_deliver_support C ℓ encT idOf N sIdx hdr e hs₁ _ rc σ w hw with
      ⟨_, hw_none⟩ | ⟨p, _, u, hu, hwu⟩
    · simp only [StateT.run_pure, runPubIdeal, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hw_none
      subst hw_none; exact Or.inl rfl
    · have hdl_body : ∀ (st₀ st' : IdealHSt Pt ℓ),
          (σ sIdx = some st₀ ∨ (σ sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
          u.2 = some st' →
          (u.1, st') ∈ support (((deliverH (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hpIdeal N false) (DG (lChainPRG C.F))
            none ((hdr, p), e)).run st₀ : ProbComp _)) → Post w := by
        intro st₀ st' hst₀ hu2 hu_dl
        rw [hu2] at hwu
        rcases deliverH_hpIdeal_false_step_spec _ _ maxForwardJumps N ((hdr, p), e) st₀ st' u.1
            (hct_idx_at st₀ hst₀) hu_dl with ⟨hu1, _⟩ |
            ⟨r_fs, hr_fs, had, hct, hsc, hls, hend, ⟨hu1, hit⟩ | ⟨mo', hu1, hit_f⟩⟩
        · simp only [hu1, Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hwu
          subst hwu; exact Or.inl rfl
        · simp only [hu1, Option.map_some, withPub, StateT.run_pure, runPubIdeal, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hwu
          subst hwu
          exact Or.inr (Or.inl ⟨rfl, rfl, rfl, fun j hj => Function.update_of_ne hj (some st') σ,
            hrej_pres σ hcl st₀ st' hst₀ hsc hls hend hit⟩)
        · rcases hmust_s₀ σ hcl (fun _ _ => rfl) st₀ hst₀ (Or.inl ⟨r_fs, hr_fs⟩) with
            ⟨s₀, rfl, hdiv, hle, hct_idx, heqvS, hvS, hne, hvR, hvR_ge, hpin₀, h5₀⟩
          simp only [hu1, Option.map_some, withPub, StateT.run_bind, StateT.run_get, pure_bind,
            StateT.run_modify] at hwu
          have hsub : ∀ r' ∈ st'.1.inTransit, r' ∈ st₀.1.inTransit := by
            intro r' hr'; rw [hit_f, List.mem_filter] at hr'; exact hr'.1
          cases mo' with
          | none =>
            cases rec with
            | none =>
              simp only [Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hwu
              subst hwu; exact Or.inl rfl
            | some r_rec =>
              simp only [Option.map_none, StateT.run_pure, runPubIdeal, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hwu
              subst hwu
              exact Or.inr (Or.inr ⟨r_fs.idx, r_rec.msg, sIdx, st₀, st', rfl, rfl, rfl, rfl,
                hdiv, hle, hct_idx, heqvS, hvS, hne, hvR, hvR_ge, hpin₀, h5₀, rfl,
                hend.trans h5₀.1, hls, hsc, hsub,
                fun _ => ⟨r_fs, hr_fs, congrArg Prod.fst had, hct, hit_f⟩⟩)
          | some m_raw =>
            simp only [Option.map_some, StateT.run_pure, runPubIdeal, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hwu
            subst hwu
            exact Or.inr (Or.inr ⟨r_fs.idx, (p, m_raw), sIdx, st₀, st', rfl, rfl, rfl, rfl,
              hdiv, hle, hct_idx, heqvS, hvS, hne, hvR, hvR_ge, hpin₀, h5₀, rfl,
              hend.trans h5₀.1, hls, hsc, hsub,
              fun _ => ⟨r_fs, hr_fs, congrArg Prod.fst had, hct, hit_f⟩⟩)
      cases hσ0 : σ sIdx with
      | none =>
        rw [hσ0] at hu
        simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
        rcases hu with ⟨b, _, v0, hv0, rfl⟩
        exact hdl_body (hInit b .unknown) v0.2 (Or.inr ⟨hσ0, b, rfl⟩) rfl hv0
      | some st₀ =>
        rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
        rcases hu with ⟨v0, hv0, hvu⟩
        simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
        subst hvu; exact hdl_body st₀ v0.2 (Or.inl hσ0) rfl hv0
  | none =>
    have hij_tail : ∀ hs_cur (σ_cur : ℕ → Option (IdealHSt Pt ℓ)),
        hs_cur.cache = hs₁.cache →
        hs_cur.sessions = hs₁.sessions →
        EpochCleanAt q Δcka tL t es σ_cur →
        (∀ idx, idx ≠ sIdx → σ_cur idx = σ idx) →
        (∀ v_up, Function.update σ_cur sIdx v_up = Function.update σ sIdx v_up) →
        ∀ (k_ij : Option (ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) ×
            FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) →
          OracleComp (PubMultiSpec Pt ℓ)
            (Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
              ℕ × (LibsignalMsgPublicPart × Plain ℓ))) ×
              FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))),
        (∀ idx0 mo0 hs_k, ∃ hs_k',
          k_ij (some (.accepted idx0 mo0), hs_k) =
            pure (match mo0, rec with
              | some m, _ => some (some (.inr sIdx, idx0, m))
              | none, some r => some (some (.inr sIdx, idx0, r.msg))
              | none, none => none, hs_k') ∧
          hs_k'.cache = hs_k.cache ∧
          hs_k'.sessions = hs_k.sessions) →
        (∀ hs_k, k_ij (none, hs_k) = pure (none, hs_k)) →
        (∀ hs_k, k_ij (some .rejected, hs_k) = pure (some none, hs_k)) →
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          ((liftFSMultiDFBucket sIdx (CryptoGames.FSAEAD.injectQuery hdr e)).run hs_cur >>= k_ij) rc σ_cur) → Post w := by
      intro hs_cur σ_cur hc_cur hse_cur hcl_cur hσ_ne hσ_up k_ij hk_acc hk_none hk_rej hw_ij
      rcases runPubIdeal_liftFSMultiDFBucket_inject_support C ℓ encT idOf N sIdx hdr e hs_cur k_ij
          rc σ_cur w hw_ij with ⟨_, hw_none⟩ | ⟨p, _, u, hu, hwu⟩
      · cases hrc : rc sIdx with
        | false =>
          simp only [hrc, Bool.false_eq_true, ↓reduceIte, hk_rej, runPubIdeal, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_none
          subst hw_none
          exact Or.inr (Or.inl ⟨rfl, hc_cur, hse_cur, hσ_ne, hunchanged σ_cur hcl_cur⟩)
        | true =>
          simp only [hrc, ↓reduceIte, hk_none, runPubIdeal, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hw_none
          subst hw_none
          exact Or.inl rfl
      · have hij_body : ∀ (st₀ st' : IdealHSt Pt ℓ),
            (σ_cur sIdx = some st₀ ∨ (σ_cur sIdx = none ∧ ∃ b, st₀ = hInit b .unknown)) →
            u.2 = some st' →
            (u.1, st') ∈ support (((injectH (lAeadR C protoSignalCodec ℓ encT idOf)
              (lChainPRG C.F) maxForwardJumps (hpIdeal N false) (DG (lChainPRG C.F))
              none ((hdr, p), e)).run st₀ : ProbComp _)) → Post w := by
          intro st₀ st' hst₀ hu2 hu_ij
          rw [hu2] at hwu
          have hspec := injectH_hpIdeal_false_step_spec _ _ maxForwardJumps N ((hdr, p), e)
            st₀ st' u.1 hu_ij
          cases hu1 : u.1 with
          | none =>
            simp only [hu1, Option.map_none, hk_none, runPubIdeal, simulateQ_pure, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hwu
            subst hwu; exact Or.inl rfl
          | some rr =>
            cases rr with
            | rejected =>
              have hit := hspec.2.2.2.2.2 (by intro _ _ h; rw [hu1] at h; simp at h)
              simp only [hu1, Option.map_some, withPub, hk_rej, runPubIdeal,
                simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hwu
              subst hwu
              exact Or.inr (Or.inl ⟨rfl, hc_cur, hse_cur,
                fun j hj => by simp [Function.update_of_ne hj, hσ_ne j hj],
                hrej_pres σ_cur hcl_cur st₀ st' hst₀ hspec.1 hspec.2.1 hspec.2.2.1 hit⟩)
            | accepted idx0 mo0 =>
              have hcomp := (hspec.2.2.2.2.1 idx0 mo0 hu1).2
              rcases hmust_s₀ σ_cur hcl_cur hσ_ne st₀ hst₀ (Or.inr ⟨idx0, hcomp⟩) with
                ⟨s₀, rfl, hdiv, hle, hct_idx, heqvS, hvS, hne, hvR, hvR_ge, hpin₀, h5₀⟩
              have hnot_heal : healedBy es.g.tL (2 + Δcka) t = true → False := by
                intro hheal
                have hsc := (h5₀.2.2.2.1 hheal).1
                rw [isCompromised_of_senderCorruptedAt_none st₀.1 hsc idx0] at hcomp; cases hcomp
              simp only [hu1, Option.map_some, withPub] at hwu
              cases mo0 with
              | none =>
                rcases hk_acc idx0 none hs_cur with ⟨hs_k', hk_eq, hc_k', hse_k'⟩
                cases rec with
                | none =>
                  simp only [Option.map_none, hk_eq, runPubIdeal, simulateQ_pure, StateT.run_pure,
                    support_pure, Set.mem_singleton_iff] at hwu
                  subst hwu; exact Or.inl rfl
                | some r_rec =>
                  simp only [Option.map_none, hk_eq, runPubIdeal, simulateQ_pure, StateT.run_pure,
                    support_pure, Set.mem_singleton_iff] at hwu
                  subst hwu
                  exact Or.inr (Or.inr ⟨idx0, r_rec.msg, sIdx, st₀, st', rfl,
                    hc_k'.trans hc_cur, hse_k'.trans hse_cur,
                    rfl, hdiv, hle, hct_idx, heqvS, hvS, hne, hvR, hvR_ge, hpin₀, h5₀,
                    hσ_up _, hspec.2.2.1.trans h5₀.1, hspec.2.1, hspec.1, hspec.2.2.2.1,
                    fun hheal => (hnot_heal hheal).elim⟩)
              | some m_raw =>
                rcases hk_acc idx0 (some (p, m_raw)) hs_cur with ⟨hs_k', hk_eq, hc_k', hse_k'⟩
                simp only [Option.map_some, hk_eq, runPubIdeal, simulateQ_pure, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff] at hwu
                subst hwu
                exact Or.inr (Or.inr ⟨idx0, (p, m_raw), sIdx, st₀, st', rfl,
                  hc_k'.trans hc_cur, hse_k'.trans hse_cur,
                  rfl, hdiv, hle, hct_idx, heqvS, hvS, hne, hvR, hvR_ge, hpin₀, h5₀,
                  hσ_up _, hspec.2.2.1.trans h5₀.1, hspec.2.1, hspec.1, hspec.2.2.2.1,
                  fun hheal => (hnot_heal hheal).elim⟩)
        cases hσ0 : σ_cur sIdx with
        | none =>
          rw [hσ0] at hu
          simp only [lazyInit_run_none', fsInit, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
          rcases hu with ⟨b, _, v0, hv0, rfl⟩
          exact hij_body (hInit b .unknown) v0.2 (Or.inr ⟨hσ0, b, rfl⟩) rfl hv0
        | some st₀ =>
          rw [hσ0, lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hu
          rcases hu with ⟨v0, hv0, hvu⟩
          simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hvu
          subst hvu; exact hij_body st₀ v0.2 (Or.inl hσ0) rfl hv0
    by_cases hguard_cs : (!(healedBy es.g.tL (2 + Δcka) t) && !((hs₁.book sIdx).getD {}).sCorr) = true
    · have hnot_heal : healedBy es.g.tL (2 + Δcka) t = false := by
        rcases Bool.and_eq_true_iff.mp hguard_cs with ⟨h1, _⟩
        exact Bool.not_eq_true' _ |>.mp h1
      simp only [Option.isNone_none, Bool.true_and, hguard_cs, ↓reduceIte,
        StateT.run_bind] at hw
      rcases corruptSender_fsRecv_bucket_clean C ℓ encT idOf q N Δcka tL t sIdx
          es rc σ hcl hnot_heal hsafe_or_pin hs₁ _ w hw with ⟨ss_out, st₁, hcl₁, hw_cs⟩
      simp only [StateT.run_bind, StateT.run_modify, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hw_cs
      refine hij_tail _ _ ?_ ?_ hcl₁
        (fun idx hne => Function.update_of_ne hne (some st₁) σ)
        (fun _ => by simp)
        _ ?_ (fun _ => rfl) (fun _ => rfl) hw_cs
      · rfl
      · rfl
      · intro idx0 mo0 hs_k; cases mo0 <;> cases rec <;>
          simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, StateT.run_modify, StateT.run_pure] <;>
          exact ⟨_, rfl, rfl, rfl⟩
    · have hgf : (!(healedBy es.g.tL (2 + Δcka) t) && !((hs₁.book sIdx).getD {}).sCorr) = false :=
        Bool.not_eq_true _ |>.mp hguard_cs
      simp only [Option.isNone_none, Bool.true_and, hgf, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, Bool.not_true, Option.isSome_none] at hw
      refine hij_tail hs₁ σ rfl rfl hcl (fun _ _ => rfl) (fun _ => rfl)
        _ ?_ (fun _ => rfl) (fun _ => rfl) hw
      intro idx0 mo0 hs_k; cases mo0 <;> cases rec <;>
        simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte, StateT.run_modify, StateT.run_pure] <;>
        exact ⟨_, rfl, rfl, rfl⟩

end BucketHooks

end

end Computational.Proofs.E2E.SessionAuthMultiEndBucketHooks

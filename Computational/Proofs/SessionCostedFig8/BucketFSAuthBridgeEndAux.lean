/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthWireEnd -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthFS
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions

/-!
# Ideal-Cutoff Support Helpers for `BucketFSAuthBridgeEndMix`

Provides layout- and cycle-free `IdealHSt` / `runPubIdeal` support invariants at `hpIdeal N la`
for both `la = true` (`PubLaSafe`) and `la = false` (epoch-indexed sender-corruption and
compromised-index tracking) used by `BucketFSAuthBridgeEndMix`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndAux

public section

set_option autoImplicit false

open scoped ENNReal
open OracleSpec OracleComp
open _root_.CryptoGames (Party AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.FSAEAD.Thm5 (HState HSt DG hp decIdx encIdxWith genUpTo receiveH
  transmitHWith challengeHWith corruptSenderH corruptReceiverH deliverH injectH
  getH getH_run onH modifyH modifyH_run hInit)
open _root_.CryptoGames.FSAEAD.Thm5.Ends (mem_support_genUpTo mem_support_encIdx
  mem_support_decIdx mem_support_senderKey)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart
  LibsignalCiphertextWithSalt32 lIdeal lAeadR lChainPRG lPubOf)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit lazyInit_run_none'
  lazyInit_run_some' sessLift sessLift_inl sessLift_inr sessLiftCore multiSessSpec)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec fsInit fsImpl)
open _root_.CryptoVerification.E2E.Signed.SessionWire (hpIdeal sessQueryAt
  allSessions_hp_eq_hpIdeal_la)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoGames.SM.Construction (Header)

/-! ## 1. Single-Session `hpIdeal N la` Step Lemmas -/

theorem decIdx_hpIdeal_none {CK MK AD M C : Type}
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

theorem injectH_hpIdeal_not_accepted_of_uncomp {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip N : ℕ) (la : Bool) (q : AD × (ℕ × C))
    (s s' : HSt CK MK AD M C) (hc0 : s.1.isCompromised q.2.1 = false)
    {res : Option (_root_.CryptoGames.FSAEAD.ReceiveResult M)}
    (hmem : (res, s') ∈ support
      ((injectH ae G maxSkip (hpIdeal N la) (DG G)
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) q).run s)) :
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧ ∀ i mo', res ≠ some (.accepted i mo') := by
  rcases q with ⟨a, i, e⟩
  dsimp only at hc0
  unfold injectH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
    rcases hmem with ⟨rfl, hs'1, _⟩
    rw [hs'1]
    exact ⟨rfl, fun _ _ h => nomatch h⟩
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨r, s₁⟩, hr₁, hr₂⟩
    have hr_none : r = none ∧ s₁.1.senderCorruptedAt = s.1.senderCorruptedAt := by
      unfold receiveH at hr₁
      simp only [StateT.run_bind, getH_run, pure_bind] at hr₁
      split at hr₁
      · rw [StateT.run_bind, decIdx_hpIdeal_none ae N la i a e s hc0, pure_bind] at hr₁
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₁
        exact ⟨hr₁.1, by rw [hr₁.2.1]⟩
      · split at hr₁
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₁
          exact ⟨hr₁.1, by rw [hr₁.2.1]⟩
        · split at hr₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₁
            exact ⟨hr₁.1, by rw [hr₁.2.1]⟩
          · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hr₁
            rcases hr₁ with ⟨⟨_, s₂⟩, hg, hr₁⟩
            rcases mem_support_genUpTo G hg with ⟨ks, hks⟩
            have hc₂ : s₂.1.isCompromised i = false := by
              rw [hks]; exact hc0
            rw [StateT.run_bind, decIdx_hpIdeal_none ae N la i a e s₂ hc₂, pure_bind] at hr₁
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₁
            exact ⟨hr₁.1, by rw [hr₁.2.1, hks]⟩
    rcases hr_none with ⟨rfl, hcorr₁⟩
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₂
    rcases hr₂ with ⟨rfl, hs'1, _⟩
    rw [hs'1]
    exact ⟨hcorr₁, fun _ _ h => nomatch h⟩

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
  have h := injectH_hpIdeal_not_accepted_of_uncomp ae G maxSkip N la q s s'
    (isCompromised_of_senderCorruptedAt_none s.1 hcorr q.2.1) hmem
  exact ⟨h.1.trans hcorr, h.2⟩

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
    have hs₁ := (mem_support_decIdx ae hd).1
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
        have hs₂ := (mem_support_decIdx ae hd).1
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
      rw [hs₂, hks] at hs'1; rw [hs'1]; exact hcorr
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
      rw [hs₂, hks] at hs'1; rw [hs'1]; exact hcorr
  · change (r, s') ∈ support ((corruptSenderH G (hpIdeal N true) q_cs).run s) at hmem
    unfold corruptSenderH at hmem
    simp only [StateT.run_bind, getH_run, pure_bind] at hmem
    split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]; exact hcorr
    · simp only [_root_.CryptoVerification.E2E.Signed.SessionWire.hpIdeal_la, ↓reduceIte,
        StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1]; exact hcorr
  · change (r, s') ∈ support ((corruptReceiverH G (hpIdeal N true) q_cr).run s) at hmem
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
  have hEq : 𝒟[Prod.fst <$> m] = 𝒟[(Pure.pure false : ProbComp Bool)] := by
    rw [map_eq_bind_pure_comp, evalDist_bind_congr_of_support m _ (fun _ => Pure.pure false)]
    · exact OracleComp.evalDist_bind_const _ _
    · intro z hz; simp [h z hz]
  rw [hEq]; simp

theorem evalDist_bind_eq_zero_of_support {α : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (hf : ∀ o ∈ support oa, 𝒟[f o] = 𝒟[(Pure.pure false : ProbComp Bool)]) :
    𝒟[oa >>= f] {true} = 0 := by
  have hEq : 𝒟[oa >>= f] = 𝒟[(Pure.pure false : ProbComp Bool)] := by
    rw [evalDist_bind_congr_of_support oa f (fun _ => Pure.pure false) hf]
    exact OracleComp.evalDist_bind_const _ _
  rw [hEq]; simp

theorem evalDist_eq_pure_false_of_support_false {β : Type} {m : ProbComp (Bool × β)}
    (h : ∀ z ∈ support m, z.1 = false) :
    𝒟[Prod.fst <$> m] = 𝒟[(Pure.pure false : ProbComp Bool)] := by
  rw [map_eq_bind_pure_comp, evalDist_bind_congr_of_support m _ (fun _ => Pure.pure false)]
  · exact OracleComp.evalDist_bind_const _ _
  · intro z hz; simp [h z hz]

/-! ## 2. Public-Part Multi-Session Ideal Runner (`runPubIdeal`) and `PubLaSafe` -/

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
    PubLaSafe C ℓ encT idOf N P (Pure.pure a) := by
  intro rc σ hσ z hz
  simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz; exact ⟨ha, hσ⟩

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

private theorem lazyInit_hpIdeal_true_step {Pt : Type} [DecidableEq Pt]
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
      injection hst with hst_eq; subst hst_eq
      exact fsImpl_hpIdeal_true_step _ _ _ maxForwardJumps N q (hInit b .unknown) z.2 rfl hz
    | some st₀ =>
      rw [hσ0] at hw
      rw [lazyInit_run_some', map_eq_bind_pure_comp, MonadAttach.mem_support_bind] at hw
      rcases hw with ⟨z, hz, hzw⟩
      rw [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hzw
      subst hzw
      injection hst with hst_eq; subst hst_eq
      exact fsImpl_hpIdeal_true_step _ _ _ maxForwardJumps N q st₀ z.2 (hσ s st₀ hσ0) hz
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

private theorem run_idealSessImpl_pubMultiTag_inr {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (s₀ : ℕ)
    (q : (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    (simulateQ (idealSessImpl C ℓ encT idOf N la) (pubMultiTag s₀ (.inr q))).run σ =
    ((fun r => (r.1, Function.update σ s₀ r.2)) <$>
      (idealLazyImpl C ℓ encT idOf N la q).run (σ s₀)) := by
  change (simulateQ (idealSessImpl C ℓ encT idOf N la)
    (query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32))
      (.inr ⟨s₀, q⟩))).run σ = _
  rw [query_eq_liftM]
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    idealSessImpl, idealLazyImpl, sessLift_inr, sessLiftCore, StateT.run_mk]
  rfl

theorem runPubIdeal_query_inr_bind {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N : ℕ) (la : Bool) (sIdx : ℕ)
    (q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    {β : Type} (f : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Range q₀ → β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    runPubIdeal C ℓ encT idOf N la
      (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => Pure.pure (f a)) rc σ =
    (((simulateQ (idealSessImpl C ℓ encT idOf N la)
        (simulateQ (pubMultiTag sIdx)
          ((_root_.CryptoGames.FSAEAD.pubRedImpl
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (AD := Header Pt) (M := Plain ℓ)
            (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
            (.inr q₀)).run (rc sIdx)))).run σ) >>= fun v =>
      Pure.pure ((f v.1.1, Function.update rc sIdx v.1.2), v.2)) := by
  unfold runPubIdeal
  rw [query_eq_liftM, simulateQ_query_bind]
  dsimp only [pubMultiImpl, OracleQuery.input_query, OracleQuery.cont_query]
  simp [StateT.run_mk, map_eq_bind_pure_comp]

theorem pubTag_tr_eq {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (N : ℕ) (la : Bool) (s₀ : ℕ) (hdr : Header Pt)
    (pm : LibsignalMsgPublicPart × Plain ℓ) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la) (simulateQ (pubMultiTag s₀)
      ((_root_.CryptoGames.FSAEAD.pubRedImpl (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
        (.inr (.inl (.inl (.inl (.inl (.inl (hdr, pm)))))))).run b))).run σ) =
    (((idealLazyImpl C ℓ encT idOf N la
      (.inl (.inl (.inl (.inl (.inl ((hdr, pm.1), pm.2))))))).run (σ s₀)) >>= fun w =>
      Pure.pure ((w.1, b), Function.update σ s₀ w.2)) := by
  simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.transmitQuery,
    StateT.run_lift, map_eq_bind_pure_comp]
  erw [run_idealSessImpl_pubMultiTag_inr]; simp [map_eq_bind_pure_comp]

theorem pubTag_ch_eq {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (N : ℕ) (la : Bool) (s₀ : ℕ) (hdr : Header Pt)
    (pm₀ pm₁ : LibsignalMsgPublicPart × Plain ℓ) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la) (simulateQ (pubMultiTag s₀)
      ((_root_.CryptoGames.FSAEAD.pubRedImpl (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
        (.inr (.inl (.inl (.inl (.inl (.inr (hdr, pm₀, pm₁)))))))).run b))).run σ) =
    (((idealLazyImpl C ℓ encT idOf N la
      (.inl (.inl (.inl (.inl (.inr ((hdr, pm₀.1), pm₀.2, pm₁.2))))))).run (σ s₀)) >>= fun w =>
      Pure.pure ((w.1, b), Function.update σ s₀ w.2)) := by
  simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.challengeQuery,
    StateT.run_lift, map_eq_bind_pure_comp]
  erw [run_idealSessImpl_pubMultiTag_inr]; simp [map_eq_bind_pure_comp]

theorem pubTag_cs_eq {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (N : ℕ) (la : Bool) (s₀ : ℕ) (u : Unit) (b : Bool)
    (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la) (simulateQ (pubMultiTag s₀)
      ((_root_.CryptoGames.FSAEAD.pubRedImpl (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
        (.inr (.inl (.inl (.inl (.inr u)))))).run b))).run σ) =
    (((idealLazyImpl C ℓ encT idOf N la (.inl (.inl (.inl (.inr ()))))).run (σ s₀)) >>= fun w =>
      Pure.pure ((w.1, b), Function.update σ s₀ w.2)) := by
  simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.corruptSenderQuery,
    StateT.run_lift, map_eq_bind_pure_comp]
  erw [run_idealSessImpl_pubMultiTag_inr]; simp [map_eq_bind_pure_comp]

theorem pubTag_cr_eq {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (N : ℕ) (la : Bool) (s₀ : ℕ) (u : Unit) (b : Bool)
    (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la) (simulateQ (pubMultiTag s₀)
      ((_root_.CryptoGames.FSAEAD.pubRedImpl (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
        (.inr (.inl (.inl (.inr u))))).run b))).run σ) =
    (((idealLazyImpl C ℓ encT idOf N la (.inl (.inl (.inr ())))).run (σ s₀)) >>= fun w =>
      Pure.pure ((w.1, if w.1.isSome then true else b), Function.update σ s₀ w.2)) := by
  simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.corruptReceiverQuery,
    StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp]
  erw [run_idealSessImpl_pubMultiTag_inr]; simp [map_eq_bind_pure_comp]
  refine bind_congr fun ⟨w₁, w₂⟩ => ?_
  change Option _ at w₁; cases w₁ <;> simp [StateT.run_set]

theorem pubTag_dl_eq {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (N : ℕ) (la : Bool) (s₀ : ℕ) (hdr : Header Pt)
    (e : ℕ × LibsignalCiphertextWithSalt32) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la) (simulateQ (pubMultiTag s₀)
      ((_root_.CryptoGames.FSAEAD.pubRedImpl (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
        (.inr (.inl (.inr (hdr, e))))).run b))).run σ) =
    match lPubOf protoSignalCodec e.2 with
    | none => Pure.pure ((none, b), σ)
    | some p =>
      (((idealLazyImpl C ℓ encT idOf N la (.inl (.inr ((hdr, p), e)))).run (σ s₀)) >>= fun w =>
        Pure.pure ((w.1.map (_root_.CryptoGames.FSAEAD.withPub p), b), Function.update σ s₀ w.2)) := by
  cases hpub : lPubOf protoSignalCodec e.2
  · simp [_root_.CryptoGames.FSAEAD.pubRedImpl, hpub]
  · simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.deliverQuery, hpub,
      StateT.run_lift, map_eq_bind_pure_comp]
    erw [run_idealSessImpl_pubMultiTag_inr]; simp [map_eq_bind_pure_comp]

theorem pubTag_ij_eq {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (N : ℕ) (la : Bool) (s₀ : ℕ) (hdr : Header Pt)
    (e : ℕ × LibsignalCiphertextWithSalt32) (b : Bool) (σ : ℕ → Option (IdealHSt Pt ℓ)) :
    ((simulateQ (idealSessImpl C ℓ encT idOf N la) (simulateQ (pubMultiTag s₀)
      ((_root_.CryptoGames.FSAEAD.pubRedImpl (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
        (.inr (.inr (hdr, e)))).run b))).run σ) =
    match lPubOf protoSignalCodec e.2 with
    | none => Pure.pure (((if b then none else some .rejected), b), σ)
    | some p =>
      (((idealLazyImpl C ℓ encT idOf N la (.inr ((hdr, p), e))).run (σ s₀)) >>= fun w =>
        Pure.pure ((w.1.map (_root_.CryptoGames.FSAEAD.withPub p), b), Function.update σ s₀ w.2)) := by
  cases hpub : lPubOf protoSignalCodec e.2
  · simp [_root_.CryptoGames.FSAEAD.pubRedImpl, hpub, StateT.run_map, StateT.run_get]
  · simp [_root_.CryptoGames.FSAEAD.pubRedImpl, _root_.CryptoGames.FSAEAD.injectQuery, hpub,
      StateT.run_lift, map_eq_bind_pure_comp]
    erw [run_idealSessImpl_pubMultiTag_inr]; simp [map_eq_bind_pure_comp]

private theorem pubStep_la_preserves {Pt : Type} [DecidableEq Pt]
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
  · rw [pubTag_tr_eq] at hv; rw [MonadAttach.mem_support_bind] at hv
    rcases hv with ⟨w, hw, hvw⟩; rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
    exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_ch_eq] at hv; rw [MonadAttach.mem_support_bind] at hv
    rcases hv with ⟨w, hw, hvw⟩; rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
    exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_cs_eq] at hv; rw [MonadAttach.mem_support_bind] at hv
    rcases hv with ⟨w, hw, hvw⟩; rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
    exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_cr_eq] at hv; rw [MonadAttach.mem_support_bind] at hv
    rcases hv with ⟨w, hw, hvw⟩; rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
    exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_dl_eq] at hv
    cases hpub : lPubOf protoSignalCodec e.2 with
    | none => rw [hpub, support_pure, Set.mem_singleton_iff] at hv; subst hv; exact hσ
    | some _ =>
      rw [hpub, MonadAttach.mem_support_bind] at hv
      rcases hv with ⟨w, hw, hvw⟩; rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
      exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw
  · rw [pubTag_ij_eq] at hv
    cases hpub : lPubOf protoSignalCodec e.2 with
    | none => rw [hpub, support_pure, Set.mem_singleton_iff] at hv; subst hv; exact hσ
    | some _ =>
      rw [hpub, MonadAttach.mem_support_bind] at hv
      rcases hv with ⟨w, hw, hvw⟩; rw [support_pure, Set.mem_singleton_iff] at hvw; subst hvw
      exact lazyInit_hpIdeal_true_step C ℓ encT idOf N s₀ _ σ hσ hw

theorem PubLaSafe.any {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    {α : Type} (x : OracleComp (PubMultiSpec Pt ℓ) α) :
    PubLaSafe C ℓ encT idOf N (fun _ => True) x := by
  induction x using OracleComp.inductionOn with
  | pure _ => exact PubLaSafe.pure trivial
  | query_bind t _ ih =>
    intro rc σ hσ z hz
    rcases t with n | ⟨s₀, q⟩
    · simp only [runPubIdeal, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, pubMultiImpl, StateT.run_bind, stateT_lift_run,
        query_eq_liftM, idealSessImpl, sessLift_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
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
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    {β : Type} (f : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) → β) :
    PubLaSafe C ℓ encT idOf N
      (fun b => ∃ r, b = f r ∧ ∀ i mo', r ≠ some (.accepted i mo'))
      (query (spec := PubMultiSpec Pt ℓ) (Sum.inr ⟨sIdx, .inr (hdr, e)⟩) >>=
        fun a => Pure.pure (f a)) := by
  intro rc σ hσ z hz
  erw [runPubIdeal_query_inr_bind, pubTag_ij_eq] at hz
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    erw [hpub, pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨⟨if rc sIdx then none else some .rejected, rfl, fun i mo' hacc => ?_⟩, hσ⟩
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
    refine ⟨⟨w.1.map (_root_.CryptoGames.FSAEAD.withPub p), rfl, fun i mo' hacc => ?_⟩, hσ'⟩
    cases hw1 : w.1 with
    | none => simp [hw1] at hacc
    | some rr =>
      cases rr with
      | rejected => simp [hw1, _root_.CryptoGames.FSAEAD.withPub] at hacc
      | accepted idx mo0 => exact hnotacc idx mo0 hw1

/-! ## 3. `la = false` Ideal-Cutoff Hoare Combinators (`slotSent`, `slotCorr`, `PubFalseHoare`) -/

theorem isCompromised_false_of_le {CK MK AD M C : Type}
    (st : HState CK MK AD M C) (i : ℕ)
    (h : ∀ c, st.senderCorruptedAt = some c → i ≤ c) :
    st.isCompromised i = false := by
  cases hc : st.senderCorruptedAt with
  | none => simp [HState.isCompromised, hc]
  | some c =>
    have hic := h c hc
    simp only [HState.isCompromised, hc, decide_eq_false_iff_not]
    omega

theorem receiveH_preserves_lastSentIdx {CK MK AD M C : Type}
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
    s'.1.lastSentIdx = s.1.lastSentIdx := by
  rcases c with ⟨i, e⟩
  unfold receiveH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨m?, s₁⟩, hd, hm⟩
    have hs₁ := (mem_support_decIdx ae hd).1
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
        have hs₂ := (mem_support_decIdx ae hd).1
        rw [hs₂] at hm
        cases m? with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hm
          rw [hm.2.1, hks]
        | some msg =>
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at hm
          rw [hm.2.1, hks]

theorem receiveH_accepted_idx_eq {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip : ℕ) (P : _root_.CryptoGames.FSAEAD.Thm5.Params)
    (hint : Option M) (a : AD) (c : ℕ × C)
    (s s' : HSt CK MK AD M C) {i' : ℕ} {m' : M}
    (hmem : (some (i', m'), s') ∈ support
      ((receiveH ae G maxSkip P (DG G)
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) hint a c).run s)) :
    i' = c.1 := by
  rcases c with ⟨i, e⟩
  dsimp only
  unfold receiveH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split at hmem
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨m?, _⟩, _, hm⟩
    cases m? with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hm
      exact nomatch hm.1
    | some msg =>
      simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff] at hm
      cases hm.1; rfl
  · split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      exact nomatch hmem.1
    · split at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        exact nomatch hmem.1
      · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨⟨_, _⟩, _, hmem⟩
        rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨⟨m?, _⟩, _, hm⟩
        cases m? with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hm
          exact nomatch hm.1
        | some msg =>
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at hm
          cases hm.1; rfl

@[expose] def slotSent {Pt : Type} {ℓ : ℕ} (σ : ℕ → Option (IdealHSt Pt ℓ)) (s : ℕ) : ℕ :=
  match σ s with
  | none => 0
  | some st => st.1.lastSentIdx

@[expose] def slotCorr {Pt : Type} {ℓ : ℕ} (σ : ℕ → Option (IdealHSt Pt ℓ)) (s : ℕ) : Option ℕ :=
  match σ s with
  | none => none
  | some st => st.1.senderCorruptedAt

theorem slotSent_update_some {Pt : Type} {ℓ : ℕ}
    (σ : ℕ → Option (IdealHSt Pt ℓ)) (s₀ : ℕ) (st : IdealHSt Pt ℓ) :
    slotSent (Function.update σ s₀ (some st)) = Function.update (slotSent σ) s₀ st.1.lastSentIdx := by
  funext s
  by_cases hs : s = s₀
  · subst hs; simp [slotSent]
  · simp [slotSent, Function.update_of_ne hs]

theorem slotCorr_update_some {Pt : Type} {ℓ : ℕ}
    (σ : ℕ → Option (IdealHSt Pt ℓ)) (s₀ : ℕ) (st : IdealHSt Pt ℓ) :
    slotCorr (Function.update σ s₀ (some st)) = Function.update (slotCorr σ) s₀ st.1.senderCorruptedAt := by
  funext s
  by_cases hs : s = s₀
  · subst hs; simp [slotCorr]
  · simp [slotCorr, Function.update_of_ne hs]

@[expose] def PubFalseHoare {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    {α : Type}
    (Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop)
    (Post : α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop)
    (x : OracleComp (PubMultiSpec Pt ℓ) α) : Prop :=
  ∀ rc σ, Pre (slotSent σ) (slotCorr σ) →
    ∀ z ∈ support (runPubIdeal C ℓ encT idOf N false x rc σ),
      Post z.1.1 (slotSent z.2) (slotCorr z.2)

theorem PubFalseHoare.pure {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {α : Type} {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Post : α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} {a : α}
    (ha : ∀ ns sc, Pre ns sc → Post a ns sc) :
    PubFalseHoare C ℓ encT idOf N Pre Post (Pure.pure a) := by
  intro rc σ hpre z hz
  simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz; exact ha _ _ hpre

theorem PubFalseHoare.conseq {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {α : Type} {Pre₁ Pre₂ : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Post₁ Post₂ : α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {x : OracleComp (PubMultiSpec Pt ℓ) α}
    (hx : PubFalseHoare C ℓ encT idOf N Pre₁ Post₁ x)
    (hPre : ∀ ns sc, Pre₂ ns sc → Pre₁ ns sc)
    (hPost : ∀ a ns sc, Post₁ a ns sc → Post₂ a ns sc) :
    PubFalseHoare C ℓ encT idOf N Pre₂ Post₂ x :=
  fun rc σ hpre z hz => hPost _ _ _ (hx rc σ (hPre _ _ hpre) z hz)

theorem PubFalseHoare.bind {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {α β : Type} {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Mid : α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Post : β → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {x : OracleComp (PubMultiSpec Pt ℓ) α}
    {f : α → OracleComp (PubMultiSpec Pt ℓ) β}
    (hx : PubFalseHoare C ℓ encT idOf N Pre Mid x)
    (hf : ∀ a, PubFalseHoare C ℓ encT idOf N (Mid a) Post (f a)) :
    PubFalseHoare C ℓ encT idOf N Pre Post (x >>= f) := by
  intro rc σ hpre z hz
  simp only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hzw⟩
  exact hf w.1.1 w.1.2 w.2 (hx rc σ hpre w hw) z hzw

theorem PubFalseHoare.query_inl {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N n : ℕ)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    PubFalseHoare C ℓ encT idOf N Pre (fun _ ns sc => Pre ns sc)
      (liftM (OracleSpec.query (spec := PubMultiSpec Pt ℓ) (Sum.inl n))) := by
  intro rc σ hpre z hz
  rw [← bind_pure (liftM (OracleSpec.query (spec := PubMultiSpec Pt ℓ) (Sum.inl n)))] at hz
  simp only [runPubIdeal, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, pubMultiImpl, StateT.run_bind, stateT_lift_run,
    query_eq_liftM, idealSessImpl, sessLift_inl,
    QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
    monadLift_self, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
  rcases hz with ⟨_, _, rfl⟩
  exact hpre

private theorem lazyInit_run_support_unpack {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (la : Bool) (s₀ : ℕ)
    (q : (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (σ : ℕ → Option (IdealHSt Pt ℓ))
    {w : (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32).Range q × Option (IdealHSt Pt ℓ)}
    (hw : w ∈ support ((idealLazyImpl C ℓ encT idOf N la q).run (σ s₀))) :
    ∃ st₀ st',
      st₀.1.lastSentIdx = slotSent σ s₀ ∧
      st₀.1.senderCorruptedAt = slotCorr σ s₀ ∧
      w.2 = some st' ∧
      (w.1, st') ∈ support
        ((fsImpl (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
          (lChainPRG C.F) maxForwardJumps (hpIdeal N la) q).run st₀) := by
  cases hσ0 : σ s₀ with
  | none =>
    rw [hσ0] at hw
    simp only [idealLazyImpl, lazyInit_run_none', fsInit, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hw
    rcases hw with ⟨b, _, z, hz, rfl⟩
    exact ⟨hInit b .unknown, z.2, by simp [slotSent, hσ0, hInit],
      by simp [slotCorr, hσ0, hInit], rfl, hz⟩
  | some st₀ =>
    rw [hσ0] at hw
    rw [idealLazyImpl, lazyInit_run_some', map_eq_bind_pure_comp,
      MonadAttach.mem_support_bind] at hw
    rcases hw with ⟨z, hz, hzw⟩
    rw [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hzw
    subst hzw
    exact ⟨st₀, z.2, by simp [slotSent, hσ0], by simp [slotCorr, hσ0], rfl, hz⟩

theorem pubQuery_tr_false {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N sIdx : ℕ)
    (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    {β : Type} (f : Option (ℕ × LibsignalCiphertextWithSalt32) → β)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    PubFalseHoare C ℓ encT idOf N Pre
      (fun out ns' sc' => ∃ ns sc, Pre ns sc ∧ sc' = sc ∧
        ((out = f none ∧ ns' = ns) ∨
         (∃ ct, out = f (some (ns sIdx + 1, ct)) ∧ ns' = Function.update ns sIdx (ns sIdx + 1))))
      (query (spec := PubMultiSpec Pt ℓ)
        (Sum.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl (hdr, pm)))))⟩) >>= fun a => Pure.pure (f a)) := by
  intro rc σ hpre z hz
  erw [runPubIdeal_query_inr_bind, pubTag_tr_eq] at hz
  erw [bind_assoc, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hzw⟩
  erw [pure_bind, support_pure, Set.mem_singleton_iff] at hzw
  subst hzw
  rcases lazyInit_run_support_unpack C ℓ encT idOf N false sIdx _ σ hw with
    ⟨st₀, st', hns₀, hsc₀, hw2, hmem⟩
  rw [hw2, slotSent_update_some, slotCorr_update_some]
  change (w.1, st') ∈ support
    ((transmitHWith (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) (hpIdeal N false) (DG (lChainPRG C.F)) none ((hdr, pm.1), pm.2)).run st₀) at hmem
  unfold transmitHWith at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  refine ⟨slotSent σ, slotCorr σ, hpre, ?_, ?_⟩
  · split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1, hsc₀]; exact Function.update_eq_self sIdx (slotCorr σ)
    · simp only [StateT.run_bind, MonadAttach.mem_support_bind, modifyH_run, pure_bind,
        StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rcases hmem with ⟨⟨_, s₁⟩, h₁, ⟨_, s₂⟩, h₂, _, hst', _⟩
      rcases mem_support_genUpTo (lChainPRG C.F) h₁ with ⟨ks, hks⟩
      have hs₂ := mem_support_encIdx (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) h₂
      rw [hst', hs₂, hks]; dsimp only; rw [hsc₀]
      exact Function.update_eq_self sIdx (slotCorr σ)
  · split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      left
      refine ⟨by rw [hmem.1], ?_⟩
      rw [hmem.2.1, hns₀]; exact Function.update_eq_self sIdx (slotSent σ)
    · simp only [StateT.run_bind, MonadAttach.mem_support_bind, modifyH_run, pure_bind,
        StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rcases hmem with ⟨⟨_, s₁⟩, h₁, ⟨ct, s₂⟩, h₂, hw1, hst', _⟩
      rcases mem_support_genUpTo (lChainPRG C.F) h₁ with ⟨ks, hks⟩
      have hs₂ := mem_support_encIdx (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) h₂
      right
      refine ⟨ct, ?_, ?_⟩
      · dsimp only; rw [hw1, hns₀]
      · rw [hst', hs₂, hks]; dsimp only; rw [hns₀]

theorem pubQuery_cs_false {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N sIdx : ℕ)
    (u : Unit) {β : Type} (f : Option (RatchetSenderState (BitVec 256)) → β)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    PubFalseHoare C ℓ encT idOf N Pre
      (fun out ns' sc' => ∃ ns sc, Pre ns sc ∧ ns' = ns ∧
        ((out = f none ∧ sc' = sc) ∨
         (∃ w, out = f (some w) ∧
           sc' = Function.update sc sIdx (some ((sc sIdx).getD (ns sIdx))))))
      (query (spec := PubMultiSpec Pt ℓ)
        (Sum.inr ⟨sIdx, .inl (.inl (.inl (.inr u)))⟩) >>= fun a => Pure.pure (f a)) := by
  intro rc σ hpre z hz
  erw [runPubIdeal_query_inr_bind, pubTag_cs_eq] at hz
  erw [bind_assoc, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hzw⟩
  erw [pure_bind, support_pure, Set.mem_singleton_iff] at hzw
  subst hzw
  rcases lazyInit_run_support_unpack C ℓ encT idOf N false sIdx _ σ hw with
    ⟨st₀, st', hns₀, hsc₀, hw2, hmem⟩
  rw [hw2, slotSent_update_some, slotCorr_update_some]
  change (w.1, st') ∈ support
    ((corruptSenderH (lChainPRG C.F) (hpIdeal N false) ()).run st₀) at hmem
  unfold corruptSenderH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  refine ⟨slotSent σ, slotCorr σ, hpre, ?_, ?_⟩
  · split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      rw [hmem.2.1, hns₀]; exact Function.update_eq_self sIdx (slotSent σ)
    · simp only [_root_.CryptoVerification.E2E.Signed.SessionWire.hpIdeal_la,
        Bool.false_eq_true, ↓reduceIte, StateT.run_bind, MonadAttach.mem_support_bind,
        modifyH_run, pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.ext_iff] at hmem
      rcases hmem with ⟨⟨_, s₁⟩, h₁, _, hst', _⟩
      have hs₁ := mem_support_senderKey (lChainPRG C.F) h₁
      rw [hst', hs₁]; dsimp only; rw [hns₀]
      exact Function.update_eq_self sIdx (slotSent σ)
  · split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
      left
      refine ⟨by rw [hmem.1], ?_⟩
      rw [hmem.2.1, hsc₀]; exact Function.update_eq_self sIdx (slotCorr σ)
    · simp only [_root_.CryptoVerification.E2E.Signed.SessionWire.hpIdeal_la,
        Bool.false_eq_true, ↓reduceIte, StateT.run_bind, MonadAttach.mem_support_bind,
        modifyH_run, pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.ext_iff] at hmem
      rcases hmem with ⟨⟨ssOut, s₁⟩, h₁, hw1, hst', _⟩
      have hs₁ := mem_support_senderKey (lChainPRG C.F) h₁
      right
      refine ⟨{ chainKey := ssOut, lastIndex := st₀.1.lastSentIdx }, ?_, ?_⟩
      · dsimp only; rw [hw1]
      · rw [hst', hs₁]; dsimp only; rw [hsc₀, hns₀]

theorem pubQuery_dl_false {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N sIdx : ℕ)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    {β : Type} (f : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) → β)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    PubFalseHoare C ℓ encT idOf N Pre
      (fun out ns' sc' => ∃ r, out = f r ∧ Pre ns' sc' ∧
        (∀ i mo', r = some (.accepted i mo') → i = e.1))
      (query (spec := PubMultiSpec Pt ℓ)
        (Sum.inr ⟨sIdx, .inl (.inr (hdr, e))⟩) >>= fun a => Pure.pure (f a)) := by
  intro rc σ hpre z hz
  erw [runPubIdeal_query_inr_bind, pubTag_dl_eq] at hz
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    erw [hpub, pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨none, rfl, hpre, fun _ _ h => nomatch h⟩
  | some p =>
    erw [hpub, bind_assoc, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨w, hw, hzw⟩
    erw [pure_bind, support_pure, Set.mem_singleton_iff] at hzw
    subst hzw
    rcases lazyInit_run_support_unpack C ℓ encT idOf N false sIdx _ σ hw with
      ⟨st₀, st', hns₀, hsc₀, hw2, hmem⟩
    rw [hw2, slotSent_update_some, slotCorr_update_some]
    change (w.1, st') ∈ support
      ((deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hpIdeal N false) (DG (lChainPRG C.F)) none ((hdr, p), e)).run st₀) at hmem
    unfold deliverH at hmem
    simp only [StateT.run_bind, getH_run, pure_bind] at hmem
    have hpres : st'.1.lastSentIdx = slotSent σ sIdx ∧
        st'.1.senderCorruptedAt = slotCorr σ sIdx ∧
        (∀ idx mo0, w.1 = some (.accepted idx mo0) → idx = e.1) := by
      split at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2.1]; exact ⟨hns₀, hsc₀, by rw [hmem.1]; intro _ _ h; exact nomatch h⟩
      · split at hmem
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
          rw [hmem.2.1]; exact ⟨hns₀, hsc₀, by rw [hmem.1]; intro _ _ h; exact nomatch h⟩
        · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
          rcases hmem with ⟨⟨ro, s₁⟩, hr₁, hr₂⟩
          have hcorr₁ := receiveH_preserves_senderCorruptedAt
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hpIdeal N false) (some _) (hdr, p) e st₀ s₁ hr₁
          have hns₁ := receiveH_preserves_lastSentIdx
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hpIdeal N false) (some _) (hdr, p) e st₀ s₁ hr₁
          rcases ro with _ | ⟨i', m'⟩
          · simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
              Set.mem_singleton_iff, Prod.ext_iff] at hr₂
            rw [hr₂.2.1]
            exact ⟨hns₁.trans hns₀, hcorr₁.trans hsc₀,
              by rw [hr₂.1]; intro _ _ h; exact nomatch h⟩
          · have hi' := receiveH_accepted_idx_eq
              (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
              (hpIdeal N false) (some _) (hdr, p) e st₀ s₁ hr₁
            simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
              Set.mem_singleton_iff, Prod.ext_iff, HState.removeFromTransit] at hr₂
            rw [hr₂.2.1]
            refine ⟨hns₁.trans hns₀, hcorr₁.trans hsc₀, fun idx mo0 hw1 => ?_⟩
            rw [hr₂.1] at hw1
            cases hw1
            exact hi'
    rw [hpres.1, hpres.2.1, Function.update_eq_self sIdx (slotSent σ),
      Function.update_eq_self sIdx (slotCorr σ)]
    refine ⟨w.1.map (_root_.CryptoGames.FSAEAD.withPub p), rfl, hpre, fun i mo' hacc => ?_⟩
    cases hw1 : w.1 with
    | none => simp [hw1] at hacc
    | some rr =>
      cases rr with
      | rejected => simp [hw1, _root_.CryptoGames.FSAEAD.withPub] at hacc
      | accepted idx mo0 =>
        simp [hw1, _root_.CryptoGames.FSAEAD.withPub] at hacc
        exact hacc.1 ▸ hpres.2.2 idx mo0 hw1

theorem pubQuery_ij_false {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N sIdx : ℕ)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    {β : Type} (f : Option (_root_.CryptoGames.FSAEAD.ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) → β)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    PubFalseHoare C ℓ encT idOf N Pre
      (fun out ns' sc' => ∃ r, out = f r ∧ Pre ns' sc' ∧
        (∀ i mo', r = some (.accepted i mo') → i = e.1) ∧
        ((∀ c, sc' sIdx = some c → e.1 ≤ c) → ∀ i mo', r ≠ some (.accepted i mo')))
      (query (spec := PubMultiSpec Pt ℓ)
        (Sum.inr ⟨sIdx, .inr (hdr, e)⟩) >>= fun a => Pure.pure (f a)) := by
  intro rc σ hpre z hz
  erw [runPubIdeal_query_inr_bind, pubTag_ij_eq] at hz
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    erw [hpub, pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨if rc sIdx then none else some .rejected, rfl, hpre,
      fun i mo' hacc => by cases rc sIdx <;> simp at hacc,
      fun _ i mo' hacc => by cases rc sIdx <;> simp at hacc⟩
  | some p =>
    erw [hpub, bind_assoc, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨w, hw, hzw⟩
    erw [pure_bind, support_pure, Set.mem_singleton_iff] at hzw
    subst hzw
    rcases lazyInit_run_support_unpack C ℓ encT idOf N false sIdx _ σ hw with
      ⟨st₀, st', hns₀, hsc₀, hw2, hmem⟩
    rw [hw2, slotSent_update_some, slotCorr_update_some]
    change (w.1, st') ∈ support
      ((injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hpIdeal N false) (DG (lChainPRG C.F)) none ((hdr, p), e)).run st₀) at hmem
    have hpres : st'.1.lastSentIdx = slotSent σ sIdx ∧
        st'.1.senderCorruptedAt = slotCorr σ sIdx ∧
        (∀ idx mo0, w.1 = some (.accepted idx mo0) → idx = e.1) := by
      unfold injectH at hmem
      simp only [StateT.run_bind, getH_run, pure_bind] at hmem
      split at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hmem
        rw [hmem.2.1]; exact ⟨hns₀, hsc₀, by rw [hmem.1]; intro _ _ h; exact nomatch h⟩
      · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨⟨ro, s₁⟩, hr₁, hr₂⟩
        have hcorr₁ := receiveH_preserves_senderCorruptedAt
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false) none (hdr, p) e st₀ s₁ hr₁
        have hns₁ := receiveH_preserves_lastSentIdx
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false) none (hdr, p) e st₀ s₁ hr₁
        rcases ro with _ | ⟨i', m'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hr₂
          rw [hr₂.2.1]
          exact ⟨hns₁.trans hns₀, hcorr₁.trans hsc₀,
            by rw [hr₂.1]; intro _ _ h; exact nomatch h⟩
        · have hi' := receiveH_accepted_idx_eq
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hpIdeal N false) none (hdr, p) e st₀ s₁ hr₁
          simp only [StateT.run_pure, StateT.run_bind, modifyH_run, pure_bind, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at hr₂
          rw [hr₂.2.1]
          refine ⟨hns₁.trans hns₀, hcorr₁.trans hsc₀, fun idx mo0 hw1 => ?_⟩
          rw [hr₂.1] at hw1
          cases hw1
          exact hi'
    rw [hpres.1, hpres.2.1, Function.update_eq_self sIdx (slotSent σ),
      Function.update_eq_self sIdx (slotCorr σ)]
    refine ⟨w.1.map (_root_.CryptoGames.FSAEAD.withPub p), rfl, hpre,
      fun i mo' hacc => ?_, fun hle i mo' hacc => ?_⟩
    · cases hw1 : w.1 with
      | none => simp [hw1] at hacc
      | some rr =>
        cases rr with
        | rejected => simp [hw1, _root_.CryptoGames.FSAEAD.withPub] at hacc
        | accepted idx mo0 =>
          simp [hw1, _root_.CryptoGames.FSAEAD.withPub] at hacc
          exact hacc.1 ▸ hpres.2.2 idx mo0 hw1
    · have hc0 : st₀.1.isCompromised e.1 = false := by
        apply isCompromised_false_of_le
        intro c hc; exact hle c (hsc₀.symm.trans hc)
      have hnotacc := (injectH_hpIdeal_not_accepted_of_uncomp
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps N false
        ((hdr, p), e) st₀ st' hc0 hmem).2
      cases hw1 : w.1 with
      | none => simp [hw1] at hacc
      | some rr =>
        cases rr with
        | rejected => simp [hw1, _root_.CryptoGames.FSAEAD.withPub] at hacc
        | accepted idx mo0 => exact hnotacc idx mo0 hw1

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndAux

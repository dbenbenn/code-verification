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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD
import Computational.Proofs.CryptoGames.SM.Theorem1.Queries
import Computational.Proofs.E2E.RefuseCorrB0Core
import Computational.Proofs.E2E.Relabel.GameEq
import Computational.Proofs.E2E.SpkHop1A
import Computational.Proofs.E2E.SpkHop2A
import Computational.Proofs.HeadlineV1.CouplingV1
import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.Fig8Atomic
import Computational.Proofs.ReductionDsl.Fig8ExcessCosts
import Computational.Proofs.ReductionDsl.Fig8SourceCosts
import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.PubRed
import Computational.Proofs.ReductionDsl.PureAuxMacroLift
import Computational.Proofs.ReductionDsl.SM.Theorem1
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow
import Computational.Proofs.SessionCostedFig8.Bundles
import Computational.Proofs.SessionCostedFig8.BundlesAuxSize
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds

/-!
# Ideal-Cutoff Step Specs, Slot Arithmetic, and Invariants for `DeliverForgePaperMultiBucket`

Provides:
1. `hpIdeal N false` single-session step specs and `liftFSMultiDFBucket` support bridges.
2. Bucket session-block arithmetic (`sessBlock_div`, `regSessMultiDFBucket_spec`) and coin-only
   `startSend` / `startRecv` specifications.
3. Per-epoch 4-state invariant `EpochInv`, global state invariant `GlobalBucketWF`, top-level
   `BucketInv`, `authOutBucket_eq_false_of_bucketInv`, and `initFSMultiDFBucketPaper_bucketInv`.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEndBucketSteps

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party AEADScheme)
open _root_.CryptoGames.FSAEAD (ReceiveResult RatchetSenderState RatchetReceiverState withPub)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.SM (GameState Record healedBy ltOpt lastLeakGuessAdmissible
  authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (
  Header FSMultiDFBucketState FSMultiBook
  liftFSMultiDFBucket lookupMultiDFBucketF
  regSessMultiDFBucket regSessOptMultiDFBucket
  rootFSMultiDFBucketPaper hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode
  initFSMultiDFBucketPaper inStage2BucketGen postLeakDFBucket healEpoch)
open _root_.CryptoGames.SM.Construction.DeliverForge (authOutBucket)
open _root_.CryptoGames.SM.Engine (Ctx VP EState authOut)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (
  LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lFS lIdeal lAeadR lChainPRG lPubOf)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit)
open _root_.CryptoVerification.E2E.Signed.SessionWire (hpIdeal)
open _root_.CryptoGames.FSAEAD.Thm5 (
  HState HSt DG decIdx encIdxWith genUpTo receiveH
  transmitHWith corruptSenderH deliverH injectH
  getH getH_run modifyH_run hInit)
open _root_.CryptoGames.FSAEAD.Thm5.Ends (
  mem_support_genUpTo mem_support_decIdx mem_support_encIdx mem_support_senderKey)
open Computational.Proofs.E2E.SessionAuthMultiEnd (IdealHSt PubMultiSpec runPubIdeal
  decIdx_hpIdeal_none runPubIdeal_query_inr_eq
  pubTag_tr_eq pubTag_cs_eq pubTag_dl_eq pubTag_ij_eq
  liftFSMultiDFBucket_run_query_eq)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketLa (CoinOnly)

section BucketSteps

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## 1. `hpIdeal N false` Step Lemmas & `liftFSMultiDFBucket` Support Bridges -/

theorem genUpTo_preserves_meta {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    (G : ℕ → _root_.PRGScheme CK (CK × MK)) (P : CryptoGames.FSAEAD.Thm5.Params) (i : ℕ)
    (s s' : HSt CK MK AD M C) (u : Unit)
    (hmem : (u, s') ∈ support (StateT.run (m := ProbComp) (CryptoGames.FSAEAD.Thm5.genUpTo G P (DG G) i) s)) :
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    s'.1.ended = s.1.ended ∧
    s'.1.inTransit = s.1.inTransit := by
  rcases mem_support_genUpTo G hmem with ⟨ks, hks⟩
  rw [hks]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem injectH_hpIdeal_false_step_spec {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → _root_.PRGScheme CK (CK × MK)) (maxSkip N : ℕ)
    (q : AD × (ℕ × C)) (s s' : HSt CK MK AD M C) (res : Option (ReceiveResult M))
    (hmem : (res, s') ∈ support (StateT.run (m := ProbComp) (injectH ae G maxSkip (hpIdeal N false) (DG G) none q) s)) :
    s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    s'.1.ended = s.1.ended ∧
    (∀ r' ∈ s'.1.inTransit, r' ∈ s.1.inTransit) ∧
    (∀ i' mo', res = some (.accepted i' mo') →
      i' = q.2.1 ∧ s.1.isCompromised i' = true) ∧
    ((∀ i' mo', res ≠ some (.accepted i' mo')) → s'.1.inTransit = s.1.inTransit) := by
  unfold injectH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, fun _ h => h, by intro _ _ h; simp at h, fun _ => rfl⟩
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨ro, s₁⟩, hro, hs'⟩
    have hpres : s₁.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
        s₁.1.lastSentIdx = s.1.lastSentIdx ∧ s₁.1.ended = s.1.ended ∧
        s₁.1.inTransit = s.1.inTransit ∧
        (∀ i' m', ro = some (i', m') → i' = q.2.1 ∧ s.1.isCompromised i' = true) := by
      unfold receiveH at hro
      simp only [StateT.run_bind, getH_run, pure_bind] at hro
      split_ifs at hro
      · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hro
        rcases hro with ⟨⟨mo0, s₂⟩, hdec, hfin⟩
        by_cases hc : s.1.isCompromised q.2.1 = false
        · rw [decIdx_hpIdeal_none ae N false q.2.1 q.1 q.2.2 s hc] at hdec
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hdec hfin
          rcases hdec with ⟨rfl, rfl⟩; rcases hfin with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl, by intro _ _ h; simp at h⟩
        · simp only [Bool.not_eq_false] at hc
          rcases mem_support_decIdx ae hdec with ⟨rfl, _⟩
          cases mo0 with
          | none =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
            rcases hfin with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl, rfl, rfl, by intro _ _ h; simp at h⟩
          | some m0 =>
            simp only [StateT.run_bind, modifyH_run, StateT.run_pure, MonadAttach.mem_support_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
            rcases hfin with ⟨_, rfl, rfl, rfl⟩
            refine ⟨rfl, rfl, rfl, rfl, fun i' _ hi => ?_⟩
            injection hi with hpair; injection hpair with hi_eq _
            exact ⟨hi_eq.symm, hi_eq ▸ hc⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hro
        rcases hro with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, by intro _ _ h; simp at h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hro
        rcases hro with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, by intro _ _ h; simp at h⟩
      · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hro
        rcases hro with ⟨⟨_, s₂⟩, hgen, hrest⟩
        have hgen_pres := genUpTo_preserves_meta G (hpIdeal N false) q.2.1 s s₂ _ hgen
        rw [StateT.run_bind, MonadAttach.mem_support_bind] at hrest
        rcases hrest with ⟨⟨mo0, s₃⟩, hdec, hfin⟩
        by_cases hc : s.1.isCompromised q.2.1 = false
        · have hc₂ : s₂.1.isCompromised q.2.1 = false := by
            simpa [HState.isCompromised, hgen_pres.1] using hc
          rw [decIdx_hpIdeal_none ae N false q.2.1 q.1 q.2.2 s₂ hc₂] at hdec
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hdec hfin
          rcases hdec with ⟨rfl, rfl⟩; rcases hfin with ⟨rfl, rfl⟩
          exact ⟨hgen_pres.1, hgen_pres.2.1, hgen_pres.2.2.1, hgen_pres.2.2.2,
            by intro _ _ h; simp at h⟩
        · simp only [Bool.not_eq_false] at hc
          rcases mem_support_decIdx ae hdec with ⟨rfl, _⟩
          cases mo0 with
          | none =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
            rcases hfin with ⟨rfl, rfl⟩
            exact ⟨hgen_pres.1, hgen_pres.2.1, hgen_pres.2.2.1, hgen_pres.2.2.2,
              by intro _ _ h; simp at h⟩
          | some m0 =>
            simp only [StateT.run_bind, modifyH_run, StateT.run_pure, MonadAttach.mem_support_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
            rcases hfin with ⟨_, rfl, rfl, rfl⟩
            refine ⟨hgen_pres.1, hgen_pres.2.1, hgen_pres.2.2.1, hgen_pres.2.2.2,
              fun i' _ hi => ?_⟩
            injection hi with hpair; injection hpair with hi_eq _
            exact ⟨hi_eq.symm, hi_eq ▸ hc⟩
    cases ro with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hs'
      rcases hs' with ⟨rfl, rfl⟩
      exact ⟨hpres.1, hpres.2.1, hpres.2.2.1, fun _ h => hpres.2.2.2.1 ▸ h,
        by intro _ _ h; simp at h, fun _ => hpres.2.2.2.1⟩
    | some im =>
      rcases im with ⟨i', m'⟩
      have him := hpres.2.2.2.2 i' m' rfl
      simp only [hpIdeal, Bool.false_and, Bool.or_false, StateT.run_bind, modifyH_run,
        StateT.run_pure, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, HState.removeFromTransit] at hs'
      rcases hs' with ⟨_, rfl, rfl, rfl⟩
      refine ⟨hpres.1, hpres.2.1, hpres.2.2.1, ?_, ?_, ?_⟩
      · intro r' hr'
        rw [List.mem_filter] at hr'
        exact hpres.2.2.2.1 ▸ hr'.1
      · intro i₀ _ hacc
        injection hacc with hacc'
        injection hacc' with hi₀ _
        exact ⟨hi₀ ▸ him.1, hi₀ ▸ him.2⟩
      · intro hnotacc
        exact False.elim (hnotacc i' (some m') rfl)

theorem deliverH_hpIdeal_false_step_spec {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → _root_.PRGScheme CK (CK × MK)) (maxSkip N : ℕ)
    (q : AD × (ℕ × C)) (s s' : HSt CK MK AD M C) (res : Option (ReceiveResult M))
    (hct_idx : ∀ r ∈ s.1.inTransit, r.ct.1 = r.idx)
    (hmem : (res, s') ∈ support (StateT.run (m := ProbComp) (deliverH ae G maxSkip (hpIdeal N false) (DG G) none q) s)) :
    (res = none ∧ s' = s) ∨
    ∃ r_fs ∈ s.1.inTransit,
      r_fs.ad = q.1 ∧ r_fs.ct = q.2 ∧
      s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
      s'.1.lastSentIdx = s.1.lastSentIdx ∧
      s'.1.ended = s.1.ended ∧
      ((res = some .rejected ∧ s'.1.inTransit = s.1.inTransit) ∨
       (∃ mo', res = some (.accepted r_fs.idx mo') ∧
         s'.1.inTransit = s.1.inTransit.filter (·.idx != r_fs.idx))) := by
  unfold deliverH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind] at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact Or.inl hmem
  · cases hfind : s.1.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
    | none =>
      simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact Or.inl hmem
    | some r_fs =>
      have hr_mem : r_fs ∈ s.1.inTransit := List.mem_of_find?_eq_some hfind
      have hr_pred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hr_pred
      simp only [hfind, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨⟨ro, s₁⟩, hro, hs'⟩
      have hidx_eq : q.2.1 = r_fs.idx := by rw [← hr_pred.2, hct_idx r_fs hr_mem]
      have hpres : s₁.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
          s₁.1.lastSentIdx = s.1.lastSentIdx ∧ s₁.1.ended = s.1.ended ∧
          s₁.1.inTransit = s.1.inTransit ∧
          (ro = none ∨ ro = some (r_fs.idx, r_fs.msg)) := by
        unfold receiveH at hro
        simp only [StateT.run_bind, getH_run, pure_bind, decIdx] at hro
        split_ifs at hro
        · simp only [StateT.run_bind, modifyH_run, StateT.run_pure, MonadAttach.mem_support_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hro
          rcases hro with ⟨_, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl, Or.inr (by simp [hidx_eq])⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hro
          rcases hro with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hro
          rcases hro with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
        · rw [StateT.run_bind, MonadAttach.mem_support_bind] at hro
          rcases hro with ⟨⟨_, s₂⟩, hgen, hfin⟩
          have hgen_pres := genUpTo_preserves_meta G (hpIdeal N false) q.2.1 s s₂ _ hgen
          simp only [StateT.run_bind, modifyH_run, StateT.run_pure, MonadAttach.mem_support_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
          rcases hfin with ⟨_, rfl, rfl, rfl⟩
          exact ⟨hgen_pres.1, hgen_pres.2.1, hgen_pres.2.2.1, hgen_pres.2.2.2,
            Or.inr (by simp [hidx_eq])⟩
      refine Or.inr ⟨r_fs, hr_mem, hr_pred.1, hr_pred.2, ?_⟩
      rcases hpres.2.2.2.2 with rfl | rfl
      · simp only [StateT.run_bind, modifyH_run, StateT.run_pure, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hs'
        rcases hs' with ⟨_, rfl, rfl, rfl⟩
        exact ⟨hpres.1, hpres.2.1, hpres.2.2.1, Or.inl ⟨rfl, hpres.2.2.2.1⟩⟩
      · simp only [StateT.run_bind, modifyH_run, StateT.run_pure, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, HState.removeFromTransit] at hs'
        rcases hs' with ⟨_, rfl, rfl, rfl⟩
        exact ⟨hpres.1, hpres.2.1, hpres.2.2.1, Or.inr ⟨_, rfl, by rw [hpres.2.2.2.1]⟩⟩

theorem transmitHWith_hpIdeal_false_step_spec {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C)
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → _root_.PRGScheme CK (CK × MK)) (N : ℕ)
    (q : AD × M) (s s' : HSt CK MK AD M C) (res : Option (ℕ × C))
    (hend : s.1.ended = false)
    (hmem : (res, s') ∈ support (StateT.run (m := ProbComp) (transmitHWith ideal ae G (hpIdeal N false) (DG G) none q) s)) :
    ∃ rawCt,
      res = some (s.1.lastSentIdx + 1, rawCt) ∧
      s'.1.ended = false ∧
      s'.1.senderCorruptedAt = s.1.senderCorruptedAt ∧
      s'.1.lastSentIdx = s.1.lastSentIdx + 1 ∧
      s'.1.inTransit = ⟨s.1.lastSentIdx + 1, q.1, q.2, (s.1.lastSentIdx + 1, rawCt)⟩ :: s.1.inTransit := by
  unfold transmitHWith at hmem
  simp only [StateT.run_bind, getH_run, pure_bind, hend, Bool.false_eq_true, ↓reduceIte,
    MonadAttach.mem_support_bind] at hmem
  rcases hmem with ⟨⟨_, s₁⟩, hgen, ⟨rawCt, s₂⟩, henc, hfin⟩
  have hgen_pres := genUpTo_preserves_meta G (hpIdeal N false) (s.1.lastSentIdx + 1) s s₁ _ hgen
  rcases mem_support_encIdx ideal ae henc with rfl
  simp only [modifyH_run, StateT.run_pure, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at hfin
  rcases hfin with ⟨_, rfl, rfl, rfl⟩
  exact ⟨rawCt, rfl, hgen_pres.2.2.1.trans hend, hgen_pres.1, rfl, by rw [hgen_pres.2.2.2]⟩

theorem corruptSenderH_hpIdeal_false_step_spec {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (G : ℕ → _root_.PRGScheme CK (CK × MK)) (N : ℕ)
    (s s' : HSt CK MK AD M C) (res : Option (CryptoGames.FSAEAD.RatchetSenderState CK))
    (hend : s.1.ended = false)
    (hmem : (res, s') ∈ support (StateT.run (m := ProbComp) (corruptSenderH G (hpIdeal N false) ()) s)) :
    res.isSome = true ∧
    s'.1.ended = false ∧
    s'.1.senderCorruptedAt = some (s.1.senderCorruptedAt.getD s.1.lastSentIdx) ∧
    s'.1.lastSentIdx = s.1.lastSentIdx ∧
    s'.1.inTransit = s.1.inTransit := by
  unfold corruptSenderH at hmem
  simp only [StateT.run_bind, getH_run, pure_bind, hend, hpIdeal, Bool.false_eq_true, ↓reduceIte,
    MonadAttach.mem_support_bind] at hmem
  rcases hmem with ⟨⟨w, s₁⟩, hsk, hfin⟩
  have hsk_pres : s₁.1 = s.1 := mem_support_senderKey G hsk
  simp only [modifyH_run, StateT.run_pure, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at hfin
  rcases hfin with ⟨_, rfl, rfl, rfl⟩
  simp [hsk_pres, hend]

theorem runPubIdeal_liftFSMultiDFBucket_transmit_support
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ) (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    {Sig K I β : Type} (hs : FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32))
    (k : Option (ℕ × LibsignalCiphertextWithSalt32) × FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32) →
      OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMultiDFBucket sIdx (CryptoGames.FSAEAD.transmitQuery hdr pm)).run hs >>= k) rc σ)) :
    ∃ u ∈ support
      ((lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false))
        (.inl (.inl (.inl (.inl (.inl ((hdr, pm.1), pm.2))))))).run (σ sIdx)),
      w ∈ support (runPubIdeal C ℓ encT idOf N false (k (u.1, hs))
        rc (Function.update σ sIdx u.2)) := by
  rcases Computational.Proofs.E2E.SessionAuthMultiEndBucketLa.runPubIdeal_bind_support_false
    _ k rc σ hw with ⟨z, hz, hwz⟩
  erw [liftFSMultiDFBucket_run_query_eq,
    runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inl (.inl (.inl (.inl (.inl (hdr, pm)))))) hs rc σ,
    pubTag_tr_eq C ℓ encT idOf N false sIdx hdr pm (rc sIdx) σ] at hz
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hz
  rcases hz with ⟨u, hu, rfl⟩
  exact ⟨u, hu, by simpa only [Function.update_idem, Function.update_eq_self] using hwz⟩

theorem runPubIdeal_liftFSMultiDFBucket_corruptSender_support
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ) {Sig K I β : Type}
    (hs : FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32))
    (k : Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) ×
      FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32) →
      OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMultiDFBucket sIdx CryptoGames.FSAEAD.corruptSenderQuery).run hs >>= k) rc σ)) :
    ∃ u ∈ support
      ((lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hpIdeal N false))
        (.inl (.inl (.inl (.inr ()))))).run (σ sIdx)),
      w ∈ support (runPubIdeal C ℓ encT idOf N false (k (u.1, hs))
        rc (Function.update σ sIdx u.2)) := by
  rcases Computational.Proofs.E2E.SessionAuthMultiEndBucketLa.runPubIdeal_bind_support_false
    _ k rc σ hw with ⟨z, hz, hwz⟩
  erw [liftFSMultiDFBucket_run_query_eq,
    runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inl (.inl (.inl (.inr ())))) hs rc σ,
    pubTag_cs_eq C ℓ encT idOf N false sIdx () (rc sIdx) σ] at hz
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hz
  rcases hz with ⟨u, hu, rfl⟩
  exact ⟨u, hu, by simpa only [Function.update_idem, Function.update_eq_self] using hwz⟩

theorem runPubIdeal_liftFSMultiDFBucket_deliver_support
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ) (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    {Sig K I β : Type}
    (hs : FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32))
    (k : Option (ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) ×
      FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32) →
      OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMultiDFBucket sIdx (CryptoGames.FSAEAD.deliverQuery hdr e)).run hs >>= k) rc σ)) :
    (lPubOf protoSignalCodec e.2 = none ∧
      w ∈ support (runPubIdeal C ℓ encT idOf N false (k (none, hs)) rc σ)) ∨
    ∃ p, lPubOf protoSignalCodec e.2 = some p ∧
      ∃ u ∈ support
        ((lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hpIdeal N false))
          (.inl (.inr ((hdr, p), e)))).run (σ sIdx)),
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          (k (u.1.map (withPub p), hs)) rc (Function.update σ sIdx u.2)) := by
  rcases Computational.Proofs.E2E.SessionAuthMultiEndBucketLa.runPubIdeal_bind_support_false
    _ k rc σ hw with ⟨z, hz, hwz⟩
  erw [liftFSMultiDFBucket_run_query_eq,
    runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inl (.inr (hdr, e))) hs rc σ,
    pubTag_dl_eq C ℓ encT idOf N false sIdx hdr e (rc sIdx) σ] at hz
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    erw [hpub] at hz
    simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl ⟨rfl, by simpa only [Function.update_eq_self] using hwz⟩
  | some p =>
    erw [hpub] at hz
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨u, hu, rfl⟩
    exact Or.inr ⟨p, rfl, u, hu, by simpa only [Function.update_idem, Function.update_eq_self] using hwz⟩

theorem runPubIdeal_liftFSMultiDFBucket_inject_support
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ) (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    {Sig K I β : Type}
    (hs : FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32))
    (k : Option (ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) ×
      FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32) →
      OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    (w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ)))
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false
      ((liftFSMultiDFBucket sIdx (CryptoGames.FSAEAD.injectQuery hdr e)).run hs >>= k) rc σ)) :
    (lPubOf protoSignalCodec e.2 = none ∧
      w ∈ support (runPubIdeal C ℓ encT idOf N false
        (k (if rc sIdx then none else some .rejected, hs)) rc σ)) ∨
    ∃ p, lPubOf protoSignalCodec e.2 = some p ∧
      ∃ u ∈ support
        ((lazyInit fsInit (fsImpl (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hpIdeal N false))
          (.inr ((hdr, p), e))).run (σ sIdx)),
        w ∈ support (runPubIdeal C ℓ encT idOf N false
          (k (u.1.map (withPub p), hs)) rc (Function.update σ sIdx u.2)) := by
  rcases Computational.Proofs.E2E.SessionAuthMultiEndBucketLa.runPubIdeal_bind_support_false
    _ k rc σ hw with ⟨z, hz, hwz⟩
  erw [liftFSMultiDFBucket_run_query_eq,
    runPubIdeal_query_inr_eq C ℓ encT idOf N false sIdx
      (.inr (hdr, e)) hs rc σ,
    pubTag_ij_eq C ℓ encT idOf N false sIdx hdr e (rc sIdx) σ] at hz
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    erw [hpub] at hz
    simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl ⟨rfl, by simpa only [Function.update_eq_self] using hwz⟩
  | some p =>
    erw [hpub] at hz
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨u, hu, rfl⟩
    exact Or.inr ⟨p, rfl, u, hu, by simpa only [Function.update_idem, Function.update_eq_self] using hwz⟩

/-! ## 2. Bucket Session-Block Arithmetic & Coin-Only `startSend` / `startRecv` Specs -/

private theorem healEpoch_none : healEpoch none = 0 := rfl
private theorem healEpoch_some (l : ℕ) : healEpoch (some l) = l + 2 := rfl

theorem healEpoch_le_of_inStage2BucketGen {Δbucket u : ℕ} {tL : Option ℕ} {par : Bool}
    (hΔb : 2 ≤ Δbucket) (hb : inStage2BucketGen Δbucket tL par u = true) :
    healEpoch tL ≤ u := by
  simp only [inStage2BucketGen, Bool.and_eq_true] at hb
  have h1 := hb.1
  cases tL with
  | none => rw [healEpoch_none]; exact Nat.zero_le _
  | some l =>
    rw [healEpoch_some]
    simp only [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq] at h1
    omega

theorem ltOpt_of_ge_healEpoch {tL : Option ℕ} {u : ℕ} (h : healEpoch tL ≤ u) :
    ltOpt tL u = true := by
  cases tL with
  | none => rfl
  | some l =>
    rw [healEpoch_some] at h
    simp only [ltOpt, decide_eq_true_eq]
    omega

theorem sessBlock_div {q b r : ℕ} (hq : 1 ≤ q) (hr : r < q) :
    (q * b + r) / q = b := by
  have hpos : 0 < q := by omega
  induction b with
  | zero =>
    simpa using Nat.div_eq_of_lt hr
  | succ b ih =>
    have heq : q * (b + 1) + r = (q * b + r) + q := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [heq, Nat.add_div_right _ hpos, ih]

theorem regSessMultiDFBucket_spec {T RSt K I E : Type} [DecidableEq I]
    {q u : ℕ} {tL : Option ℕ} {ik : I} {hs : FSMultiDFBucketState T RSt K I E}
    (hq : 1 ≤ q) (hlen : (hs.sessions u).length < q) :
    let p := regSessMultiDFBucket (q + 1) tL u ik hs
    p.1 / q = u - healEpoch tL ∧
    p.2.cache = hs.cache ∧
    p.2.book = hs.book ∧
    p.2.lfWin = hs.lfWin ∧
    (p.2.sessions u).length ≤ (hs.sessions u).length + 1 ∧
    (∀ u', u' ≠ u → p.2.sessions u' = hs.sessions u') := by
  dsimp only [regSessMultiDFBucket]
  simp only [Nat.add_sub_cancel]
  split_ifs with hmem
  · have hidx : (hs.sessions u).idxOf ik < q :=
      Nat.lt_trans (List.idxOf_lt_length_iff.mpr hmem) hlen
    exact ⟨sessBlock_div hq hidx, rfl, rfl, rfl, Nat.le_succ _, fun _ _ => rfl⟩
  · refine ⟨sessBlock_div hq hlen, rfl, rfl, rfl, ?_, fun u' hu' => Function.update_of_ne hu' _ _⟩
    simp [Function.update_self]

theorem lookupMultiDFBucketF_coinOnly
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (t0 : ℕ) (ik : Pt)
    (hs : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) :
    CoinOnly (fun p =>
      p.2.cache = hs.cache ∧ p.2.sessions = hs.sessions ∧ p.2.book = hs.book ∧ p.2.lfWin = hs.lfWin)
      C ℓ encT idOf N
      ((lookupMultiDFBucketF (T := Pt) (RSt := BitVec 256) (K := BitVec 256)
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32) t0 ik).run hs) := by
  unfold lookupMultiDFBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (hs.fTable t0).lookup ik with
  | some k => simpa only [StateT.run_pure] using CoinOnly.pure ⟨rfl, rfl, rfl, rfl⟩
  | none =>
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    refine CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun k _ => ?_
    simp only [StateT.run_modify, pure_bind, StateT.run_pure]
    exact CoinOnly.pure ⟨rfl, rfl, rfl, rfl⟩

theorem rootFSMultiDFBucketPaper_coinOnly
    (C : Crypto) (ℓ : ℕ) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : Pt) (σ0 : BitVec 256)
    (hs : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) :
    CoinOnly (fun p =>
      p.2.cache = hs.cache ∧ p.2.sessions = hs.sessions ∧ p.2.book = hs.book ∧ p.2.lfWin = hs.lfWin ∧
      ((pl = false ∧ t0 ≤ qep + 1 ∧ inStage2BucketGen Δbucket tL par t0 = true ∧ p.1.2.2.isSome = true) ∨
       ((pl = true ∨ qep + 1 < t0 ∨ inStage2BucketGen Δbucket tL par t0 = false) ∧ p.1.2.2 = none)))
      C ℓ encT idOf N
      ((rootFSMultiDFBucketPaper (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (T := Pt)
        (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
        (CryptoGames.Ratchet.rootPRNG C.F encPt) Δbucket qep tL par t0 pl ik0 σ0).run hs) := by
  unfold rootFSMultiDFBucketPaper
  by_cases h1 : (pl || decide (qep + 1 < t0)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure]
    refine CoinOnly.pure ⟨rfl, rfl, rfl, rfl, Or.inr ⟨?_, rfl⟩⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with hpl | hgt
    · exact Or.inl hpl
    · exact Or.inr (Or.inl hgt)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h1
    rcases h1 with ⟨hpl, hle⟩
    by_cases h2 : inStage2BucketGen Δbucket tL par t0 = true
    · simp only [h2, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
        exact CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
          CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
            by simpa only [StateT.run_pure] using
              CoinOnly.pure ⟨rfl, rfl, rfl, rfl, Or.inl ⟨hpl, hle, trivial, rfl⟩⟩
      · simp only [StateT.run_bind]
        exact CoinOnly.bind (lookupMultiDFBucketF_coinOnly C ℓ encT idOf N t0 ik0 hs)
          fun ⟨_, hs₁⟩ ⟨hc, hse, hbk, hlf⟩ =>
            by simpa only [StateT.run_pure] using
              CoinOnly.pure ⟨hc, hse, hbk, hlf, Or.inl ⟨hpl, hle, trivial, rfl⟩⟩
    · simp only [Bool.not_eq_true] at h2
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
        exact CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
          CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun _ _ =>
            by simpa only [StateT.run_pure] using
              CoinOnly.pure ⟨rfl, rfl, rfl, rfl, Or.inr ⟨Or.inr (Or.inr trivial), rfl⟩⟩
      · simpa only [StateT.run_pure] using
          CoinOnly.pure ⟨rfl, rfl, rfl, rfl, Or.inr ⟨Or.inr (Or.inr trivial), rfl⟩⟩

theorem startSend_bucket_coinOnly
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hq : 1 ≤ q) (t_next : ℕ) (P : Party)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σr : BitVec 256) (r : Option (BitVec 256))
    (hs : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (hlen : (hs.sessions t_next).length < q) :
    CoinOnly (fun p =>
      ∃ γ' T' σr' ssv,
        p.1 = some (γ', T', σr', ssv) ∧
        p.2.book = hs.book ∧
        (p.2.sessions t_next).length ≤ (hs.sessions t_next).length + 1 ∧
        (∀ u', u' ≠ t_next → p.2.sessions u' = hs.sessions u') ∧
        (∀ u', u' ≠ t_next → p.2.cache u' = hs.cache u') ∧
        ((postLeakDFBucket tL ctx = false ∧ t_next ≤ qep + 1 ∧
          inStage2BucketGen Δbucket tL par t_next = true ∧
          ∃ s₀ k, ssv = .inr s₀ ∧ s₀ / q = t_next - healEpoch tL ∧
            p.2.cache t_next = some (T', σr', k, some s₀)) ∨
         ((postLeakDFBucket tL ctx = true ∨ qep + 1 < t_next ∨
           inStage2BucketGen Δbucket tL par t_next = false) ∧
          (∃ ss, ssv = .inl ss) ∧
          ∃ k, p.2.cache t_next = some (T', σr', k, none))))
      C ℓ encT idOf N
      (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).startSend
        ctx P t_next γ σr r).run hs) := by
  dsimp only [hooksFSMultiDFBucketPaper]
  cases r with
  | some coins =>
    simp only [pure_bind, StateT.run_bind]
    set cOut := (dhScheme Dh).send γ coins
    refine CoinOnly.bind
      (rootFSMultiDFBucketPaper_coinOnly C ℓ encPt encT idOf N Δbucket qep tL par
        t_next (postLeakDFBucket tL ctx) cOut.2.2 σr hs)
      fun ⟨⟨σ', kVal, sid⟩, hs₁⟩ ⟨hc₁, hse₁, hbk₁, _, hsid⟩ => ?_
    dsimp only at hc₁ hse₁ hbk₁ hsid
    simp only [StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure]
    rcases hsid with ⟨hpl, hle, hbuck, hsome⟩ | ⟨hnot, rfl⟩
    · rcases Option.isSome_iff_exists.mp hsome with ⟨ik, rfl⟩
      have hlen₁ : (hs₁.sessions t_next).length < q := hse₁ ▸ hlen
      rcases regSessMultiDFBucket_spec (q := q) (u := t_next) (tL := tL) (ik := ik) (hs := hs₁) hq hlen₁ with
        ⟨hdiv, hc₂, hbk₂, _, hlen₂, hse₂⟩
      dsimp only [regSessOptMultiDFBucket]
      refine CoinOnly.pure ⟨cOut.1, cOut.2.1, σ', .inr (regSessMultiDFBucket (q + 1) tL t_next ik hs₁).1,
        rfl, hbk₂.trans hbk₁, hse₁ ▸ hlen₂, fun u' hu' => (hse₂ u' hu').trans (congrFun hse₁ u'),
        fun u' hu' => by simp [Function.update_of_ne hu', hc₂, hc₁],
        Or.inl ⟨hpl, hle, hbuck, _, kVal, rfl, hdiv, by simp⟩⟩
    · dsimp only [regSessOptMultiDFBucket]
      refine CoinOnly.pure ⟨cOut.1, cOut.2.1, σ', .inl _, rfl, hbk₁,
        by rw [hse₁]; exact Nat.le_succ _, fun u' _ => congrFun hse₁ u',
        fun u' hu' => by simp [Function.update_of_ne hu', hc₁],
        Or.inr ⟨hnot, ⟨_, rfl⟩, kVal, by simp⟩⟩
  | none =>
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    refine CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun coins _ => ?_
    set cOut := (dhScheme Dh).send γ coins
    refine CoinOnly.bind
      (rootFSMultiDFBucketPaper_coinOnly C ℓ encPt encT idOf N Δbucket qep tL par
        t_next (postLeakDFBucket tL ctx) cOut.2.2 σr hs)
      fun ⟨⟨σ', kVal, sid⟩, hs₁⟩ ⟨hc₁, hse₁, hbk₁, _, hsid⟩ => ?_
    dsimp only at hc₁ hse₁ hbk₁ hsid
    simp only [StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure]
    rcases hsid with ⟨hpl, hle, hbuck, hsome⟩ | ⟨hnot, rfl⟩
    · rcases Option.isSome_iff_exists.mp hsome with ⟨ik, rfl⟩
      have hlen₁ : (hs₁.sessions t_next).length < q := hse₁ ▸ hlen
      rcases regSessMultiDFBucket_spec (q := q) (u := t_next) (tL := tL) (ik := ik) (hs := hs₁) hq hlen₁ with
        ⟨hdiv, hc₂, hbk₂, _, hlen₂, hse₂⟩
      dsimp only [regSessOptMultiDFBucket]
      refine CoinOnly.pure ⟨cOut.1, cOut.2.1, σ', .inr (regSessMultiDFBucket (q + 1) tL t_next ik hs₁).1,
        rfl, hbk₂.trans hbk₁, hse₁ ▸ hlen₂, fun u' hu' => (hse₂ u' hu').trans (congrFun hse₁ u'),
        fun u' hu' => by simp [Function.update_of_ne hu', hc₂, hc₁],
        Or.inl ⟨hpl, hle, hbuck, _, kVal, rfl, hdiv, by simp⟩⟩
    · dsimp only [regSessOptMultiDFBucket]
      refine CoinOnly.pure ⟨cOut.1, cOut.2.1, σ', .inl _, rfl, hbk₁,
        by rw [hse₁]; exact Nat.le_succ _, fun u' _ => congrFun hse₁ u',
        fun u' hu' => by simp [Function.update_of_ne hu', hc₁],
        Or.inr ⟨hnot, ⟨_, rfl⟩, kVal, by simp⟩⟩

theorem startRecv_bucket_coinOnly
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hq : 1 ≤ q) (t_recv : ℕ) (P : Party)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σr : BitVec 256) (Tn : Pt)
    (hs : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (hlen : (hs.sessions t_recv).length < q) :
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
      C ℓ encT idOf N
      (((hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false).startRecv
        ctx P t_recv γ σr Tn).run hs) := by
  dsimp only [hooksFSMultiDFBucketPaper]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hct : hs.cache t_recv with
  | none =>
    have hne_c : ∀ (σc k : BitVec 256) (optIdx : Option ℕ), none ≠ some (Tn, σc, k, optIdx) :=
      fun _ _ _ h => nomatch h
    dsimp only
    by_cases hcond : (!(decide (qep + 1 < t_recv)) && inStage2BucketGen Δbucket tL par t_recv) = true
    · simp only [hcond, ↓reduceIte]
      have hcond' := hcond
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hcond'
      rcases hcond' with ⟨hle, hbuck⟩
      split_ifs with htH hpl
      · simpa only [StateT.run_pure] using
          CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inl rfl⟩
      · simpa only [StateT.run_pure] using
          CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl,
            Or.inr (Or.inr ⟨_, _, _, rfl, Or.inr ⟨hne_c, hle, hbuck, Or.inl ⟨hpl, _, rfl⟩⟩⟩)⟩
      · simp only [Bool.not_eq_true] at hpl
        simp only [StateT.run_bind]
        set kk := (dhScheme Dh).receive γ Tn
        refine CoinOnly.bind (lookupMultiDFBucketF_coinOnly C ℓ encT idOf N t_recv kk.2 hs)
          fun ⟨_, hs₁⟩ ⟨hc₁, hse₁, hbk₁, _⟩ => ?_
        simp only [StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure]
        have hlen₁ : (hs₁.sessions t_recv).length < q := hse₁ ▸ hlen
        rcases regSessMultiDFBucket_spec (q := q) (u := t_recv) (tL := tL) (ik := kk.2)
            (hs := hs₁) hq hlen₁ with ⟨hdiv, hc₂, hbk₂, _, hlen₂, hse₂⟩
        exact CoinOnly.pure ⟨hc₂.trans hc₁, hbk₂.trans hbk₁, hse₁ ▸ hlen₂,
          fun u' hu' => (hse₂ u' hu').trans (congrFun hse₁ u'),
          Or.inr (Or.inr ⟨_, _, _, rfl,
            Or.inr ⟨hne_c, hle, hbuck, Or.inr ⟨hpl, _, rfl, hdiv⟩⟩⟩)⟩
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
      exact CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inr (Or.inl rfl)⟩
  | some quad =>
    rcases quad with ⟨Tc, σc, kVal, optIdx⟩
    by_cases hT : Tc = Tn
    · subst hT
      simp only [↓reduceIte, StateT.run_pure]
      cases optIdx with
      | none =>
        exact CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl,
          Or.inr (Or.inr ⟨_, σc, _, rfl, Or.inl ⟨σc, kVal, none, rfl, Or.inl ⟨rfl, _, rfl⟩⟩⟩)⟩
      | some s₀ =>
        exact CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl,
          Or.inr (Or.inr ⟨_, σc, _, rfl, Or.inl ⟨σc, kVal, some s₀, rfl, Or.inr ⟨s₀, rfl, rfl⟩⟩⟩)⟩
    · simp only [hT, ↓reduceIte]
      have hne_c : ∀ σc' k' optIdx', some (Tc, σc, kVal, optIdx) ≠ some (Tn, σc', k', optIdx') :=
        fun _ _ _ h => hT (by injection h with hq; exact (Prod.mk.inj hq).1)
      by_cases hcond : (!(decide (qep + 1 < t_recv)) && inStage2BucketGen Δbucket tL par t_recv) = true
      · simp only [hcond, ↓reduceIte]
        have hcond' := hcond
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hcond'
        rcases hcond' with ⟨hle, hbuck⟩
        split_ifs with htH hpl
        · simpa only [StateT.run_pure] using
            CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inl rfl⟩
        · simpa only [StateT.run_pure] using
            CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl,
              Or.inr (Or.inr ⟨_, _, _, rfl, Or.inr ⟨hne_c, hle, hbuck, Or.inl ⟨hpl, _, rfl⟩⟩⟩)⟩
        · simp only [Bool.not_eq_true] at hpl
          simp only [StateT.run_bind]
          set kk := (dhScheme Dh).receive γ Tn
          refine CoinOnly.bind (lookupMultiDFBucketF_coinOnly C ℓ encT idOf N t_recv kk.2 hs)
            fun ⟨_, hs₁⟩ ⟨hc₁, hse₁, hbk₁, _⟩ => ?_
          simp only [StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure]
          have hlen₁ : (hs₁.sessions t_recv).length < q := hse₁ ▸ hlen
          rcases regSessMultiDFBucket_spec (q := q) (u := t_recv) (tL := tL) (ik := kk.2)
              (hs := hs₁) hq hlen₁ with ⟨hdiv, hc₂, hbk₂, _, hlen₂, hse₂⟩
          exact CoinOnly.pure ⟨hc₂.trans hc₁, hbk₂.trans hbk₁, hse₁ ▸ hlen₂,
            fun u' hu' => (hse₂ u' hu').trans (congrFun hse₁ u'),
            Or.inr (Or.inr ⟨_, _, _, rfl,
              Or.inr ⟨hne_c, hle, hbuck, Or.inr ⟨hpl, _, rfl, hdiv⟩⟩⟩)⟩
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
        exact CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inr (Or.inl rfl)⟩

theorem startRecv_bucketMode_coinOnly
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (hq : 1 ≤ q) (t_recv : ℕ) (P : Party)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σr : BitVec 256) (Tn : Pt)
    (hs : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (hlen : (hs.sessions t_recv).length < q) :
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
      C ℓ encT idOf N
      (((hooksFSMultiDFBucketPaperMode (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep gMain tL par false).startRecv
        ctx P t_recv γ σr Tn).run hs) := by
  dsimp only [hooksFSMultiDFBucketPaperMode]
  cases gMain with
  | false =>
    exact startRecv_bucket_coinOnly C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
      hq t_recv P ctx γ σr Tn hs hlen
  | true =>
    simp only [↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    cases hct : hs.cache t_recv with
    | none =>
      split_ifs
      · simpa only [StateT.run_pure] using
          CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inl rfl⟩
      · simpa only [StateT.run_pure] using
          CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inr (Or.inl rfl)⟩
    | some quad =>
      rcases quad with ⟨Tc, σc, kVal, optIdx⟩
      by_cases hT : Tc = Tn
      · subst hT
        simp only [↓reduceIte, StateT.run_pure]
        cases optIdx with
        | none =>
          exact CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl,
            Or.inr (Or.inr ⟨_, σc, _, rfl, Or.inl ⟨σc, kVal, none, rfl, Or.inl ⟨rfl, _, rfl⟩⟩⟩)⟩
        | some s₀ =>
          exact CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl,
            Or.inr (Or.inr ⟨_, σc, _, rfl, Or.inl ⟨σc, kVal, some s₀, rfl, Or.inr ⟨s₀, rfl, rfl⟩⟩⟩)⟩
      · simp only [hT, ↓reduceIte]
        split_ifs
        · simpa only [StateT.run_pure] using
            CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inl rfl⟩
        · simpa only [StateT.run_pure] using
            CoinOnly.pure ⟨rfl, rfl, Nat.le_succ _, fun _ _ => rfl, Or.inr (Or.inl rfl)⟩

/-! ## 3. Bucket Target-Epoch & Global Invariants -/

abbrev BucketEState (Pt : Type) (ℓ : ℕ) :=
  EState
    (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
    (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))

@[expose] def IsTargetEpoch (Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) : Prop :=
  inStage2BucketGen Δbucket tL par t = true ∧
  lastLeakGuessAdmissible (2 + Δcka) tL t = true ∧
  t ≤ qep + 1

@[expose] def EpochBad {St Msg C : Type} (tL : Option ℕ) (t : ℕ) (g : GameState St Msg C) : Prop :=
  ∃ lk ∈ g.leaks, ltOpt tL lk = true ∧ lk < t

@[expose] def EpochCompEntry {ℓ : ℕ} (q : ℕ) (tL : Option ℕ) (t : ℕ)
    (es : BucketEState Pt ℓ) : Prop :=
  t ≤ es.g.epoch (Party.senderOf t) ∧
  (∃ cur, es.g.tL = some cur ∧ t ≤ cur) ∧
  (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∈ es.g.comp) ∧
  (∀ P sIdx, sIdx / q = t - healEpoch tL → (es.g.st P).vS ≠ some (.inr sIdx)) ∧
  (∀ P sIdx, (es.g.st P).vR t ≠ some (.inr sIdx)) ∧
  (∀ Tc σc k optIdx, es.h.cache t = some (Tc, σc, k, optIdx) → optIdx = none)

@[expose] def EpochPre {ℓ : ℕ} (q : ℕ) (tL : Option ℕ) (t : ℕ)
    (es : BucketEState Pt ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  (∀ P, es.g.epoch P < t) ∧
  (∀ cur, es.g.tL = some cur → cur < t) ∧
  postLeakDFBucket tL es.g = false ∧
  (∀ P, (es.g.st P).vR t = none) ∧
  (∀ P sIdx, sIdx / q = t - healEpoch tL → (es.g.st P).vS ≠ some (.inr sIdx)) ∧
  es.h.cache t = none ∧
  (∀ sIdx st, sIdx / q = t - healEpoch tL → σ sIdx = some st →
    st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
    st.1.inTransit = [] ∧ st.1.lastSentIdx = 0)

@[expose] def EpochIdealAt {ℓ : ℕ} (q Δcka : ℕ) (tL : Option ℕ) (t s₀ : ℕ)
    (es : BucketEState Pt ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  s₀ / q = t - healEpoch tL ∧
  t ≤ es.g.epoch (Party.senderOf t) ∧
  (∀ r ∈ es.g.trans, r.pos.epoch = t → r.ct.2.1 = r.pos.idx) ∧
  (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).vS = some (.inr s₀)) ∧
  (∀ P sIdx, sIdx / q = t - healEpoch tL → (es.g.st P).vS = some (.inr sIdx) →
    P = Party.senderOf t ∧ sIdx = s₀ ∧
    ((Party.senderOf t).sendsIn (es.g.epoch (Party.senderOf t)) = true →
      es.g.epoch (Party.senderOf t) = t ∧
      ((σ s₀ = none ∧ es.g.idx (Party.senderOf t) = 0) ∨
        ∃ st, σ s₀ = some st ∧ st.1.lastSentIdx = es.g.idx (Party.senderOf t)))) ∧
  (∀ sIdx st, sIdx / q = t - healEpoch tL → sIdx ≠ s₀ → σ sIdx = some st →
    st.1.ended = false ∧ st.1.senderCorruptedAt = none ∧
    st.1.inTransit = [] ∧ st.1.lastSentIdx = 0) ∧
  (σ s₀ = none → ∀ r ∈ es.g.trans, r.pos.epoch ≠ t) ∧
  (∀ st, σ s₀ = some st →
    st.1.ended = false ∧
    (∀ r_fs ∈ st.1.inTransit, r_fs.ct.1 = r_fs.idx ∧ r_fs.idx ≤ st.1.lastSentIdx) ∧
    (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos.idx ≤ st.1.lastSentIdx) ∧
    (healedBy es.g.tL (2 + Δcka) t = true →
      st.1.senderCorruptedAt = none ∧
      (∀ r_fs ∈ st.1.inTransit,
        ∃ m, ⟨⟨Party.senderOf t, t, r_fs.idx⟩, m, (r_fs.ad.1, r_fs.ct)⟩ ∈ es.g.trans)) ∧
    (∀ r ∈ es.g.trans, r.pos.epoch = t → r.pos ∉ es.g.comp →
      st.1.isCompromised r.pos.idx = false ∧
      (∀ r_fs ∈ st.1.inTransit, r_fs.idx = r.pos.idx → (r_fs.ad.1, r_fs.ct) = r.ct))) ∧
  (∀ P v, (es.g.st P).vR t = some v → v = .inr s₀) ∧
  (t ≤ es.g.epoch (Party.receiverOf t) → (es.g.st (Party.receiverOf t)).vR t = some (.inr s₀)) ∧
  (0 < t → ∃ Tc σc k,
    es.h.cache t = some (Tc, σc, k, some s₀) ∧
    (es.g.epoch (Party.senderOf t) = t → (es.g.st (Party.senderOf t)).curCkaMsg = some Tc) ∧
    (∀ r ∈ es.g.trans, r.pos.epoch = t → r.ct.1.2 = some Tc))

@[expose] def EpochIdeal {ℓ : ℕ} (q Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (es : BucketEState Pt ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  ∃ s₀, EpochIdealAt q Δcka tL t s₀ es σ

@[expose] def EpochInv {ℓ : ℕ} (q Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (es : BucketEState Pt ℓ) (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  EpochBad tL t es.g ∨
  EpochCompEntry q tL t es ∨
  EpochPre q tL t es σ ∨
  EpochIdeal q Δcka tL t es σ

theorem EpochIdealAt.congr_block {ℓ : ℕ} {q Δcka : ℕ} {tL : Option ℕ} {t s₀ : ℕ}
    {es : BucketEState Pt ℓ}
    {hs' : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    {σ σ' : ℕ → Option (IdealHSt Pt ℓ)}
    (h : EpochIdealAt q Δcka tL t s₀ es σ)
    (hc : hs'.cache t = es.h.cache t)
    (hσ : ∀ sIdx, sIdx / q = t - healEpoch tL → σ' sIdx = σ sIdx) :
    EpochIdealAt q Δcka tL t s₀ { es with h := hs' } σ' := by
  rcases h with ⟨hdiv, hep, hct_idx, hvS_eq, hvS_all, hunused, hnone_tr, hsome, hvR, hvR_ge, hpin⟩
  have hs₀_eq : σ' s₀ = σ s₀ := hσ s₀ hdiv
  refine ⟨hdiv, hep, hct_idx, hvS_eq, ?_, ?_, hs₀_eq ▸ hnone_tr, hs₀_eq ▸ hsome, hvR, hvR_ge,
    fun hpos => by simpa only [hc] using hpin hpos⟩
  · intro P sIdx hblk hvS
    rcases hvS_all P sIdx hblk hvS with ⟨hP, hsIdx, hsends⟩
    exact ⟨hP, hsIdx, hs₀_eq ▸ hsends⟩
  · intro sIdx st hblk hne hst
    exact hunused sIdx st hblk hne ((hσ sIdx hblk) ▸ hst)

theorem EpochInv.congr_block {ℓ : ℕ} {q Δcka : ℕ} {tL : Option ℕ} {t : ℕ}
    {es : BucketEState Pt ℓ}
    {hs' : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    {σ σ' : ℕ → Option (IdealHSt Pt ℓ)}
    (h : EpochInv q Δcka tL t es σ)
    (hc : hs'.cache t = es.h.cache t)
    (hσ : ∀ sIdx, sIdx / q = t - healEpoch tL → σ' sIdx = σ sIdx) :
    EpochInv q Δcka tL t { es with h := hs' } σ' := by
  rcases h with hbad | hcomp | hpre | ⟨s₀, hidl⟩
  · exact Or.inl hbad
  · refine Or.inr (Or.inl ⟨hcomp.1, hcomp.2.1, hcomp.2.2.1, hcomp.2.2.2.1, hcomp.2.2.2.2.1, ?_⟩)
    simpa only [hc] using hcomp.2.2.2.2.2
  · refine Or.inr (Or.inr (Or.inl ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2.1, hpre.2.2.2.2.1,
      hc.trans hpre.2.2.2.2.2.1, ?_⟩))
    intro sIdx st hblk hst
    exact hpre.2.2.2.2.2.2 sIdx st hblk ((hσ sIdx hblk) ▸ hst)
  · exact Or.inr (Or.inr (Or.inr ⟨s₀, hidl.congr_block hc hσ⟩))

theorem healedBy_iff_postLeakDFBucket_false {St Msg C : Type}
    {Δcka t : ℕ} {tL : Option ℕ} {g : GameState St Msg C}
    (hadm : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (htL_mem : ∀ cur, g.tL = some cur → cur ∈ g.leaks)
    (hnot_bad : ¬ EpochBad tL t g) :
    healedBy g.tL (2 + Δcka) t = true ↔ postLeakDFBucket tL g = false := by
  unfold postLeakDFBucket
  cases hcur : g.tL with
  | none => simp [healedBy]
  | some cur =>
    dsimp only
    constructor
    · intro hheal
      by_contra hlt_ne
      simp only [Bool.not_eq_false] at hlt_ne
      simp only [healedBy, decide_eq_true_eq] at hheal
      exact hnot_bad ⟨cur, htL_mem cur hcur, hlt_ne, by omega⟩
    · intro hlt_f
      cases tL with
      | none => simp [ltOpt] at hlt_f
      | some l =>
        simp only [ltOpt, decide_eq_false_iff_not, not_lt] at hlt_f
        simp only [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq] at hadm ⊢
        omega

structure GlobalBucketWF {ℓ : ℕ}
    (q Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (rem : ℕ)
    (es : BucketEState Pt ℓ) : Prop where
  habort : es.abort = false
  hwin : es.g.win = false
  hid : ∀ P, (es.g.st P).id = P
  htcur : ∀ P, (es.g.st P).tcur = es.g.epoch P
  htL_mem : ∀ cur, es.g.tL = some cur → cur ∈ es.g.leaks
  hsess_zero : ∀ ik ∈ es.h.sessions 0,
    inStage2BucketGen Δbucket tL par 0 = true ∧ (es.h.sessions 0).length = 1
  hsess_pos : ∀ u, 1 ≤ u → (es.h.sessions u).length + rem ≤ q
  hcache_blk : ∀ u Tc σc k sIdx,
    es.h.cache u = some (Tc, σc, k, some sIdx) →
      1 ≤ u ∧ inStage2BucketGen Δbucket tL par u = true ∧ u ≤ qep + 1 ∧
      sIdx / q = u - healEpoch tL
  hvR_blk : ∀ P u sIdx,
    (es.g.st P).vR u = some (.inr sIdx) →
      inStage2BucketGen Δbucket tL par u = true ∧ u ≤ qep + 1 ∧
      sIdx / q = u - healEpoch tL
  hvS_blk : ∀ P sIdx,
    (es.g.st P).vS = some (.inr sIdx) →
      ∃ u, u ≤ es.g.epoch P ∧
        (P.sendsIn (es.g.epoch P) = true → u = es.g.epoch P) ∧
        P = Party.senderOf u ∧
        inStage2BucketGen Δbucket tL par u = true ∧ u ≤ qep + 1 ∧
        sIdx / q = u - healEpoch tL
  htrans_wf : ∀ r ∈ es.g.trans,
    r.pos.epoch = r.ct.1.1 ∧
    r.pos.sender = Party.senderOf r.pos.epoch ∧
    r.pos.epoch ≤ es.g.epoch r.pos.sender ∧
    (r.pos.epoch = es.g.epoch r.pos.sender → r.pos.idx ≤ es.g.idx r.pos.sender)

@[expose] def BucketWon {ℓ : ℕ} (Δcka : ℕ) (tL : Option ℕ)
    (es : BucketEState Pt ℓ) (winEp : Option ℕ) : Prop :=
  es.g.win = true ∧
    ∀ tWin, winEp = some tWin →
      lastLeakGuessAdmissible (2 + Δcka) tL tWin = false ∨ EpochBad tL tWin es.g

@[expose] def BucketActive {ℓ : ℕ}
    (q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (rem : ℕ)
    (st : BucketEState Pt ℓ × Option ℕ) (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  st.2 = none ∧
  GlobalBucketWF q Δbucket qep tL par rem st.1 ∧
  (∀ t, IsTargetEpoch Δcka Δbucket qep tL par t → EpochInv q Δcka tL t st.1 σ)

@[expose] def BucketInv {ℓ : ℕ}
    (q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (rem : ℕ)
    (st : BucketEState Pt ℓ × Option ℕ) (σ : ℕ → Option (IdealHSt Pt ℓ)) : Prop :=
  st.1.abort = true ∨
  BucketWon Δcka tL st.1 st.2 ∨
  BucketActive q Δcka Δbucket qep tL par rem st σ

theorem authOutBucket_eq_false_of_bucketInv {ℓ : ℕ}
    {q Δcka Δbucket qep : ℕ} {tL : Option ℕ} {par : Bool} {rem : ℕ}
    {st : BucketEState Pt ℓ × Option ℕ} {σ : ℕ → Option (IdealHSt Pt ℓ)}
    (hinv : BucketInv q Δcka Δbucket qep tL par rem st σ) :
    authOutBucket (2 + Δcka) tL st = false := by
  rcases st with ⟨es, winEp⟩
  dsimp only [BucketInv, BucketWon, BucketActive] at hinv
  rcases hinv with hab | ⟨_, hbad_win⟩ | ⟨rfl, _, _⟩
  · cases winEp <;> simp [authOutBucket, authOut, hab]
  · cases winEp with
    | none => rfl
    | some tWin =>
      rcases hbad_win tWin rfl with hadm_f | ⟨lk, hlk_mem, hlt, hlt_t⟩
      · simp [authOutBucket, authOut, authLosingConditionsAvoided, hadm_f]
      · have hall_f : (es.g.leaks.all fun l => !(ltOpt tL l && decide (l < tWin))) = false := by
          rw [Bool.eq_false_iff]
          intro hall
          have hlk := List.all_eq_true.mp hall lk hlk_mem
          simp [hlt, hlt_t] at hlk
        simp only [authOutBucket, authOut, authLosingConditionsAvoided, hall_f,
          Bool.and_false, Bool.false_and]
  · rfl

theorem initFSMultiDFBucketPaper_bucketInv
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hq : 1 ≤ q) (hΔb : 2 ≤ Δbucket) :
    CoinOnly (fun p =>
      ∀ vA vB, p.1 = some (vA, vB) →
        BucketInv q Δcka Δbucket qep tL par q
          ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := p.2 }, none)
          (fun _ => (none : Option (IdealHSt Pt ℓ))))
      C ℓ encT idOf N
      ((initFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δbucket qep tL par).run {}) := by
  unfold initFSMultiDFBucketPaper
  simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
  refine CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun kr _ => ?_
  refine CoinOnly.bind (CoinOnly.sampleT C ℓ encT idOf N) fun kc _ => ?_
  refine CoinOnly.bind
    (rootFSMultiDFBucketPaper_coinOnly C ℓ encPt encT idOf N Δbucket qep tL par 0 false lam
      ((CryptoGames.Ratchet.rootPRNG C.F encPt).init kr) {})
    fun ⟨⟨σr, kVal, sid⟩, hs₁⟩ ⟨hc₁, hse₁, hbk₁, _, hsid⟩ => ?_
  have hs1_s : ∀ u, hs₁.sessions u = [] := congrFun hse₁
  have hs1_c : ∀ u, hs₁.cache u = none := congrFun hc₁
  simp only [StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure]
  rcases hsid with ⟨_, _, hbuck0, hsome⟩ | ⟨hnot0, rfl⟩
  · rcases Option.isSome_iff_exists.mp hsome with ⟨ik, rfl⟩
    have htH0 : healEpoch tL = 0 := Nat.eq_zero_of_le_zero (healEpoch_le_of_inStage2BucketGen hΔb hbuck0)
    have hdiv0 : 0 / q = 0 := Nat.div_eq_of_lt (by omega)
    dsimp only [regSessOptMultiDFBucket, regSessMultiDFBucket]
    simp only [hs1_s, List.not_mem_nil, ↓reduceIte, List.length_nil, Nat.add_zero, htH0,
      Nat.sub_self, Nat.mul_zero]
    refine CoinOnly.pure fun vA vB hv => ?_
    injection hv with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    refine Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)
    · refine {
        habort := rfl
        hwin := rfl
        hid := fun P => by cases P <;> rfl
        htcur := fun P => by cases P <;> rfl
        htL_mem := fun _ h => by simp at h
        hsess_zero := fun _ _ => ⟨hbuck0, rfl⟩
        hsess_pos := fun u hu => by
          have hne : u ≠ 0 := by omega
          simp [Function.update_of_ne hne, hs1_s]
        hcache_blk := fun _ _ _ _ _ h => by simp [hs1_c] at h
        hvR_blk := fun P u sIdx hvR => by
          cases P <;> simp at hvR
          rcases hvR with ⟨rfl, rfl⟩
          exact ⟨hbuck0, Nat.zero_le _, by rw [hdiv0, htH0]⟩
        hvS_blk := fun P sIdx hvS => by
          cases P <;> simp at hvS
          subst hvS
          exact ⟨0, le_rfl, fun _ => rfl, rfl, hbuck0, Nat.zero_le _, by rw [hdiv0, htH0]⟩
        htrans_wf := fun _ h => by simp at h
      }
    · intro t ht
      by_cases ht0 : t = 0
      · subst ht0
        refine Or.inr (Or.inr (Or.inr ⟨0, ?_⟩))
        refine ⟨by rw [hdiv0, htH0], le_rfl, fun _ h => by simp at h, fun _ => rfl, ?_,
          fun _ _ _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ h => by simp at h,
          fun P v hvR => by cases P <;> simp at hvR; exact hvR.symm,
          fun _ => rfl, fun h => by omega⟩
        intro P sIdx _ hvS
        cases P <;> simp at hvS
        subst hvS
        exact ⟨rfl, rfl, fun _ => ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · have hpos : 0 < t := Nat.pos_of_ne_zero ht0
        refine Or.inr (Or.inr (Or.inl ⟨fun _ => hpos, fun _ h => by simp at h, rfl,
          fun P => by cases P <;> simp [Nat.ne_of_gt hpos],
          fun P sIdx hblk hvS => ?_, by simp [hs1_c], fun _ _ _ h => by simp at h⟩))
        cases P <;> simp at hvS
        subst hvS
        rw [hdiv0, htH0, Nat.sub_zero] at hblk
        omega
  · dsimp only [regSessOptMultiDFBucket]
    refine CoinOnly.pure fun vA vB hv => ?_
    injection hv with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    refine Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)
    · refine {
        habort := rfl
        hwin := rfl
        hid := fun P => by cases P <;> rfl
        htcur := fun P => by cases P <;> rfl
        htL_mem := fun _ h => by simp at h
        hsess_zero := fun _ h => by simp [hs1_s] at h
        hsess_pos := fun u _ => by simp [hs1_s]
        hcache_blk := fun _ _ _ _ _ h => by simp [hs1_c] at h
        hvR_blk := fun P u sIdx hvR => by cases P <;> simp at hvR
        hvS_blk := fun P sIdx hvS => by cases P <;> simp at hvS
        htrans_wf := fun _ h => by simp at h
      }
    · intro t ht
      have hpos : 0 < t := by
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exfalso
          rcases hnot0 with hpl | hgt | hfb
          · cases hpl
          · omega
          · rw [ht.1] at hfb; cases hfb
        · exact hpos
      exact Or.inr (Or.inr (Or.inl ⟨fun _ => hpos, fun _ h => by simp at h, rfl,
        fun P => by cases P <;> simp [Nat.ne_of_gt hpos],
        fun P sIdx _ hvS => by cases P <;> simp at hvS,
        by simp [hs1_c], fun _ _ _ h => by simp at h⟩))

end BucketSteps

end

end Computational.Proofs.E2E.SessionAuthMultiEndBucketSteps

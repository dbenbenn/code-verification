/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.SendShortC -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FsAtomicMacros -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import

import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs
import Computational.Proofs.E2E.SessionAuthBridge
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.SessionCostedFig8.BundlesMultiFs
import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap
import Computational.Proofs.SessionCostedFs
public import Computational.Proofs.ReductionDsl.FsAtomicMacrosBase

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketQuery

public section

open scoped ENNReal
open OracleComp OracleSpec
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState encBadMsg)
open _root_.CryptoGames.GuardedSafe (GuardedSafePost)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open _root_.CryptoGames.SM (Config GameState specDF)
open _root_.CryptoGames.SM.Engine (EState Hooks TComp VP abortE coinsE commitE deliverE injectE
  run_liftH_bind vRecv vSend)
open _root_.CryptoGames.SM.Construction (FSMultiDFBucketState FSMultiSpec Header PartyState
  bucketAuthCfgGen hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode initFSMultiDFBucketPaper
  isHonestHdrFSMultiDFBucket liftFSMultiDFBucket lookupMultiDFBucketF
  redFSAuthDFPaperMultiBucketModeGen rootFSMultiDFBucketPaper sampleT)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF challEBucket corrEPaperBucket
  deliverForgeE engRunDFPaperBucketMode implEDFPaperBucketMode implEDFPaperBucketRaw
  transmitEBucket withWinEpDF withWinEpDFMode)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF badSendMsgDF)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)

private theorem hm_run_bind {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀} {HS α β : Type}
    (x : StateT HS (TComp tspec) α)
    (f : α → StateT HS (TComp tspec) β) (s : HS) :
    (x >>= f).run s = (x.run s >>= fun p => (f p.1).run p.2) := rfl

private abbrev SafeZeroAll {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (Q : spec.Domain → Prop) (oa : OracleComp spec α) : Prop :=
  GuardedSafePost (fun _ _ => True) Q (fun _ => True) oa

private theorem safeZeroAll_to_isQueryBoundP
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {Q : spec.Domain → Prop} [DecidablePred Q] {oa : OracleComp spec α}
    (h : SafeZeroAll Q oa) : oa.IsQueryBoundP Q 0 := by
  induction h with
  | pure _ => simp
  | query_bind hQt _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl hQt, fun u => by simpa [hQt] using ih u trivial⟩

private theorem safeZeroAll_pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {Q : spec.Domain → Prop} (a : α) :
    SafeZeroAll Q (pure a : OracleComp spec α) :=
  GuardedSafePost.pure trivial

private theorem safeZeroAll_run_pure {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀} {HS α : Type}
    {Q : (unifSpec + tspec).Domain → Prop} (a : α) (s : HS) :
    SafeZeroAll Q ((pure a : StateT HS (TComp tspec) α).run s) :=
  safeZeroAll_pure (a, s)

private theorem safeZeroAll_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {Q : spec.Domain → Prop} {oa : OracleComp spec α} {f : α → OracleComp spec β}
    (hoa : SafeZeroAll Q oa) (hf : ∀ a, SafeZeroAll Q (f a)) :
    SafeZeroAll Q (oa >>= f) :=
  hoa.bind fun a _ => hf a

private theorem redFSAuthDFPaperMultiBucketModeGen_query_zero
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType Pt] [SampleableType KR] [SampleableType K]
    (L : ℕ) (cka : CKAScheme (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG KR RSt Pt K) (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (lam : Pt) (Δcka Δbucket qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (MsgOk : M → Bool)
    (Pbad : (unifSpec + FSMultiSpec SS RS Pt M E).Domain → Prop) [DecidablePred Pbad]
    (hUnif0 : ∀ n, ¬ Pbad (.inl n))
    (hCorrS : ∀ sIdx, ¬ Pbad (.inr ⟨sIdx, .inl (.inl (.inl (.inr ())))⟩))
    (hTrans : ∀ sIdx hdr m, MsgOk m = true →
      ¬ Pbad (.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl (hdr, m)))))⟩))
    (hChall : ∀ sIdx hdr m₀ m₁, MsgOk m₀ = true → MsgOk m₁ = true →
      ¬ Pbad (.inr ⟨sIdx, .inl (.inl (.inl (.inl (.inr (hdr, m₀, m₁)))))⟩))
    (hDeliv : ∀ sIdx hdr e, ¬ Pbad (.inr ⟨sIdx, .inl (.inr (hdr, e))⟩))
    (hInj : ∀ sIdx hdr e, ¬ Pbad (.inr ⟨sIdx, .inr (hdr, e)⟩))
    (A : AdversaryDF (PartyState (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E))
    (hsh : SendMsgsOkDF MsgOk A) :
    (redFSAuthDFPaperMultiBucketModeGen L cka prng fs lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP
      Pbad 0 := by
  apply safeZeroAll_to_isQueryBoundP
  have hSample : ∀ (HS X : Type) [SampleableType X] (h : HS),
      SafeZeroAll Pbad
        ((StateT.lift (sampleT (tspec := FSMultiSpec SS RS Pt M E) X) :
          StateT HS (TComp (FSMultiSpec SS RS Pt M E)) X).run h) := by
    intro HS X _ h
    rw [StateT.run_lift]
    exact (GuardedSafePost.liftComp_unif hUnif0 ($ᵗ X : ProbComp X)).bind
      fun _ _ => safeZeroAll_pure _
  have hLiftOk : ∀ sIdx (q : (_root_.CryptoGames.FSAEAD.spec SS RS (Header Pt) M E).Domain),
      ¬ Pbad (.inr ⟨sIdx, q⟩) →
      ∀ h, SafeZeroAll Pbad
        ((liftFSMultiDFBucket (T := Pt) (Sig := RSt) (K := K) (I := Pt) (E := E) sIdx
          (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header Pt) M E) (.inr q)))).run h) := by
    intro sIdx q hq h
    have hEq :
        ((liftFSMultiDFBucket (T := Pt) (Sig := RSt) (K := K) (I := Pt) (E := E) sIdx
          (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header Pt) M E) (.inr q)))).run h) =
        ((liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS RS Pt M E) (.inr ⟨sIdx, q⟩)) :
          TComp (FSMultiSpec SS RS Pt M E) _) >>= fun a => pure (a, h)) := by
      simp [liftFSMultiDFBucket, StateT.run_lift]
    rw [hEq]
    exact GuardedSafePost.query_bind hq fun _ _ => safeZeroAll_pure _
  have hLookup : ∀ t0 ik (h : FSMultiDFBucketState Pt RSt K Pt E),
      SafeZeroAll Pbad
        ((lookupMultiDFBucketF (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E) t0 ik).run h) := by
    intro t0 ik h
    unfold lookupMultiDFBucketF
    rw [hm_run_bind, StateT.run_get, pure_bind]
    dsimp only
    cases (h.fTable t0).lookup ik with
    | some _ => exact safeZeroAll_run_pure _ _
    | none =>
      dsimp only; rw [hm_run_bind]
      refine safeZeroAll_bind (hSample _ K h) fun ⟨_, h₁⟩ => ?_
      rw [hm_run_bind, StateT.run_modify, pure_bind]
      exact safeZeroAll_run_pure _ _
  have hRoot : ∀ t0 pl ik0 σ0 (h : FSMultiDFBucketState Pt RSt K Pt E),
      SafeZeroAll Pbad
        ((rootFSMultiDFBucketPaper (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E)
          prng Δbucket qep tL par t0 pl ik0 σ0).run h) := by
    intro t0 pl ik0 σ0 h
    unfold rootFSMultiDFBucketPaper
    dsimp only
    split_ifs
    · exact safeZeroAll_run_pure _ _
    · rw [hm_run_bind]
      refine safeZeroAll_bind (hSample _ Pt h) fun ⟨_, h₁⟩ => ?_
      rw [hm_run_bind]
      exact safeZeroAll_bind (hSample _ K h₁) fun _ => safeZeroAll_run_pure _ _
    · rw [hm_run_bind]
      exact safeZeroAll_bind (hLookup t0 ik0 h) fun _ => safeZeroAll_run_pure _ _
    · rw [hm_run_bind]
      refine safeZeroAll_bind (hSample _ Pt h) fun ⟨_, h₁⟩ => ?_
      rw [hm_run_bind]
      exact safeZeroAll_bind (hSample _ K h₁) fun _ => safeZeroAll_run_pure _ _
    · exact safeZeroAll_run_pure _ _
  unfold redFSAuthDFPaperMultiBucketModeGen engRunDFPaperBucketMode
  generalize hhk : hooksFSMultiDFBucketPaperMode L cka prng fs Δcka Δbucket qep gMain tL par la = hk
  generalize hcfg : bucketAuthCfgGen (Msg := M) Δbucket tL par = cfg
  have hStartSend : ∀ ctx P t γ σ r h, SafeZeroAll Pbad ((hk.startSend ctx P t γ σ r).run h) := by
    intro ctx P t γ σ r h
    subst hhk
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]
    rcases r with _ | c
    · dsimp only; rw [hm_run_bind]
      refine safeZeroAll_bind (hSample _ (BitVec 256) h) fun ⟨_, h₀⟩ => ?_
      rw [hm_run_bind]
      refine safeZeroAll_bind (hRoot _ _ _ _ h₀) fun ⟨⟨_, _, _⟩, _⟩ => ?_
      rw [hm_run_bind, StateT.run_get, pure_bind, hm_run_bind, StateT.run_set, pure_bind]
      exact safeZeroAll_run_pure _ _
    · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind, hm_run_bind]
      refine safeZeroAll_bind (hRoot _ _ _ _ h) fun ⟨⟨_, _, _⟩, _⟩ => ?_
      rw [hm_run_bind, StateT.run_get, pure_bind, hm_run_bind, StateT.run_set, pure_bind]
      exact safeZeroAll_run_pure _ _
  have hStartRecvBase : ∀ ctx P t γ σ Tn h,
      SafeZeroAll Pbad (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).startRecv ctx P t γ σ Tn).run h) := by
    intro ctx P t γ σ Tn h
    dsimp only [hooksFSMultiDFBucketPaper]
    rw [hm_run_bind, StateT.run_get, pure_bind]
    dsimp only
    cases h.cache t with
    | none =>
      dsimp only
      split_ifs
      · exact safeZeroAll_run_pure _ _
      · exact safeZeroAll_run_pure _ _
      · rw [hm_run_bind]
        refine safeZeroAll_bind (hLookup t _ h) fun ⟨_, _⟩ => ?_
        rw [hm_run_bind, StateT.run_get, pure_bind, hm_run_bind, StateT.run_set, pure_bind]
        exact safeZeroAll_run_pure _ _
      · exact safeZeroAll_run_pure _ _
    | some cv =>
      rcases cv with ⟨tCached, _, _, _⟩
      dsimp only
      by_cases hT : tCached = Tn
      · simp only [hT, ↓reduceIte]; exact safeZeroAll_run_pure _ _
      · simp only [hT, ↓reduceIte]
        split_ifs
        · exact safeZeroAll_run_pure _ _
        · exact safeZeroAll_run_pure _ _
        · rw [hm_run_bind]
          refine safeZeroAll_bind (hLookup t _ h) fun ⟨_, _⟩ => ?_
          rw [hm_run_bind, StateT.run_get, pure_bind, hm_run_bind, StateT.run_set, pure_bind]
          exact safeZeroAll_run_pure _ _
        · exact safeZeroAll_run_pure _ _
  have hStartRecv : ∀ ctx P t γ σ Tn h, SafeZeroAll Pbad ((hk.startRecv ctx P t γ σ Tn).run h) := by
    intro ctx P t γ σ Tn h
    subst hhk
    cases gMain
    · exact hStartRecvBase ctx P t γ σ Tn h
    · simp only [hooksFSMultiDFBucketPaperMode, ↓reduceIte]
      rw [hm_run_bind, StateT.run_get, pure_bind]
      dsimp only
      cases h.cache t with
      | none =>
        dsimp only; split_ifs <;> exact safeZeroAll_run_pure _ _
      | some cv =>
        rcases cv with ⟨tCached, _, _, _⟩
        dsimp only
        by_cases hT : tCached = Tn
        · simp only [hT, ↓reduceIte]; exact safeZeroAll_run_pure _ _
        · simp only [hT, ↓reduceIte]; split_ifs <;> exact safeZeroAll_run_pure _ _
  have hFsSend : ∀ ctx P t ssv hdr m pair h, MsgOk m = true →
      (∀ m₀ m₁, pair = some (m₀, m₁) → MsgOk m₀ = true ∧ MsgOk m₁ = true) →
      SafeZeroAll Pbad ((hk.fsSend ctx P t ssv hdr m pair).run h) := by
    intro ctx P t ssv hdr m pair h hm hpair
    subst hhk
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]
    rcases ssv with _ | sIdx
    · exact safeZeroAll_run_pure _ _
    · dsimp only
      rw [hm_run_bind, StateT.run_get, pure_bind]
      dsimp only
      by_cases hc : (!GameState.safeCh ctx (2 + Δcka) P && !((h.book sIdx).getD {}).sCorr) = true
      · simp only [hc, ↓reduceIte]
        rw [hm_run_bind]
        refine safeZeroAll_bind (hLiftOk sIdx _ (hCorrS sIdx) h) fun ⟨o, h₁⟩ => ?_
        rcases o with _ | _
        · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]
          exact safeZeroAll_run_pure _ _
        · dsimp only
          rw [hm_run_bind, StateT.run_modify, pure_bind, hm_run_bind, StateT.run_pure, pure_bind]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases pair with _ | ⟨m₀, m₁⟩
          · dsimp only; rw [hm_run_bind]
            refine safeZeroAll_bind (hLiftOk sIdx _ (hTrans sIdx hdr m hm) _) fun ⟨e?, _⟩ => ?_
            rcases e? with _ | _
            · exact safeZeroAll_run_pure _ _
            · dsimp only; rw [hm_run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
          · obtain ⟨hm₀, hm₁⟩ := hpair m₀ m₁ rfl
            dsimp only; rw [hm_run_bind]
            refine safeZeroAll_bind (hLiftOk sIdx _ (hChall sIdx hdr m₀ m₁ hm₀ hm₁) _) fun ⟨e?, _⟩ => ?_
            rcases e? with _ | _
            · exact safeZeroAll_run_pure _ _
            · dsimp only; rw [hm_run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        rw [hm_run_bind, StateT.run_pure, pure_bind]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases pair with _ | ⟨m₀, m₁⟩
        · dsimp only; rw [hm_run_bind]
          refine safeZeroAll_bind (hLiftOk sIdx _ (hTrans sIdx hdr m hm) h) fun ⟨e?, _⟩ => ?_
          rcases e? with _ | _
          · exact safeZeroAll_run_pure _ _
          · dsimp only; rw [hm_run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
        · obtain ⟨hm₀, hm₁⟩ := hpair m₀ m₁ rfl
          dsimp only; rw [hm_run_bind]
          refine safeZeroAll_bind (hLiftOk sIdx _ (hChall sIdx hdr m₀ m₁ hm₀ hm₁) h) fun ⟨e?, _⟩ => ?_
          rcases e? with _ | _
          · exact safeZeroAll_run_pure _ _
          · dsimp only; rw [hm_run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
  have hFsRecv : ∀ ctx P t rsv hdr e rec_ h, SafeZeroAll Pbad ((hk.fsRecv ctx P t rsv hdr e rec_).run h) := by
    intro ctx P t rsv hdr e rec_ h
    subst hhk
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]
    rcases rsv with _ | sIdx
    · exact safeZeroAll_run_pure _ _
    · dsimp only
      rw [hm_run_bind, StateT.run_get, pure_bind]
      dsimp only
      by_cases hc : ((List.find? (fun x => x.2 == (hdr, e)) ((h.book sIdx).getD {}).fsTrans).isNone &&
          !_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t && !((h.book sIdx).getD {}).sCorr) = true
      · simp only [hc, ↓reduceIte]
        rw [hm_run_bind]
        refine safeZeroAll_bind (hLiftOk sIdx _ (hCorrS sIdx) h) fun ⟨o, h₁⟩ => ?_
        rcases o with _ | _
        · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]
          exact safeZeroAll_run_pure _ _
        · dsimp only
          rw [hm_run_bind, StateT.run_modify, pure_bind, hm_run_bind, StateT.run_pure, pure_bind]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases hm : (List.find? (fun x => x.2 == (hdr, e)) ((h.book sIdx).getD {}).fsTrans).isSome = true
          · simp only [hm, ↓reduceIte]
            rw [hm_run_bind]
            refine safeZeroAll_bind (hLiftOk sIdx _ (hDeliv sIdx hdr e) _) fun ⟨res, _⟩ => ?_
            rcases res with _ | (_ | ⟨_, mo'⟩)
            · exact safeZeroAll_run_pure _ _
            · exact safeZeroAll_run_pure _ _
            · dsimp only; rw [hm_run_bind, StateT.run_get, pure_bind]; dsimp only
              split_ifs
              · rw [hm_run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
              · rw [hm_run_bind, StateT.run_modify, pure_bind]; dsimp only
                rcases mo' with _ | _ <;> rcases rec_ with _ | _ <;> exact safeZeroAll_run_pure _ _
          · simp only [hm, Bool.false_eq_true, ↓reduceIte]
            rw [hm_run_bind]
            refine safeZeroAll_bind (hLiftOk sIdx _ (hInj sIdx hdr e) _) fun ⟨res, _⟩ => ?_
            rcases res with _ | (_ | ⟨_, mo'⟩)
            · exact safeZeroAll_run_pure _ _
            · exact safeZeroAll_run_pure _ _
            · dsimp only; rw [hm_run_bind, StateT.run_get, pure_bind]; dsimp only
              split_ifs
              · rw [hm_run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
              · rw [hm_run_bind, StateT.run_modify, pure_bind]; dsimp only
                rcases mo' with _ | _ <;> rcases rec_ with _ | _ <;> exact safeZeroAll_run_pure _ _
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        rw [hm_run_bind, StateT.run_pure, pure_bind]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases hm : (List.find? (fun x => x.2 == (hdr, e)) ((h.book sIdx).getD {}).fsTrans).isSome = true
        · simp only [hm, ↓reduceIte]
          rw [hm_run_bind]
          refine safeZeroAll_bind (hLiftOk sIdx _ (hDeliv sIdx hdr e) h) fun ⟨res, _⟩ => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact safeZeroAll_run_pure _ _
          · exact safeZeroAll_run_pure _ _
          · dsimp only; rw [hm_run_bind, StateT.run_get, pure_bind]; dsimp only
            split_ifs
            · rw [hm_run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
            · rw [hm_run_bind, StateT.run_modify, pure_bind]; dsimp only
              rcases mo' with _ | _ <;> rcases rec_ with _ | _ <;> exact safeZeroAll_run_pure _ _
        · simp only [hm, Bool.false_eq_true, ↓reduceIte]
          rw [hm_run_bind]
          refine safeZeroAll_bind (hLiftOk sIdx _ (hInj sIdx hdr e) h) fun ⟨res, _⟩ => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact safeZeroAll_run_pure _ _
          · exact safeZeroAll_run_pure _ _
          · dsimp only; rw [hm_run_bind, StateT.run_get, pure_bind]; dsimp only
            split_ifs
            · rw [hm_run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
            · rw [hm_run_bind, StateT.run_modify, pure_bind]; dsimp only
              rcases mo' with _ | _ <;> rcases rec_ with _ | _ <;> exact safeZeroAll_run_pure _ _
  have hRevealBase : ∀ ctx P vp h,
      SafeZeroAll Pbad (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).reveal ctx P vp).run h) := by
    intro ctx P vp h
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases vp.vS with _ | (_ | sIdx)
    · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]; dsimp only
      split_ifs <;> exact safeZeroAll_run_pure _ _
    · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]; dsimp only
      split_ifs <;> exact safeZeroAll_run_pure _ _
    · dsimp only; rw [hm_run_bind]
      refine safeZeroAll_bind (hLiftOk sIdx _ (hCorrS sIdx) h) fun ⟨o, _⟩ => ?_
      rcases o with _ | _
      · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]; exact safeZeroAll_run_pure _ _
      · dsimp only; rw [hm_run_bind, StateT.run_modify, pure_bind, hm_run_bind, StateT.run_pure, pure_bind]
        dsimp only; split_ifs <;> exact safeZeroAll_run_pure _ _
  have hReveal : ∀ ctx P vp h, SafeZeroAll Pbad ((hk.reveal ctx P vp).run h) := by
    intro ctx P vp h
    subst hhk
    cases gMain
    · simp only [hooksFSMultiDFBucketPaperMode, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · exact safeZeroAll_run_pure _ _
      · exact hRevealBase ctx P vp h
    · exact hRevealBase ctx P vp h
  have hvRecv : ∀ ctx P st c rec_ h, SafeZeroAll Pbad ((vRecv hk ctx P st c rec_).run h) := by
    intro ctx P st c rec_ h
    unfold vRecv; dsimp only
    by_cases hRej : (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) = true
    · simp only [hRej, ↓reduceIte]; exact safeZeroAll_run_pure _ _
    · simp only [hRej, Bool.false_eq_true, ↓reduceIte]
      by_cases hAdv : c.1.1 = st.tcur + 1
      · simp only [hAdv, ↓reduceIte]
        rcases c with ⟨⟨t0, tn0?⟩, ctE⟩
        dsimp only
        rcases tn0? with _ | tn0
        · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]; exact safeZeroAll_run_pure _ _
        · dsimp only; rw [hm_run_bind]
          refine safeZeroAll_bind (hStartRecv ctx P (st.tcur + 1) st.γ st.root tn0 h) fun ⟨sr, h₁⟩ => ?_
          rcases sr with _ | (_ | ⟨_, _, rsv⟩)
          · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]; exact safeZeroAll_run_pure _ _
          · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]; exact safeZeroAll_run_pure _ _
          · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]
            simp only [Function.update_self]
            rw [hm_run_bind]
            refine safeZeroAll_bind (hFsRecv ctx P (st.tcur + 1) rsv _ ctE rec_ h₁) fun ⟨fr, _⟩ => ?_
            rcases fr with _ | (_ | _) <;> exact safeZeroAll_run_pure _ _
      · simp only [hAdv, ↓reduceIte]
        rw [hm_run_bind, StateT.run_pure, pure_bind]
        dsimp only
        rcases st.vR c.1.1 with _ | rsv
        · exact safeZeroAll_run_pure _ _
        · dsimp only; rw [hm_run_bind]
          refine safeZeroAll_bind (hFsRecv ctx P c.1.1 rsv c.1 c.2 rec_ h) fun ⟨fr, _⟩ => ?_
          rcases fr with _ | (_ | _) <;> exact safeZeroAll_run_pure _ _
  have hCommit : ∀ s P old new pos es0, SafeZeroAll Pbad ((commitE hk s P old new pos).run es0) := by
    intro s P old new pos es0
    subst hhk
    unfold commitE
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]
    rw [run_liftH_bind, StateT.run_pure, pure_bind]
    exact safeZeroAll_run_pure _ _
  have hInit : SafeZeroAll Pbad ((initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par).run {}) := by
    unfold initFSMultiDFBucketPaper
    rw [hm_run_bind]
    refine safeZeroAll_bind (hSample _ KR ({} : FSMultiDFBucketState Pt RSt K Pt E)) fun ⟨_, h₀⟩ => ?_
    rw [hm_run_bind]
    refine safeZeroAll_bind (hSample _ (BitVec 256) h₀) fun ⟨_, h₁⟩ => ?_
    rw [hm_run_bind]
    refine safeZeroAll_bind (hRoot _ _ _ _ h₁) fun ⟨⟨_, _, _⟩, _⟩ => ?_
    rw [hm_run_bind, StateT.run_get, pure_bind, hm_run_bind, StateT.run_set, pure_bind]
    exact safeZeroAll_run_pure _ _
  rw [bind_assoc]
  refine safeZeroAll_bind hInit fun ⟨vs, _⟩ => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · exact safeZeroAll_pure _
  suffices hSim : SendMsgsOkDF MsgOk A →
      ∀ st : EState _ M (Header Pt × E) _ × Option ℕ,
      SafeZeroAll Pbad
        ((simulateQ (implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip cfg gMain isHonestHdrFSMultiDFBucket) A).run st) by
    dsimp only; rw [bind_assoc]
    exact safeZeroAll_bind (hSim hsh _) fun _ => safeZeroAll_pure _
  clear hsh
  induction A using OracleComp.inductionOn with
  | pure _ => intro _ _; simp only [simulateQ_pure, StateT.run_pure]; exact safeZeroAll_pure _
  | query_bind qy mx ih =>
    rintro hSendOk ⟨es, winEp⟩
    unfold SendMsgsOkDF at hSendOk
    rw [isQueryBoundP_query_bind_iff] at hSendOk
    rcases hSendOk with ⟨hBad0, hSendMx⟩
    rw [simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    refine safeZeroAll_bind ?_ fun ⟨u, st'⟩ => ih u (by simpa [SendMsgsOkDF] using hSendMx u) st'
    suffices hRaw : SafeZeroAll Pbad ((implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip cfg qy).run es) by
      cases gMain <;>
        (simp only [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, ↓reduceIte, Bool.false_eq_true];
         exact safeZeroAll_bind hRaw fun _ => safeZeroAll_pure _)
    rcases qy with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · change SafeZeroAll Pbad ((coinsE n).run es)
      unfold coinsE
      rw [StateT.run_lift]
      exact GuardedSafePost.query_bind (hUnif0 n) fun _ _ => safeZeroAll_pure _
    · have hm : MsgOk m = true := by
        have hFalse := Bool.eq_false_iff.mpr (hBad0.resolve_right (Nat.not_lt_zero 0))
        simpa [badSendMsgDF] using hFalse
      change SafeZeroAll Pbad ((transmitEBucket hk (2 + Δcka) qep (P, m, r)).run es)
      unfold transmitEBucket abortE vSend
      rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only
      split_ifs
      · exact safeZeroAll_run_pure _ _
      · rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
        · exact safeZeroAll_run_pure _ _
        · dsimp only; rw [run_liftH_bind]
          refine safeZeroAll_bind ?_ fun ⟨r?, _⟩ => by
            rcases r? with _ | _
            · dsimp only; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
            · dsimp only; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
          split_ifs
          · rw [hm_run_bind]
            refine safeZeroAll_bind (hStartSend _ _ _ _ _ _ _) fun ⟨sr, h₁⟩ => ?_
            rcases sr with _ | ⟨_, _, _, ssv⟩
            · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]; exact safeZeroAll_run_pure _ _
            · dsimp only; rw [hm_run_bind, StateT.run_pure, pure_bind]; dsimp only; rw [hm_run_bind]
              refine safeZeroAll_bind (hFsSend _ _ _ ssv _ m none h₁ hm (by simp)) fun ⟨fr, _⟩ => ?_
              rcases fr with _ | _ <;> exact safeZeroAll_run_pure _ _
          · rw [hm_run_bind, StateT.run_pure, pure_bind]; dsimp only
            rcases (s₁.st P).vS with _ | ssv
            · exact safeZeroAll_run_pure _ _
            · dsimp only; rw [hm_run_bind]
              refine safeZeroAll_bind (hFsSend _ _ _ ssv _ m none _ hm (by simp)) fun ⟨fr, _⟩ => ?_
              rcases fr with _ | _ <;> exact safeZeroAll_run_pure _ _
    · change SafeZeroAll Pbad ((challEBucket (P, m₀, m₁, r)).run es)
      unfold challEBucket; exact safeZeroAll_run_pure _ _
    · change SafeZeroAll Pbad ((deliverE hk fs.maxSkip cfg (P, c)).run es)
      unfold deliverE abortE
      rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only; split_ifs
      · exact safeZeroAll_run_pure _ _
      · rcases es.g.inTransit P.other c with _ | _
        · exact safeZeroAll_run_pure _ _
        · dsimp only; rw [run_liftH_bind]
          refine safeZeroAll_bind (hvRecv _ _ _ _ _ _) fun ⟨r?, _⟩ => ?_
          rcases r? with _ | (_ | ⟨_, _, _, _⟩)
          · dsimp only; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
          · dsimp only; split_ifs
            · rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
            · exact safeZeroAll_run_pure _ _
          · dsimp only; rw [StateT.run_bind]
            refine safeZeroAll_bind (hCommit _ _ _ _ _ _) fun ⟨s₁?, _⟩ => ?_
            rcases s₁? with _ | _
            · exact safeZeroAll_run_pure _ _
            · dsimp only; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
    · change SafeZeroAll Pbad ((_root_.CryptoGames.SM.Engine.injectE hk (2 + Δcka) qep cfg (P, c)).run es)
      unfold _root_.CryptoGames.SM.Engine.injectE abortE
      rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only; split_ifs
      · exact safeZeroAll_run_pure _ _
      · rw [run_liftH_bind]
        refine safeZeroAll_bind (hvRecv _ _ _ _ _ _) fun ⟨r?, _⟩ => ?_
        rcases r? with _ | (_ | ⟨_, _, _, _⟩)
        · dsimp only; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
        · exact safeZeroAll_run_pure _ _
        · dsimp only
          split_ifs
          · exact safeZeroAll_run_pure _ _
          · rw [StateT.run_bind]
            refine safeZeroAll_bind (hCommit _ _ _ _ _ _) fun ⟨s₁?, _⟩ => ?_
            rcases s₁? with _ | _
            · exact safeZeroAll_run_pure _ _
            · dsimp only; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
          · rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
          · exact safeZeroAll_run_pure _ _
    · change SafeZeroAll Pbad ((corrEPaperBucket hk P).run es)
      unfold corrEPaperBucket abortE
      rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only; split_ifs
      · exact safeZeroAll_run_pure _ _
      · rw [run_liftH_bind]
        refine safeZeroAll_bind (hReveal _ _ _ _) fun ⟨r?, _⟩ => ?_
        rcases r? with _ | _ <;>
          (dsimp only; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _)
    · change SafeZeroAll Pbad ((deliverForgeE hk (2 + Δcka) qep cfg (P, c, c')).run es)
      unfold deliverForgeE abortE
      rw [StateT.run_bind, StateT.run_get, pure_bind]; dsimp only; split_ifs
      · exact safeZeroAll_run_pure _ _
      · rcases es.g.inTransit P.other c with _ | _
        · exact safeZeroAll_run_pure _ _
        · dsimp only; split_ifs
          · exact safeZeroAll_run_pure _ _
          · rw [run_liftH_bind]
            refine safeZeroAll_bind (hvRecv _ _ _ _ _ _) fun ⟨r?, _⟩ => ?_
            rcases r? with _ | (_ | ⟨_, _, _, _⟩)
            · dsimp only; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
            · exact safeZeroAll_run_pure _ _
            · dsimp only
              split_ifs
              · exact safeZeroAll_run_pure _ _
              · rw [StateT.run_bind]
                refine safeZeroAll_bind (hCommit _ _ _ _ _ _) fun ⟨s₁?, _⟩ => ?_
                rcases s₁? with _ | _
                · exact safeZeroAll_run_pure _ _
                · dsimp only; rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
              · rw [StateT.run_bind, StateT.run_modify, pure_bind]; exact safeZeroAll_run_pure _ _
              · exact safeZeroAll_run_pure _ _

private theorem sendMsgsOkDF_true {St M Coins C : Type}
    (oa : AdversaryDF St M Coins C) :
    SendMsgsOkDF (fun _ : M => true) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp [SendMsgsOkDF]
  | query_bind qy mx ih =>
    unfold SendMsgsOkDF at ih ⊢
    rw [isQueryBoundP_query_bind_iff]
    have h0 : badSendMsgDF (St := St) (Coins := Coins) (C := C) (fun _ : M => true) qy = false := by
      rcases qy with _ | ((((((_ | _) | _) | _) | _) | _)) <;> simp [badSendMsgDF]
    exact ⟨Or.inl (by simp [h0]), fun u => by simpa [h0] using ih u⟩

theorem redFSAuthDFPaperMultiBucketModeGen_noCr
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType Pt] [SampleableType KR] [SampleableType K]
    (L : ℕ) (cka : CKAScheme (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG KR RSt Pt K) (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (lam : Pt) (Δcka Δbucket qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (PartyState (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E)) :
    (redFSAuthDFPaperMultiBucketModeGen L cka prng fs lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP
      (fun x => (match x with | .inr ⟨_, .inl (.inl (.inr _))⟩ => true | _ => false) = true) 0 :=
  redFSAuthDFPaperMultiBucketModeGen_query_zero L cka prng fs lam Δcka Δbucket qep gMain la tL par
    (fun _ => true) (fun x => (match x with | .inr ⟨_, .inl (.inl (.inr _))⟩ => true | _ => false) = true)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    A (sendMsgsOkDF_true A)

theorem redFSAuthDFPaperMultiBucketModeGen_encBadMsg
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (L ℓ Δcka Δbucket qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (s : ℕ)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    (redFSAuthDFPaperMultiBucketModeGen L (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep gMain la tL par A).IsQueryBoundP
      (fun x => (match x with
        | .inl _ => false
        | .inr ⟨s', qv⟩ => decide (s' = s) &&
            encBadMsg (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
              (AD := Header Pt) (C := ℕ × LibsignalCiphertextWithSalt32)
              (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr qv)) = true) 0 :=
  redFSAuthDFPaperMultiBucketModeGen_query_zero L (dhScheme Dh) (rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep gMain la tL par
    (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) _
    (by simp) (by simp [encBadMsg])
    (fun _ _ m hm => by have h1 := atomicShortPubB_imp_shortB hm; simp_all [encBadMsg, atomicShortB])
    (fun _ _ m₀ m₁ hm₀ hm₁ => by
      have h0 := atomicShortPubB_imp_shortB hm₀
      have h1 := atomicShortPubB_imp_shortB hm₁
      simp_all [encBadMsg, atomicShortB])
    (by simp [encBadMsg]) (by simp [encBadMsg]) A hsh


end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketQuery

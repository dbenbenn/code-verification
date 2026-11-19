/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiEndBase -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD
import Computational.Proofs.CryptoGames.SM.Theorem1.Queries
import Computational.Proofs.E2E.SpkHop2A
import Computational.Proofs.ReductionDsl.SM.Theorem1
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedShallow

/-!
# `la = true` and `q = 0` Zero-Output Helpers for `DeliverForgePaperMultiBucket`

Proves:
1. `redFSAuthDFPaperMultiBucket_la_true_zero`: `lfWin = false` across all bucket hooks at `la = true`.
2. `CoinOnly` combinators and `redFSAuthDFPaperMultiBucket_la_false_q_zero`: `winEp = none` when `q = 0`.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEndBucketLa

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.SM (Record healedBy)
open _root_.CryptoGames.SM.Construction (
  Header FSMultiDFBucketState FSMultiBook
  liftFSMultiDFBucket lookupMultiDFBucketF
  regSessMultiDFBucket regSessOptMultiDFBucket
  rootFSMultiDFBucketPaper hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode
  initFSMultiDFBucketPaper redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketMode
  isHonestHdrFSMultiDFBucket inStage2BucketGen bucketAuthCfgGen postLeakDFBucket)
open _root_.CryptoGames.SM.Construction.DeliverForge (
  AdversaryDF MakesAtMostQueriesDF
  deliverForgeE corrEPaperBucket transmitEBucket challEBucket
  implEDFPaperBucketRaw implEDFPaperBucket implEDFPaperBucketMode
  engRunDFPaperBucket engRunDFPaperBucketMode withWinEpDF withWinEpDFMode authOutBucket)
open _root_.CryptoGames.SM.Engine (
  Ctx VP EState liftH abortE vSend vRecv commitE deliverE injectE coinsE)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (
  LibsignalMsgPublicPart LibsignalCiphertextWithSalt32 lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift_inl)
open Computational.Proofs.E2E.SessionAuthMultiEnd (
  IdealHSt PubMultiSpec pubMultiImpl idealSessImpl runPubIdeal
  PubLaSafe liftFSMultiDFBucket_run_query_eq pubQuery_inject_not_accepted_la)

section Helpers

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## 1. `la = true`: `hooksFSMultiDFBucketPaper` & `implEDFPaperBucket` Preserve `lfWin = false` -/

private theorem pubQuery_bucket_any_eq_hs_la
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N sIdx : ℕ)
    (q₀ : (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    {Sig K I : Type}
    (hs : FSMultiDFBucketState Pt Sig K I (ℕ × LibsignalCiphertextWithSalt32)) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2 = hs)
      ((liftFSMultiDFBucket sIdx
        (query (spec := unifSpec + fsSpec (BitVec 256) (BitVec 256) (Header Pt)
          (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32) (Sum.inr q₀))).run hs) := by
  erw [liftFSMultiDFBucket_run_query_eq]
  exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => PubLaSafe.pure rfl

private theorem hooksFSMultiDFBucketPaper_fsRecv_lfWin_la
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (L N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (t0 : ℕ)
    (rsv : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hs : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (hlf : hs.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      (((hooksFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true).fsRecv
        ctx P t0 rsv hdr e rec).run hs) := by
  dsimp only [hooksFSMultiDFBucketPaper]
  rcases rsv with rs | sIdx
  · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
  · simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_bind, CryptoGames.FSAEAD.corruptSenderQuery]
      refine PubLaSafe.bind
        (pubQuery_bucket_any_eq_hs_la C ℓ encT idOf N sIdx (.inl (.inl (.inl (.inr ())))) hs) ?_
      rintro ⟨o, hs'⟩ rfl
      rcases o with _ | _
      · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
        exact PubLaSafe.pure hlf
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        generalize hfind : List.find? _ ((hs'.book sIdx).getD {}).fsTrans = matched
        clear hfind
        cases matched with
        | some m0 =>
          simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, CryptoGames.FSAEAD.deliverQuery]
          refine PubLaSafe.bind
            (pubQuery_bucket_any_eq_hs_la C ℓ encT idOf N sIdx (.inl (.inr (hdr, e))) _) ?_
          rintro ⟨res, _⟩ rfl
          rcases res with _ | (_ | ⟨i, mo'⟩)
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
          · simp only [StateT.run_bind, StateT.run_get, pure_bind,
              Option.isNone_some, Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_modify]
            rcases mo' with _ | m
            · rcases rec with _ | r <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf)
            · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            CryptoGames.FSAEAD.injectQuery]
          erw [liftFSMultiDFBucket_run_query_eq]
          refine PubLaSafe.bind
            (pubQuery_inject_not_accepted_la C ℓ encT idOf N sIdx hdr e _) ?_
          rintro ⟨res, _⟩ ⟨rfl, hnotacc⟩
          rcases res with _ | (_ | ⟨i, mo'⟩)
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
          · exact False.elim (hnotacc i mo' rfl)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      generalize hfind : List.find? _ ((hs.book sIdx).getD {}).fsTrans = matched
      clear hfind
      cases matched with
      | some m0 =>
        simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, CryptoGames.FSAEAD.deliverQuery]
        refine PubLaSafe.bind
          (pubQuery_bucket_any_eq_hs_la C ℓ encT idOf N sIdx (.inl (.inr (hdr, e))) _) ?_
        rintro ⟨res, _⟩ rfl
        rcases res with _ | (_ | ⟨i, mo'⟩)
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        · simp only [StateT.run_bind, StateT.run_get, pure_bind,
            Option.isNone_some, Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_modify]
          rcases mo' with _ | m
          · rcases rec with _ | r <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf)
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          CryptoGames.FSAEAD.injectQuery]
        erw [liftFSMultiDFBucket_run_query_eq]
        refine PubLaSafe.bind
          (pubQuery_inject_not_accepted_la C ℓ encT idOf N sIdx hdr e _) ?_
        rintro ⟨res, _⟩ ⟨rfl, hnotacc⟩
        rcases res with _ | (_ | ⟨i, mo'⟩)
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        · exact False.elim (hnotacc i mo' rfl)

private theorem rootFSMultiDFBucketPaper_lfWin_la
    (C : Crypto) (ℓ : ℕ) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (N Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : Pt) (σ0 : BitVec 256)
    (hs : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (hlf : hs.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      ((rootFSMultiDFBucketPaper
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32)
        (CryptoGames.Ratchet.rootPRNG C.F encPt) Δbucket qep tL par t0 pl ik0 σ0).run hs) := by
  unfold rootFSMultiDFBucketPaper
  dsimp only
  split_ifs
  · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
  · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => ?_
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => ?_
    simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
  · simp only [StateT.run_bind, lookupMultiDFBucketF, StateT.run_get, pure_bind]
    cases (hs.fTable t0).lookup ik0 with
    | some k => simp only [StateT.run_pure, pure_bind]; exact PubLaSafe.pure hlf
    | none =>
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => ?_
      simp only [StateT.run_modify, pure_bind, StateT.run_pure]
      exact PubLaSafe.pure hlf
  · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => ?_
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => ?_
    simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
  · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf

private theorem hooksFSMultiDFBucketPaper_nonRecv_lfWin_la
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (L N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hs : FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (hlf : hs.lfWin = false) :
    (∀ ctx P t0 γ σr r,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true).startSend
          ctx P t0 γ σr r).run hs)) ∧
    (∀ ctx P t0 γ σr Tn,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true).startRecv
          ctx P t0 γ σr Tn).run hs)) ∧
    (∀ ctx P t0 ssv hdr m pair,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true).fsSend
          ctx P t0 ssv hdr m pair).run hs)) ∧
    (∀ ctx P vp,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        (((hooksFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true).reveal
          ctx P vp).run hs)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ctx P t0 γ σr r
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases r with _ | coins
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun coins _ => ?_
      refine PubLaSafe.bind
        (rootFSMultiDFBucketPaper_lfWin_la C ℓ encPt encT idOf N Δbucket qep tL par t0
          (postLeakDFBucket tL ctx) ((dhScheme Dh).send γ coins).2.2 σr hs hlf)
        fun ⟨⟨σ', kVal, sid⟩, hs₂⟩ hlf₂ => ?_
      simp only [StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure]
      cases sid with
      | none => exact PubLaSafe.pure hlf₂
      | some ik =>
        dsimp only [regSessOptMultiDFBucket, regSessMultiDFBucket]
        split_ifs <;> exact PubLaSafe.pure hlf₂
    · simp only [pure_bind, StateT.run_bind]
      refine PubLaSafe.bind
        (rootFSMultiDFBucketPaper_lfWin_la C ℓ encPt encT idOf N Δbucket qep tL par t0
          (postLeakDFBucket tL ctx) ((dhScheme Dh).send γ coins).2.2 σr hs hlf)
        fun ⟨⟨σ', kVal, sid⟩, hs₂⟩ hlf₂ => ?_
      simp only [StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure]
      cases sid with
      | none => exact PubLaSafe.pure hlf₂
      | some ik =>
        dsimp only [regSessOptMultiDFBucket, regSessMultiDFBucket]
        split_ifs <;> exact PubLaSafe.pure hlf₂
  · intro ctx P t0 γ σr Tn
    dsimp only [hooksFSMultiDFBucketPaper]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    cases hs.cache t0 with
    | some entry =>
      rcases entry with ⟨tCached, σc, kVal, optIdx⟩
      by_cases heq : tCached = Tn
      · simp only [heq, ↓reduceIte, StateT.run_pure]
        exact PubLaSafe.pure hlf
      · simp only [heq, ↓reduceIte]
        split_ifs
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        · simp only [StateT.run_bind, lookupMultiDFBucketF, StateT.run_get, pure_bind]
          cases (hs.fTable t0).lookup ((dhScheme Dh).receive γ Tn).2 with
          | some _ =>
            simp only [StateT.run_pure, pure_bind, StateT.run_set]
            dsimp only [regSessMultiDFBucket]
            split_ifs <;> exact PubLaSafe.pure hlf
          | none =>
            simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
            refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => ?_
            simp only [StateT.run_modify, pure_bind, StateT.run_pure,
              StateT.run_set]
            dsimp only [regSessMultiDFBucket]
            split_ifs <;> exact PubLaSafe.pure hlf
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
    | none =>
      split_ifs
      · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      · simp only [StateT.run_bind, lookupMultiDFBucketF, StateT.run_get, pure_bind]
        cases (hs.fTable t0).lookup ((dhScheme Dh).receive γ Tn).2 with
        | some _ =>
          simp only [StateT.run_pure, pure_bind, StateT.run_set]
          dsimp only [regSessMultiDFBucket]
          split_ifs <;> exact PubLaSafe.pure hlf
        | none =>
          simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
          refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => ?_
          simp only [StateT.run_modify, pure_bind, StateT.run_pure,
            StateT.run_set]
          dsimp only [regSessMultiDFBucket]
          split_ifs <;> exact PubLaSafe.pure hlf
      · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
  · intro ctx P t0 ssv hdr m pair
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases ssv with ss | sIdx
    · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_bind, CryptoGames.FSAEAD.corruptSenderQuery]
        refine PubLaSafe.bind
          (pubQuery_bucket_any_eq_hs_la C ℓ encT idOf N sIdx (.inl (.inl (.inl (.inr ())))) hs) ?_
        rintro ⟨o, hs'⟩ rfl
        rcases o with _ | _
        · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
          exact PubLaSafe.pure hlf
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases pair with _ | ⟨m₀, m₁⟩
          · simp only [StateT.run_bind, CryptoGames.FSAEAD.transmitQuery]
            refine PubLaSafe.bind
              (pubQuery_bucket_any_eq_hs_la C ℓ encT idOf N sIdx
                (.inl (.inl (.inl (.inl (.inl (hdr, m)))))) _) ?_
            rintro ⟨e?, _⟩ rfl
            rcases e? with _ | e
            · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact PubLaSafe.pure hlf
          · simp only [StateT.run_bind, CryptoGames.FSAEAD.challengeQuery]
            refine PubLaSafe.bind
              (pubQuery_bucket_any_eq_hs_la C ℓ encT idOf N sIdx
                (.inl (.inl (.inl (.inl (.inr (hdr, m₀, m₁)))))) _) ?_
            rintro ⟨e?, _⟩ rfl
            rcases e? with _ | e
            · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact PubLaSafe.pure hlf
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases pair with _ | ⟨m₀, m₁⟩
        · simp only [StateT.run_bind, CryptoGames.FSAEAD.transmitQuery]
          refine PubLaSafe.bind
            (pubQuery_bucket_any_eq_hs_la C ℓ encT idOf N sIdx
              (.inl (.inl (.inl (.inl (.inl (hdr, m)))))) _) ?_
          rintro ⟨e?, _⟩ rfl
          rcases e? with _ | e
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PubLaSafe.pure hlf
        · simp only [StateT.run_bind, CryptoGames.FSAEAD.challengeQuery]
          refine PubLaSafe.bind
            (pubQuery_bucket_any_eq_hs_la C ℓ encT idOf N sIdx
              (.inl (.inl (.inl (.inl (.inr (hdr, m₀, m₁)))))) _) ?_
          rintro ⟨e?, _⟩ rfl
          rcases e? with _ | e
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact PubLaSafe.pure hlf
  · intro ctx P vp
    dsimp only [hooksFSMultiDFBucketPaper]
    rcases vp.vS with _ | (ss | sIdx)
    · simp only [pure_bind]
      split_ifs <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf)
    · simp only [pure_bind]
      split_ifs <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf)
    · simp only [StateT.run_bind, CryptoGames.FSAEAD.corruptSenderQuery]
      refine PubLaSafe.bind
        (pubQuery_bucket_any_eq_hs_la C ℓ encT idOf N sIdx (.inl (.inl (.inl (.inr ())))) hs) ?_
      rintro ⟨o, _⟩ rfl
      rcases o with _ | ss
      · simp only [StateT.run_pure, pure_bind]; exact PubLaSafe.pure hlf
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        split_ifs <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf)

private theorem implEDFPaperBucketRaw_step_lfWin_la
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (L N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hk : CryptoGames.SM.Engine.Hooks _ (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt
      (ℕ × LibsignalCiphertextWithSalt32))
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (hss_eq : hk.startSend = (hooksFSMultiDFBucketPaper L (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true).startSend)
    (hfs_eq : hk.fsSend = (hooksFSMultiDFBucketPaper L (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true).fsSend)
    (hfr_eq : hk.fsRecv = (hooksFSMultiDFBucketPaper L (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true).fsRecv)
    (hcm_eq : hk.commit = (hooksFSMultiDFBucketPaper L (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true).commit)
    (hsr_lf : ∀ hs, hs.lfWin = false → ∀ ctx P t0 γ0 σ0 tn0,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        ((hk.startRecv ctx P t0 γ0 σ0 tn0).run hs))
    (hrv_lf : ∀ hs, hs.lfWin = false → ∀ ctx P vp,
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
        ((hk.reveal ctx P vp).run hs))
    (q_in : _)
    (es : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
      (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (hlf : es.h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
      ((implEDFPaperBucketRaw hk
        (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par) q_in).run es) := by
  have hliftH : ∀ {α : Type}
      (m : CryptoGames.SM.Engine.HM
        (CryptoGames.SM.Construction.FSMultiSpec (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt (LibsignalMsgPublicPart × Plain ℓ)
          (ℕ × LibsignalCiphertextWithSalt32))
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) α)
      (es₀ : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))),
      PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false) (m.run es₀.h) →
      PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false) ((liftH m).run es₀) := by
    intro α m es₀ hm
    unfold liftH
    simp only []
    exact PubLaSafe.bind hm fun ⟨_, _⟩ hh' => PubLaSafe.pure hh'
  have hvSend : ∀ s₁ P vp m pair r
      (es₀ : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
      (hlf₀ : es₀.h.lfWin = false),
      PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
        ((liftH (vSend hk s₁ P vp m pair r)).run es₀) := by
    intro s₁ P vp m pair r es₀ hlf₀
    apply hliftH
    unfold vSend
    dsimp only
    split_ifs
    · simp only [StateT.run_bind, pure_bind, hss_eq]
      refine PubLaSafe.bind
        ((hooksFSMultiDFBucketPaper_nonRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
          Δbucket qep tL par es₀.h hlf₀).1 s₁ P (vp.tcur + 1) vp.γ vp.root r)
        fun ⟨o, h₁⟩ hlf₁ => ?_
      rcases o with _ | ⟨γ', T', σ', ss⟩
      · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
      · simp only [StateT.run_bind, hfs_eq]
        refine PubLaSafe.bind
          ((hooksFSMultiDFBucketPaper_nonRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
            Δbucket qep tL par h₁ hlf₁).2.2.1 s₁ P (vp.tcur + 1) ss (vp.tcur + 1, some T') m pair)
          fun ⟨res, _⟩ hlf₂ => ?_
        rcases res with _ | ⟨v', e⟩ <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂)
    · simp only [pure_bind]
      rcases vp.vS with _ | v
      · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₀
      · simp only [StateT.run_bind, hfs_eq]
        refine PubLaSafe.bind
          ((hooksFSMultiDFBucketPaper_nonRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
            Δbucket qep tL par es₀.h hlf₀).2.2.1 s₁ P vp.tcur v (vp.tcur, vp.curCkaMsg) m pair)
          fun ⟨res, _⟩ hlf₂ => ?_
        rcases res with _ | ⟨v', e⟩ <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂)
  have hvRecv : ∀ s₁ P vp c rec
      (es₀ : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
      (hlf₀ : es₀.h.lfWin = false),
      PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
        ((liftH (vRecv hk s₁ P vp c rec)).run es₀) := by
    intro s₁ P vp c rec es₀ hlf₀
    apply hliftH
    unfold vRecv
    dsimp only
    split
    · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₀
    · split
      · cases c.1.2 with
        | none => simp only [StateT.run_pure, pure_bind]; exact PubLaSafe.pure hlf₀
        | some Tn =>
          simp only [StateT.run_bind, pure_bind]
          refine PubLaSafe.bind (hsr_lf es₀.h hlf₀ s₁ P c.1.1 vp.γ vp.root Tn)
            fun ⟨o, h₁⟩ hlf₁ => ?_
          rcases o with _ | (_ | ⟨γ', σ', rs⟩)
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
          · simp only [Function.update_self, StateT.run_bind, hfr_eq]
            refine PubLaSafe.bind
              (hooksFSMultiDFBucketPaper_fsRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
                Δbucket qep tL par s₁ P c.1.1 rs c.1 c.2 rec h₁ hlf₁) fun ⟨res, _⟩ hlf₂ => ?_
            rcases res with _ | (_ | ⟨v', i, m⟩) <;>
              (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂)
      · simp only [pure_bind]
        rcases vp.vR c.1.1 with _ | v
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₀
        · simp only [StateT.run_bind, hfr_eq]
          refine PubLaSafe.bind
            (hooksFSMultiDFBucketPaper_fsRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
              Δbucket qep tL par s₁ P c.1.1 v c.1 c.2 rec es₀.h hlf₀) fun ⟨res, _⟩ hlf₂ => ?_
          rcases res with _ | (_ | ⟨v', i, m⟩) <;>
            (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₂)
  have hcommit : ∀ s₁ P old new pos
      (es₀ : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
      (hlf₀ : es₀.h.lfWin = false),
      PubLaSafe C ℓ encT idOf N (fun p => p.2.h.lfWin = false)
        ((commitE hk s₁ P old new pos).run es₀) := by
    intro s₁ P old new pos es₀ hlf₀
    unfold commitE
    rw [StateT.run_bind]
    refine PubLaSafe.bind (hliftH _ es₀ (by rw [hcm_eq]; dsimp only [hooksFSMultiDFBucketPaper]; simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₀)) ?_
    rintro ⟨o, es₁⟩ hlf₁
    cases o <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁)
  rcases q_in with n | ((((q1 | q2) | q3) | q4) | q5) | q6
  · change PubLaSafe _ _ _ _ _ _ ((coinsE n).run es)
    unfold coinsE
    rw [StateT.run_lift]
    exact PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun _ _ => PubLaSafe.pure hlf
  · rcases q1 with ⟨P, m, r⟩
    change PubLaSafe _ _ _ _ _ _ ((transmitEBucket _ (2 + Δcka) qep (P, m, r)).run es)
    unfold transmitEBucket
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
    · cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | some s₁ =>
        dsimp only
        rw [StateT.run_bind]
        refine PubLaSafe.bind (hvSend s₁ P (s₁.st P) m none r es hlf) fun ⟨res, _⟩ hlf₁ => ?_
        cases res <;>
          simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
          exact PubLaSafe.pure hlf₁
  · change PubLaSafe _ _ _ _ _ _ ((challEBucket q2).run es)
    unfold challEBucket
    simp only [StateT.run_pure]
    exact PubLaSafe.pure hlf
  · rcases q3 with ⟨P, c⟩
    change PubLaSafe _ _ _ _ _ _ ((deliverE _ maxForwardJumps (bucketAuthCfgGen Δbucket tL par) (P, c)).run es)
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
    · cases es.g.inTransit P.other c with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | some r =>
        dsimp only
        rw [StateT.run_bind]
        refine PubLaSafe.bind (hvRecv es.g P (es.g.st P) c (some r) es hlf)
          fun ⟨res, es₁⟩ hlf₁ => ?_
        rcases res with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
          exact PubLaSafe.pure hlf₁
        · dsimp only
          split <;>
            simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
            exact PubLaSafe.pure hlf₁
        · dsimp only
          rw [StateT.run_bind]
          refine PubLaSafe.bind (hcommit es.g P (es.g.st P) st' r.pos es₁ hlf₁)
            fun ⟨s1?, _⟩ hlf₂ => ?_
          cases s1? <;>
            simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
            exact PubLaSafe.pure hlf₂
  · rcases q4 with ⟨P, c⟩
    change PubLaSafe _ _ _ _ _ _ ((injectE _ (2 + Δcka) qep (bucketAuthCfgGen Δbucket tL par) (P, c)).run es)
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
    · rw [StateT.run_bind]
      refine PubLaSafe.bind (hvRecv es.g P (es.g.st P) c none es hlf)
        fun ⟨res, es₁⟩ hlf₁ => ?_
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
        exact PubLaSafe.pure hlf₁
      · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
      · dsimp only
        split
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
        · split
          · rw [StateT.run_bind]
            refine PubLaSafe.bind (hcommit es.g P (es.g.st P) st' ⟨P.other, t', i'⟩ es₁ hlf₁)
              fun ⟨s1?, _⟩ hlf₂ => ?_
            cases s1? <;>
              simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
              exact PubLaSafe.pure hlf₂
          · split <;>
              simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
              exact PubLaSafe.pure hlf₁
  · change PubLaSafe _ _ _ _ _ _ ((corrEPaperBucket _ q5).run es)
    unfold corrEPaperBucket
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
    · rw [StateT.run_bind]
      refine PubLaSafe.bind (hliftH _ es (hrv_lf es.h hlf es.g q5 (es.g.st q5)))
        fun ⟨res, _⟩ hlf₁ => ?_
      cases res <;>
        simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
        exact PubLaSafe.pure hlf₁
  · rcases q6 with ⟨P, c, c'⟩
    change PubLaSafe _ _ _ _ _ _ ((deliverForgeE _ (2 + Δcka) qep (bucketAuthCfgGen Δbucket tL par) (P, c, c')).run es)
    unfold deliverForgeE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
    · cases es.g.inTransit P.other c with
      | none => simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
      | some _ =>
        dsimp only
        split
        · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf
        · rw [StateT.run_bind]
          refine PubLaSafe.bind (hvRecv es.g P (es.g.st P) c' none es hlf)
            fun ⟨res, es₁⟩ hlf₁ => ?_
          rcases res with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
            exact PubLaSafe.pure hlf₁
          · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
          · dsimp only
            split
            · simp only [StateT.run_pure]; exact PubLaSafe.pure hlf₁
            · split
              · rw [StateT.run_bind]
                refine PubLaSafe.bind (hcommit es.g P (es.g.st P) st' ⟨P.other, t', i'⟩ es₁ hlf₁)
                  fun ⟨s1?, _⟩ hlf₂ => ?_
                cases s1? <;>
                  simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
                  exact PubLaSafe.pure hlf₂
              · split <;>
                  simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure] <;>
                  exact PubLaSafe.pure hlf₁

private theorem implEDFPaperBucket_step_lfWin_la
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (L N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q_in : _)
    (st : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) ×
      Option ℕ)
    (hlf : st.1.h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.1.h.lfWin = false)
      ((implEDFPaperBucket
        (hooksFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true)
        (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par) q_in).run st) := by
  rcases st with ⟨es, winEp⟩
  unfold implEDFPaperBucket withWinEpDF
  simp only [StateT.run_mk]
  refine PubLaSafe.bind
    (implEDFPaperBucketRaw_step_lfWin_la C ℓ Dh encPt encT idOf L N Δcka Δbucket qep tL par _
      rfl rfl rfl rfl
      (fun hs h => (hooksFSMultiDFBucketPaper_nonRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
        Δbucket qep tL par hs h).2.1)
      (fun hs h => (hooksFSMultiDFBucketPaper_nonRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
        Δbucket qep tL par hs h).2.2.2)
      q_in es hlf) ?_
  rintro ⟨_, _⟩ hlf'
  exact PubLaSafe.pure hlf'

private theorem implEDFPaperBucketMode_step_lfWin_la
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (L N Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (q_in : _)
    (st : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) ×
      Option ℕ)
    (hlf : st.1.h.lfWin = false) :
    PubLaSafe C ℓ encT idOf N (fun p => p.2.1.h.lfWin = false)
      ((implEDFPaperBucketMode
        (hooksFSMultiDFBucketPaperMode L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep gMain tL par true)
        (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par)
        gMain isHonestHdrFSMultiDFBucket q_in).run st) := by
  rcases st with ⟨es, winEp⟩
  have hraw := implEDFPaperBucketRaw_step_lfWin_la C ℓ Dh encPt encT idOf L N Δcka Δbucket qep tL par
    (hooksFSMultiDFBucketPaperMode L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep gMain tL par true)
    rfl rfl rfl rfl
    (fun hs h ctx P t0 γ0 σ0 tn0 => by
      dsimp only [hooksFSMultiDFBucketPaperMode]
      cases gMain with
      | false =>
        exact (hooksFSMultiDFBucketPaper_nonRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
          Δbucket qep tL par hs h).2.1 ctx P t0 γ0 σ0 tn0
      | true =>
        simp only [↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
        cases hs.cache t0 with
        | none =>
          split_ifs <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure h)
        | some quad =>
          rcases quad with ⟨Tc, σc, kVal, optIdx⟩
          by_cases hT : Tc = tn0
          · subst hT
            cases optIdx <;> (simp only [↓reduceIte, StateT.run_pure]; exact PubLaSafe.pure h)
          · simp only [hT, ↓reduceIte]
            split_ifs <;> (simp only [StateT.run_pure]; exact PubLaSafe.pure h))
    (fun hs h ctx P vp => by
      dsimp only [hooksFSMultiDFBucketPaperMode]
      cases gMain with
      | true =>
        exact (hooksFSMultiDFBucketPaper_nonRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
          Δbucket qep tL par hs h).2.2.2 ctx P vp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        split_ifs
        · simp only [StateT.run_pure]; exact PubLaSafe.pure h
        · exact (hooksFSMultiDFBucketPaper_nonRecv_lfWin_la C ℓ Dh encPt encT idOf L N Δcka
            Δbucket qep tL par hs h).2.2.2 ctx P vp)
    q_in es hlf
  unfold implEDFPaperBucketMode withWinEpDFMode
  cases gMain with
  | true =>
    simp only [↓reduceIte, withWinEpDF, StateT.run_mk]
    refine PubLaSafe.bind hraw ?_
    rintro ⟨_, _⟩ hlf'
    exact PubLaSafe.pure hlf'
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk]
    refine PubLaSafe.bind hraw ?_
    rintro ⟨_, _⟩ hlf'
    exact PubLaSafe.pure hlf'

theorem redFSAuthDFPaperMultiBucket_la_true_zero
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (L N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    ∀ w ∈ support (runPubIdeal C ℓ encT idOf N true
      (redFSAuthDFPaperMultiBucket L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep true tL par A)
      (fun _ => false) (fun _ => none)),
      w.1.1 = false := by
  have hinit : PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      ((initFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δbucket qep tL par).run {}) := by
    unfold initFSMultiDFBucketPaper
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun kr _ => ?_
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun kc _ => ?_
    refine PubLaSafe.bind
      (rootFSMultiDFBucketPaper_lfWin_la C ℓ encPt encT idOf N Δbucket qep tL par 0 false lam
        ((CryptoGames.Ratchet.rootPRNG C.F encPt).init kr) {} rfl)
      fun ⟨⟨σ, kVal, sid⟩, h₁⟩ hlf₁ => ?_
    simp only [StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure]
    cases sid with
    | none => exact PubLaSafe.pure hlf₁
    | some ik =>
      dsimp only [regSessOptMultiDFBucket, regSessMultiDFBucket]
      split_ifs <;> exact PubLaSafe.pure hlf₁
  have hsim : ∀ (m : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (st : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
          (RatchetSenderState (BitVec 256) ⊕ ℕ)
          (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
          (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
          (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) ×
        Option ℕ)
      (hlf : st.1.h.lfWin = false),
      PubLaSafe C ℓ encT idOf N (fun p => p.2.1.h.lfWin = false)
        ((simulateQ (implEDFPaperBucket
          (hooksFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par true)
          (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par)) m).run st) := by
    intro m
    induction m using OracleComp.inductionOn with
    | pure a =>
      intro st hlf
      simp only [simulateQ_pure, StateT.run_pure]
      exact PubLaSafe.pure hlf
    | query_bind q k ih =>
      intro st hlf
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      refine PubLaSafe.bind
        (implEDFPaperBucket_step_lfWin_la C ℓ Dh encPt encT idOf L N Δcka Δbucket qep tL par q st hlf) ?_
      rintro ⟨a, st'⟩ hlf'
      exact ih a st' hlf'
  have hfull : PubLaSafe C ℓ encT idOf N (fun b => b = false)
      (redFSAuthDFPaperMultiBucket L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep true tL par A) := by
    unfold redFSAuthDFPaperMultiBucket
    dsimp only [CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketGen]
    unfold engRunDFPaperBucket
    have hms : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
    rw [hms, bind_assoc]
    refine PubLaSafe.bind hinit fun ⟨vs, h₁⟩ hlf₁ => ?_
    cases vs with
    | none => simp only [pure_bind]; exact PubLaSafe.pure rfl
    | some vAB =>
      rcases vAB with ⟨vA, vB⟩
      simp only [bind_assoc, pure_bind]
      refine PubLaSafe.bind
        (hsim A ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₁ }, none) hlf₁) ?_
      rintro ⟨_, st'⟩ hlf'
      simp only [↓reduceIte]
      exact PubLaSafe.pure hlf'
  intro w hw
  exact (hfull (fun _ => false) (fun _ => none) (fun _ _ h => by simp at h) w hw).1

/-! ## 2. `CoinOnly` Combinators & `q = 0` Zero-Output Theorem (`la = false`) -/

theorem runPubIdeal_bind_support_false {α β : Type}
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {N : ℕ}
    (x : OracleComp (PubMultiSpec Pt ℓ) α)
    (f : α → OracleComp (PubMultiSpec Pt ℓ) β)
    (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
    {w : (β × (ℕ → Bool)) × (ℕ → Option (IdealHSt Pt ℓ))}
    (hw : w ∈ support (runPubIdeal C ℓ encT idOf N false (x >>= f) rc σ)) :
    ∃ z ∈ support (runPubIdeal C ℓ encT idOf N false x rc σ),
      w ∈ support (runPubIdeal C ℓ encT idOf N false (f z.1.1) z.1.2 z.2) := by
  simpa only [runPubIdeal, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] using hw

@[expose] def CoinOnly {α : Type} (P : α → Prop)
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (x : OracleComp (PubMultiSpec Pt ℓ) α) : Prop :=
  ∀ rc σ, ∀ z ∈ support (runPubIdeal C ℓ encT idOf N false x rc σ),
    P z.1.1 ∧ z.1.2 = rc ∧ z.2 = σ

theorem CoinOnly.pure {α : Type} {P : α → Prop} {a : α} (ha : P a)
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ} :
    CoinOnly P C ℓ encT idOf N (Pure.pure a) := by
  intro rc σ z hz
  simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz; exact ⟨ha, rfl, rfl⟩

theorem CoinOnly.bind {α β : Type} {P : α → Prop} {Q : β → Prop}
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {N : ℕ}
    {x : OracleComp (PubMultiSpec Pt ℓ) α} {f : α → OracleComp (PubMultiSpec Pt ℓ) β}
    (hx : CoinOnly P C ℓ encT idOf N x) (hf : ∀ a, P a → CoinOnly Q C ℓ encT idOf N (f a)) :
    CoinOnly Q C ℓ encT idOf N (x >>= f) := by
  intro rc σ z hz
  rcases runPubIdeal_bind_support_false x f rc σ hz with ⟨w, hw, hzw⟩
  rcases hx rc σ w hw with ⟨hp, hrc, hσ⟩
  rcases hf w.1.1 hp w.1.2 w.2 z hzw with ⟨hq, hrc', hσ'⟩
  exact ⟨hq, hrc'.trans hrc, hσ'.trans hσ⟩

private theorem CoinOnly.of_isQueryBoundP_zero {α : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (x : OracleComp (PubMultiSpec Pt ℓ) α)
    (h0 : x.IsQueryBoundP (fun t => t.isRight) 0) :
    CoinOnly (fun _ : α => True) C ℓ encT idOf N x := by
  induction x using OracleComp.inductionOn with
  | pure a => exact CoinOnly.pure trivial
  | query_bind t r ih =>
    intro rc σ z hz
    rw [isQueryBoundP_query_bind_iff] at h0
    rcases t with n | ⟨s₀, q⟩
    · simp only [runPubIdeal, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, pubMultiImpl, StateT.run_bind, stateT_lift_run,
        simulateQ_HasQuery_query, idealSessImpl, sessLift_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨u, _, hzu⟩
      exact ih u (h0.2 u) rc σ z hzu
    · simp at h0

private theorem isQueryBoundP_zero_liftProbComp {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp (unifSpec + spec₀) α) (fun t => t.isRight) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := unifSpec + spec₀) (.inl t)) >>= fun u =>
        (liftM (k u) : OracleComp (unifSpec + spec₀) α))
      (fun x => x.isRight) 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨by simp, fun u => ih u⟩

theorem CoinOnly.sampleT {T₀ : Type} [SampleableType T₀]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ) :
    CoinOnly (fun _ : T₀ => True) C ℓ encT idOf N
      (CryptoGames.SM.Construction.sampleT T₀) :=
  CoinOnly.of_isQueryBoundP_zero C ℓ encT idOf N _ (isQueryBoundP_zero_liftProbComp ($ᵗ T₀ : ProbComp T₀))

theorem redFSAuthDFPaperMultiBucket_la_false_q_zero
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (L N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq0 : MakesAtMostQueriesDF A 0) :
    ∀ w ∈ support (runPubIdeal C ℓ encT idOf N false
      (redFSAuthDFPaperMultiBucket L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep false tL par A)
      (fun _ => false) (fun _ => none)),
      w.1.1 = false := by
  have hq0' : A.IsQueryBoundP (fun x => x.isRight = true) 0 := by
    unfold MakesAtMostQueriesDF at hq0
    convert hq0 using 1; funext x; rcases x with _ | _ <;> rfl
  have hsim0 : ∀ {α : Type}
      (oa : OracleComp (unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF
        (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) α)
      (h0 : oa.IsQueryBoundP (fun x => x.isRight = true) 0)
      (es : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
      (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
      (z : _),
      z ∈ support (runPubIdeal C ℓ encT idOf N false
        ((simulateQ (implEDFPaperBucket
          (hooksFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false)
          (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par)) oa).run (es, none))
        rc σ) →
      z.1.1.2.2 = none := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro _ es rc σ z hz
      simp only [simulateQ_pure, StateT.run_pure, runPubIdeal, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; rfl
    | query_bind t r ih =>
      intro h0 es rc σ z hz
      rw [isQueryBoundP_query_bind_iff] at h0
      rcases t with n | qdf
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind] at hz
        rcases runPubIdeal_bind_support_false _ _ rc σ hz with ⟨u, hu, hzu⟩
        simp only [implEDFPaperBucket, withWinEpDF, StateT.run_mk] at hu
        change u ∈ support (runPubIdeal C ℓ encT idOf N false
          ((coinsE n).run es >>= _) rc σ) at hu
        unfold coinsE at hu
        rw [StateT.run_lift, bind_assoc] at hu
        simp only [pure_bind] at hu
        rcases runPubIdeal_bind_support_false _ _ rc σ hu with ⟨v, _, huv⟩
        have hnw : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
        simp only [hnw, Bool.false_eq_true, ↓reduceIte, runPubIdeal, simulateQ_pure,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at huv
        subst huv
        exact ih v.1.1 (h0.2 v.1.1) es v.1.2 v.2 z hzu
      · simp at h0
  intro w hw
  unfold redFSAuthDFPaperMultiBucket at hw
  dsimp only [CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketGen] at hw
  unfold engRunDFPaperBucket at hw
  have hms : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hms, bind_assoc] at hw
  rcases runPubIdeal_bind_support_false _ _ (fun _ => false) (fun _ => none) hw with ⟨z₀, _, hw₁⟩
  rcases z₀ with ⟨⟨⟨vs, h₀⟩, rc₀⟩, σ₀⟩
  cases vs with
  | none =>
    simp only [pure_bind, runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hw₁
    subst hw₁; rfl
  | some vAB =>
    rcases vAB with ⟨vA, vB⟩
    simp only [bind_assoc, pure_bind] at hw₁
    rcases runPubIdeal_bind_support_false _ _ rc₀ σ₀ hw₁ with ⟨z₁, hz₁, hw₂⟩
    have hnone := hsim0 A hq0'
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₀ }
      rc₀ σ₀ z₁ hz₁
    simp only [authOutBucket, hnone, Bool.false_eq_true, ↓reduceIte, runPubIdeal, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw₂
    subst hw₂; rfl

theorem redFSAuthDFPaperMultiBucketMode_la_true_zero
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (L N Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    ∀ w ∈ support (runPubIdeal C ℓ encT idOf N true
      (redFSAuthDFPaperMultiBucketMode L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep gMain true tL par A)
      (fun _ => false) (fun _ => none)),
      w.1.1 = false := by
  have hinit : PubLaSafe C ℓ encT idOf N (fun p => p.2.lfWin = false)
      ((initFSMultiDFBucketPaper L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δbucket qep tL par).run {}) := by
    unfold initFSMultiDFBucketPaper
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun kr _ => ?_
    refine PubLaSafe.bind (PubLaSafe.any C ℓ encT idOf N _) fun kc _ => ?_
    refine PubLaSafe.bind
      (rootFSMultiDFBucketPaper_lfWin_la C ℓ encPt encT idOf N Δbucket qep tL par 0 false lam
        ((CryptoGames.Ratchet.rootPRNG C.F encPt).init kr) {} rfl)
      fun ⟨⟨σ, kVal, sid⟩, h₁⟩ hlf₁ => ?_
    simp only [StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure]
    cases sid with
    | none => exact PubLaSafe.pure hlf₁
    | some ik =>
      dsimp only [regSessOptMultiDFBucket, regSessMultiDFBucket]
      split_ifs <;> exact PubLaSafe.pure hlf₁
  have hsim : ∀ (m : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (st : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
          (RatchetSenderState (BitVec 256) ⊕ ℕ)
          (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
          (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
          (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) ×
        Option ℕ)
      (hlf : st.1.h.lfWin = false),
      PubLaSafe C ℓ encT idOf N (fun p => p.2.1.h.lfWin = false)
        ((simulateQ (implEDFPaperBucketMode
          (hooksFSMultiDFBucketPaperMode L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep gMain tL par true)
          (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par)
          gMain isHonestHdrFSMultiDFBucket) m).run st) := by
    intro m
    induction m using OracleComp.inductionOn with
    | pure a =>
      intro st hlf
      simp only [simulateQ_pure, StateT.run_pure]
      exact PubLaSafe.pure hlf
    | query_bind q k ih =>
      intro st hlf
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      refine PubLaSafe.bind
        (implEDFPaperBucketMode_step_lfWin_la C ℓ Dh encPt encT idOf L N Δcka Δbucket qep
          gMain tL par q st hlf) ?_
      rintro ⟨a, st'⟩ hlf'
      exact ih a st' hlf'
  have hfull : PubLaSafe C ℓ encT idOf N (fun b => b = false)
      (redFSAuthDFPaperMultiBucketMode L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep gMain true tL par A) := by
    unfold redFSAuthDFPaperMultiBucketMode
    dsimp only [CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeGen]
    unfold engRunDFPaperBucketMode
    have hms : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
    rw [hms, bind_assoc]
    refine PubLaSafe.bind hinit fun ⟨vs, h₁⟩ hlf₁ => ?_
    cases vs with
    | none => simp only [pure_bind]; exact PubLaSafe.pure rfl
    | some vAB =>
      rcases vAB with ⟨vA, vB⟩
      simp only [bind_assoc, pure_bind]
      refine PubLaSafe.bind
        (hsim A ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₁ }, none) hlf₁) ?_
      rintro ⟨_, st'⟩ hlf'
      simp only [↓reduceIte]
      exact PubLaSafe.pure hlf'
  intro w hw
  exact (hfull (fun _ => false) (fun _ => none) (fun _ _ h => by simp at h) w hw).1

theorem redFSAuthDFPaperMultiBucketMode_la_false_q_zero
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (L N Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq0 : MakesAtMostQueriesDF A 0) :
    ∀ w ∈ support (runPubIdeal C ℓ encT idOf N false
      (redFSAuthDFPaperMultiBucketMode L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep gMain false tL par A)
      (fun _ => false) (fun _ => none)),
      w.1.1 = false := by
  have hq0' : A.IsQueryBoundP (fun x => x.isRight = true) 0 := by
    unfold MakesAtMostQueriesDF at hq0
    convert hq0 using 1; funext x; rcases x with _ | _ <;> rfl
  have hsim0 : ∀ {α : Type}
      (oa : OracleComp (unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF
        (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) α)
      (h0 : oa.IsQueryBoundP (fun x => x.isRight = true) 0)
      (es : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
        (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
        (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
      (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
      (z : _),
      z ∈ support (runPubIdeal C ℓ encT idOf N false
        ((simulateQ (implEDFPaperBucketMode
          (hooksFSMultiDFBucketPaperMode L (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep gMain tL par false)
          (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par)
          gMain isHonestHdrFSMultiDFBucket) oa).run (es, none))
        rc σ) →
      z.1.1.2.2 = none := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro _ es rc σ z hz
      simp only [simulateQ_pure, StateT.run_pure, runPubIdeal, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; rfl
    | query_bind t r ih =>
      intro h0 es rc σ z hz
      rw [isQueryBoundP_query_bind_iff] at h0
      rcases t with n | qdf
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind] at hz
        rcases runPubIdeal_bind_support_false _ _ rc σ hz with ⟨u, hu, hzu⟩
        have hnw : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
        cases gMain with
        | true =>
          simp only [implEDFPaperBucketMode, withWinEpDFMode, ↓reduceIte, withWinEpDF,
            StateT.run_mk] at hu
          change u ∈ support (runPubIdeal C ℓ encT idOf N false
            ((coinsE n).run es >>= _) rc σ) at hu
          unfold coinsE at hu
          rw [StateT.run_lift, bind_assoc] at hu
          simp only [pure_bind] at hu
          rcases runPubIdeal_bind_support_false _ _ rc σ hu with ⟨v, _, huv⟩
          simp only [hnw, Bool.false_eq_true, ↓reduceIte, runPubIdeal, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at huv
          subst huv
          exact ih v.1.1 (h0.2 v.1.1) es v.1.2 v.2 z hzu
        | false =>
          simp only [implEDFPaperBucketMode, withWinEpDFMode, Bool.false_eq_true, ↓reduceIte,
            StateT.run_mk] at hu
          change u ∈ support (runPubIdeal C ℓ encT idOf N false
            ((coinsE n).run es >>= _) rc σ) at hu
          unfold coinsE at hu
          rw [StateT.run_lift, bind_assoc] at hu
          simp only [pure_bind] at hu
          rcases runPubIdeal_bind_support_false _ _ rc σ hu with ⟨v, _, huv⟩
          simp only [hnw, Bool.false_eq_true, ↓reduceIte, runPubIdeal, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at huv
          subst huv
          exact ih v.1.1 (h0.2 v.1.1) es v.1.2 v.2 z hzu
      · simp at h0
  intro w hw
  unfold redFSAuthDFPaperMultiBucketMode at hw
  dsimp only [CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeGen] at hw
  unfold engRunDFPaperBucketMode at hw
  have hms : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hms, bind_assoc] at hw
  rcases runPubIdeal_bind_support_false _ _ (fun _ => false) (fun _ => none) hw with ⟨z₀, _, hw₁⟩
  rcases z₀ with ⟨⟨⟨vs, h₀⟩, rc₀⟩, σ₀⟩
  cases vs with
  | none =>
    simp only [pure_bind, runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hw₁
    subst hw₁; rfl
  | some vAB =>
    rcases vAB with ⟨vA, vB⟩
    simp only [bind_assoc, pure_bind] at hw₁
    rcases runPubIdeal_bind_support_false _ _ rc₀ σ₀ hw₁ with ⟨z₁, hz₁, hw₂⟩
    have hnone := hsim0 A hq0'
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₀ }
      rc₀ σ₀ z₁ hz₁
    simp only [authOutBucket, hnone, Bool.false_eq_true, ↓reduceIte, runPubIdeal, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw₂
    subst hw₂; rfl

end Helpers

end

end Computational.Proofs.E2E.SessionAuthMultiEndBucketLa

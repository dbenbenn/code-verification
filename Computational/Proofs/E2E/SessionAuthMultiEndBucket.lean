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
import Computational.Proofs.E2E.SessionAuthMultiPot
import Computational.Proofs.E2E.SessionAuthWireEnd
import Computational.Proofs.E2E.SessionAuthPubToAD
public import Computational.Proofs.E2E.SessionAuthMultiEndBase -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthMultiEndBucketPot
import Computational.Proofs.E2E.SessionAuthMultiEndBucketLa
import Computational.Proofs.E2E.SessionAuthMultiEndBucketSteps
import Computational.Proofs.E2E.SessionAuthMultiEndBucketStep

/-!
# Multi-Session Ideal-Cutoff (`multiSessEndWinProb = 0`) Proofs for `DeliverForgePaperMultiBucket`

Proves that at the ideal FS-AEAD hopping endpoint (`Thm5.hp cut cut la`, with
`cut = authHopCutoff maxForwardJumps qR la` and `2 * q ≤ qR`), both `(tL, par)`-bucket Stage-2
`DeliverForgePaper` FS-AEAD reductions output `true` with probability `0` when `2 ≤ Δbucket`:
1. `multiSessEndWinProb_redFSAuthDFPaperMultiBucket_eq_zero`
2. `multiSessEndWinProb_redFSAuthDFPaperMultiBucketMode_eq_zero` (`∀ gMain la : Bool`)-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiEnd

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.SM.Construction (
  Header hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode
  initFSMultiDFBucketPaper isHonestHdrFSMultiDFBucket bucketAuthCfgGen
  redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketMode)
open _root_.CryptoGames.SM.Construction.DeliverForge (
  AdversaryDF MakesAtMostQueriesDF implEDFPaperBucket implEDFPaperBucketMode
  engRunDFPaperBucket engRunDFPaperBucketMode authOutBucket)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff multiSessPubToAD)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessEndWinProb)
open Computational.Proofs.E2E.SessionAuthMultiPot (
  redFSAuthDFPaperMultiBucket_sess_isQueryBoundP
  redFSAuthDFPaperMultiBucket_sess_isQueryBoundP_min)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketPot (
  redFSAuthDFPaperMultiBucketMode_sess_isQueryBoundP
  redFSAuthDFPaperMultiBucketMode_sess_isQueryBoundP_min)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketLa (
  runPubIdeal_bind_support_false
  redFSAuthDFPaperMultiBucket_la_true_zero
  redFSAuthDFPaperMultiBucket_la_false_q_zero
  redFSAuthDFPaperMultiBucketMode_la_true_zero
  redFSAuthDFPaperMultiBucketMode_la_false_q_zero)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketSteps (
  BucketEState BucketInv authOutBucket_eq_false_of_bucketInv initFSMultiDFBucketPaper_bucketInv)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketStep (
  implEDFPaperBucketMode_coins_bucketInv
  implEDFPaperBucketMode_inr_bucketInv
  implEDFPaperBucket_step_bucketInv)


section MultiSessEndZero

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)

private theorem simulateQ_bucketInv {α : Type}
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (impl : QueryImpl (unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (StateT (BucketEState Pt ℓ × Option ℕ) (OracleComp (PubMultiSpec Pt ℓ))))
    (hInl : ∀ rem n st rc σ w,
      BucketInv q Δcka Δbucket qep tL par rem st σ →
      w ∈ support (runPubIdeal C ℓ encT idOf N false ((impl (.inl n)).run st) rc σ) →
      BucketInv q Δcka Δbucket qep tL par rem w.1.1.2 w.2)
    (hInr : ∀ rem' qdf st rc σ w,
      BucketInv q Δcka Δbucket qep tL par (rem' + 1) st σ →
      w ∈ support (runPubIdeal C ℓ encT idOf N false ((impl (.inr qdf)).run st) rc σ) →
      BucketInv q Δcka Δbucket qep tL par rem' w.1.1.2 w.2)
    (oa : OracleComp (unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) α) :
    ∀ (rem : ℕ) (_hq : oa.IsQueryBoundP (fun x => x.isRight = true) rem)
      (st : BucketEState Pt ℓ × Option ℕ) (rc : ℕ → Bool) (σ : ℕ → Option (IdealHSt Pt ℓ))
      (_hinv : BucketInv q Δcka Δbucket qep tL par rem st σ)
      (z : _),
      z ∈ support (runPubIdeal C ℓ encT idOf N false ((simulateQ impl oa).run st) rc σ) →
      ∃ rem_out, BucketInv q Δcka Δbucket qep tL par rem_out z.1.1.2 z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro rem _ st rc σ hinv z hz
    simp only [simulateQ_pure, StateT.run_pure, runPubIdeal, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rem, hinv⟩
  | query_bind t r ih =>
    intro rem hq st rc σ hinv z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind] at hz
    rw [isQueryBoundP_query_bind_iff] at hq
    rcases runPubIdeal_bind_support_false _ _ rc σ hz with ⟨w, hw, hzw⟩
    rcases t with n | qdf
    · have hq_next : (r w.1.1.1).IsQueryBoundP (fun x => x.isRight = true) rem := by
        simpa using hq.2 w.1.1.1
      exact ih w.1.1.1 rem hq_next w.1.1.2 w.1.2 w.2 (hInl rem n st rc σ w hinv hw) z hzw
    · rcases rem with _ | rem'
      · simp at hq
      · have hq_next : (r w.1.1.1).IsQueryBoundP (fun x => x.isRight = true) rem' := by
          simpa using hq.2 w.1.1.1
        exact ih w.1.1.1 rem' hq_next w.1.1.2 w.1.2 w.2
          (hInr rem' qdf st rc σ w hinv hw) z hzw

private theorem redFSAuthDFPaperMultiBucket_la_false_pos_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q N Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hq_pos : 1 ≤ q) (hΔb : 2 ≤ Δbucket)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) :
    ∀ w ∈ support (runPubIdeal C ℓ encT idOf N false
      (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep false tL par A)
      (fun _ => false) (fun _ => none)),
      w.1.1 = false := by
  have hq' : A.IsQueryBoundP (fun x => x.isRight = true) q := by
    unfold MakesAtMostQueriesDF at hq
    convert hq using 1; funext x; rcases x with _ | _ <;> rfl
  intro w hw
  unfold redFSAuthDFPaperMultiBucket at hw
  dsimp only [CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketGen] at hw
  unfold engRunDFPaperBucket at hw
  have hms : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hms, bind_assoc] at hw
  rcases runPubIdeal_bind_support_false _ _ (fun _ => false) (fun _ => none) hw with ⟨z₀, hz₀, hw₁⟩
  rcases initFSMultiDFBucketPaper_bucketInv C ℓ Dh encPt encT idOf lam q N Δcka Δbucket qep tL par
    hq_pos hΔb (fun _ => false) (fun _ => none) z₀ hz₀ with ⟨hinit_inv, _, hz₀_σ⟩
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
    have hinv₀ : BucketInv q Δcka Δbucket qep tL par q
        ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₀ }, none)
        σ₀ := by
      dsimp only at hz₀_σ
      rw [hz₀_σ]
      exact hinit_inv vA vB rfl
    rcases simulateQ_bucketInv ℓ Pt C encT idOf q N Δcka Δbucket qep tL par
      (implEDFPaperBucket
        (hooksFSMultiDFBucketPaper (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep tL par false)
        (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par))
      (fun rem n st rc σ u hinv hu =>
        (implEDFPaperBucket_step_bucketInv C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
          hq_pos hΔb (.inl n) rem st rc σ u hu).1 n rfl hinv)
      (fun rem' qdf st rc σ u hinv hu =>
        (implEDFPaperBucket_step_bucketInv C ℓ Dh encPt encT idOf q N Δcka Δbucket qep tL par
          hq_pos hΔb (.inr qdf) (rem' + 1) st rc σ u hu).2 qdf rem' rfl rfl hinv)
      A q hq' _ rc₀ σ₀ hinv₀ z₁ hz₁ with ⟨rem_out, hinv_out⟩
    simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hw₂
    subst hw₂
    exact authOutBucket_eq_false_of_bucketInv hinv_out

private theorem redFSAuthDFPaperMultiBucketMode_la_false_pos_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q N Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (hq_pos : 1 ≤ q) (hΔb : 2 ≤ Δbucket)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) :
    ∀ w ∈ support (runPubIdeal C ℓ encT idOf N false
      (redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep gMain false tL par A)
      (fun _ => false) (fun _ => none)),
      w.1.1 = false := by
  have hq' : A.IsQueryBoundP (fun x => x.isRight = true) q := by
    unfold MakesAtMostQueriesDF at hq
    convert hq using 1; funext x; rcases x with _ | _ <;> rfl
  intro w hw
  unfold redFSAuthDFPaperMultiBucketMode at hw
  dsimp only [CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeGen] at hw
  unfold engRunDFPaperBucketMode at hw
  have hms : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hms, bind_assoc] at hw
  rcases runPubIdeal_bind_support_false _ _ (fun _ => false) (fun _ => none) hw with ⟨z₀, hz₀, hw₁⟩
  rcases initFSMultiDFBucketPaper_bucketInv C ℓ Dh encPt encT idOf lam q N Δcka Δbucket qep tL par
    hq_pos hΔb (fun _ => false) (fun _ => none) z₀ hz₀ with ⟨hinit_inv, _, hz₀_σ⟩
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
    have hinv₀ : BucketInv q Δcka Δbucket qep tL par q
        ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₀ }, none)
        σ₀ := by
      dsimp only at hz₀_σ
      rw [hz₀_σ]
      exact hinit_inv vA vB rfl
    rcases simulateQ_bucketInv ℓ Pt C encT idOf q N Δcka Δbucket qep tL par
      (implEDFPaperBucketMode
        (hooksFSMultiDFBucketPaperMode (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka Δbucket qep gMain tL par false)
        (2 + Δcka) qep maxForwardJumps (bucketAuthCfgGen Δbucket tL par)
        gMain isHonestHdrFSMultiDFBucket)
      (fun rem n st rc σ u hinv hu =>
        implEDFPaperBucketMode_coins_bucketInv C ℓ Dh encPt encT idOf q N Δcka Δbucket qep
          gMain tL par rem n st rc σ hinv u hu)
      (fun rem' qdf st rc σ u hinv hu =>
        implEDFPaperBucketMode_inr_bucketInv C ℓ Dh encPt encT idOf q N Δcka Δbucket qep
          gMain tL par hq_pos hΔb rem' qdf st rc σ hinv u hu)
      A q hq' _ rc₀ σ₀ hinv₀ z₁ hz₁ with ⟨rem_out, hinv_out⟩
    simp only [runPubIdeal, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hw₂
    subst hw₂
    exact authOutBucket_eq_false_of_bucketInv hinv_out


/-- Ideal-cutoff (`hp cut cut la`) zero-output theorem for `redFSAuthDFPaperMultiBucket`
when `2 ≤ Δbucket`. -/
theorem multiSessEndWinProb_redFSAuthDFPaperMultiBucket_eq_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (hΔb : 2 ≤ Δbucket)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : 2 * q ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la' tL par A))
      la = 0 := by
  refine multiSessEndWinProb_eq_zero_of_hpIdeal C ℓ encT idOf q qR
    (fun la' =>
      redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la' tL par A)
    la (fun la' s => ?_) hqR ?_
  · convert redFSAuthDFPaperMultiBucket_sess_isQueryBoundP (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka Δbucket qep tL par la' A hq s using 1
    funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  · refine multiSessPubToAD_support_of_runPubIdeal C ℓ encT idOf
      (authHopCutoff maxForwardJumps qR la) la _ ?_
    cases la with
    | true =>
      exact redFSAuthDFPaperMultiBucket_la_true_zero C ℓ Dh encPt encT idOf lam (q + 1)
        (authHopCutoff maxForwardJumps qR true) Δcka Δbucket qep tL par A
    | false =>
      rcases Nat.eq_zero_or_pos q with rfl | hq_pos
      · exact redFSAuthDFPaperMultiBucket_la_false_q_zero C ℓ Dh encPt encT idOf lam 1
          (authHopCutoff maxForwardJumps qR false) Δcka Δbucket qep tL par A hq
      · exact redFSAuthDFPaperMultiBucket_la_false_pos_zero ℓ Pt C Dh encPt encT idOf lam q
          (authHopCutoff maxForwardJumps qR false) Δcka Δbucket qep tL par hq_pos hΔb A hq

/-- Ideal-cutoff (`hp cut cut la`) zero-output theorem for `redFSAuthDFPaperMultiBucketMode`
(`gMain : Bool`, `2 ≤ Δbucket`). -/
theorem multiSessEndWinProb_redFSAuthDFPaperMultiBucketMode_eq_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (hΔb : 2 ≤ Δbucket)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : 2 * q ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh)
            (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep
            gMain la' tL par A))
      la = 0 := by
  refine multiSessEndWinProb_eq_zero_of_hpIdeal C ℓ encT idOf q qR
    (fun la' =>
      redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh)
        (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep
        gMain la' tL par A)
    la (fun la' s => ?_) hqR ?_
  · convert redFSAuthDFPaperMultiBucketMode_sess_isQueryBoundP (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka Δbucket qep
      gMain tL par la' A hq s using 1
    funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  · refine multiSessPubToAD_support_of_runPubIdeal C ℓ encT idOf
      (authHopCutoff maxForwardJumps qR la) la _ ?_
    cases la with
    | true =>
      exact redFSAuthDFPaperMultiBucketMode_la_true_zero C ℓ Dh encPt encT idOf lam (q + 1)
        (authHopCutoff maxForwardJumps qR true) Δcka Δbucket qep gMain tL par A
    | false =>
      rcases Nat.eq_zero_or_pos q with rfl | hq_pos
      · exact redFSAuthDFPaperMultiBucketMode_la_false_q_zero C ℓ Dh encPt encT idOf lam 1
          (authHopCutoff maxForwardJumps qR false) Δcka Δbucket qep gMain tL par A hq
      · exact redFSAuthDFPaperMultiBucketMode_la_false_pos_zero ℓ Pt C Dh encPt encT idOf lam q
          (authHopCutoff maxForwardJumps qR false) Δcka Δbucket qep gMain tL par hq_pos hΔb A hq

/-- Ideal-cutoff (`hp cut cut la`, `min (2 * q) (q + 2) ≤ qR`) zero-output theorem for
`redFSAuthDFPaperMultiBucket` when `2 ≤ Δbucket`. -/
theorem multiSessEndWinProb_redFSAuthDFPaperMultiBucket_eq_zero_min
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (hΔb : 2 ≤ Δbucket)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : min (2 * q) (q + 2) ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la' tL par A))
      la = 0 := by
  refine multiSessEndWinProb_eq_zero_of_hpIdeal_gen C ℓ encT idOf (min (2 * q) (q + 2)) qR
    (fun la' =>
      redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la' tL par A)
    la (fun la' s => ?_) hqR ?_
  · convert redFSAuthDFPaperMultiBucket_sess_isQueryBoundP_min (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka Δbucket qep tL par la' A hq s using 1
    funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  · refine multiSessPubToAD_support_of_runPubIdeal C ℓ encT idOf
      (authHopCutoff maxForwardJumps qR la) la _ ?_
    cases la with
    | true =>
      exact redFSAuthDFPaperMultiBucket_la_true_zero C ℓ Dh encPt encT idOf lam (q + 1)
        (authHopCutoff maxForwardJumps qR true) Δcka Δbucket qep tL par A
    | false =>
      rcases Nat.eq_zero_or_pos q with rfl | hq_pos
      · exact redFSAuthDFPaperMultiBucket_la_false_q_zero C ℓ Dh encPt encT idOf lam 1
          (authHopCutoff maxForwardJumps qR false) Δcka Δbucket qep tL par A hq
      · exact redFSAuthDFPaperMultiBucket_la_false_pos_zero ℓ Pt C Dh encPt encT idOf lam q
          (authHopCutoff maxForwardJumps qR false) Δcka Δbucket qep tL par hq_pos hΔb A hq

/-- Ideal-cutoff (`hp cut cut la`, `min (2 * q) (q + 2) ≤ qR`) zero-output theorem for
`redFSAuthDFPaperMultiBucketMode` (`gMain : Bool`, `2 ≤ Δbucket`). -/
theorem multiSessEndWinProb_redFSAuthDFPaperMultiBucketMode_eq_zero_min
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool)
    (hΔb : 2 ≤ Δbucket)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : min (2 * q) (q + 2) ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh)
            (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep
            gMain la' tL par A))
      la = 0 := by
  refine multiSessEndWinProb_eq_zero_of_hpIdeal_gen C ℓ encT idOf (min (2 * q) (q + 2)) qR
    (fun la' =>
      redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh)
        (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep
        gMain la' tL par A)
    la (fun la' s => ?_) hqR ?_
  · convert redFSAuthDFPaperMultiBucketMode_sess_isQueryBoundP_min (q + 1) (dhScheme Dh)
      (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka Δbucket qep
      gMain tL par la' A hq s using 1
    funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  · refine multiSessPubToAD_support_of_runPubIdeal C ℓ encT idOf
      (authHopCutoff maxForwardJumps qR la) la _ ?_
    cases la with
    | true =>
      exact redFSAuthDFPaperMultiBucketMode_la_true_zero C ℓ Dh encPt encT idOf lam (q + 1)
        (authHopCutoff maxForwardJumps qR true) Δcka Δbucket qep gMain tL par A
    | false =>
      rcases Nat.eq_zero_or_pos q with rfl | hq_pos
      · exact redFSAuthDFPaperMultiBucketMode_la_false_q_zero C ℓ Dh encPt encT idOf lam 1
          (authHopCutoff maxForwardJumps qR false) Δcka Δbucket qep gMain tL par A hq
      · exact redFSAuthDFPaperMultiBucketMode_la_false_pos_zero ℓ Pt C Dh encPt encT idOf lam q
          (authHopCutoff maxForwardJumps qR false) Δcka Δbucket qep gMain tL par hq_pos hΔb A hq


end MultiSessEndZero

end

end Computational.Proofs.E2E.SessionAuthMultiEnd

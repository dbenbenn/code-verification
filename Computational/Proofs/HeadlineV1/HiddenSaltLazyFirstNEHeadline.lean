/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.HeadlineComposed -- proof-setup: allow-public-import
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECell
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEReds -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDir2
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperSim
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.E2E.HeadlineSpkSession
import Computational.Proofs.E2E.RefuseCorrB0Core
import Computational.Proofs.E2E.SpkCostedAndHeadlineSlice
import Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg
import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp2
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedCouple
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedEvict
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNESkeleton
import Computational.Proofs.SessionCostedHalt
import Computational.Proofs.SignalPqxdh.Delta.Statements

/-!
# Headline Composed Security from `SessionCostedReductions`

Lifts per-session `SessionCostedReductions` families to `SessionCostedReductionFamily`, bounds the
`sessionSchemeU` and `sessionSchemeFixedSpk` mixture biases, and establishes the session and
composed `hiddenSaltBoundV1` bridges.-/

namespace CryptoVerification.E2E
public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.LibsignalSM.Proofs
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal
open CryptoVerification.LibsignalSession.HeadlineV1
open CryptoVerification.E2E.Signed
open CryptoGames.SM.Construction.AuthL11
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD


attribute [local irreducible] CryptoVerification.E2E.HeadlineSpk.mkSpkCostedReds
attribute [local irreducible] Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst

/-! ## Reduction family packaging -/

/-- Lifts a per-session `SessionCostedReductions` constructor family to `SessionCostedReductionFamily Pt ℓ`. -/
def spkSlotRedsWithSpqrOfV1SessionReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (v1Reds :
      (C : Crypto) → (K : MlKem) → (idA idB : IdentityKey) →
      (Dh : DHFun (BitVec 256) Pt) → (encPt : Pt → Bytes) →
      (encT : Pt → PublicKey) → (decT : PublicKey → Option Pt) →
      (lam : Pt) → (qep q : ℕ) →
      SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam) :
    SessionCostedReductionFamily Pt ℓ :=
  fun C K idA idB Dh encPt encT decT lam qep q =>
    v1Reds C K idA idB Dh encPt encT decT lam qep q

/-! ## Uniform-start mixture bias -/

/-- Bounds the `sessionSchemeU` mixture bias by `uniformStartMixtureBound` from a session-level
`hiddenSaltBoundV1` bound on `support oa`. -/
theorem boolBias_mixU_le_uTermShortMix_of_v1SessionReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem)
    (hK_tot : Encaps1Total K) (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh Z Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt,
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o,
      SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hHid : ∀ o ∈ support oa,
      let P := paramsV1 Z K (ida o) (idb o)
      LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) lam qep
          (RefuseB0.refuseCorrB0 (A o)) ≤
        hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o)
          (RefuseB0.refuseCorrB0 (A o)))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8 := by
      intros; rfl)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs := by
      intros; rfl)
    (hsimFig8 : ∀ o, (R o).simFig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).simFig8 := by
      intros; rfl)
    (hepoch0Red : ∀ o, (R o).epoch0Red =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).epoch0Red := by
      intros; rfl)
    (huniformStartRed : ∀ o, (R o).uniformStartRed =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).uniformStartRed := by
      intros; rfl) :
    𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  obtain ⟨A', hsup, hq'⟩ :
      ∃ A' : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
        (∀ o ∈ support oa, A' o = A o) ∧ (∀ o, SM.MakesAtMostQueries (A' o) q) := by
    classical
    refine ⟨fun o => if o ∈ support oa then A o
      else (pure false : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) Bool),
      fun o ho => ?_, fun o => ?_⟩
    · dsimp only; split_ifs; rfl
    · dsimp only
      split_ifs with ho
      · exact hq o ho
      · unfold SM.MakesAtMostQueries; simp
  have hqR : ∀ o, SM.MakesAtMostQueries (RefuseB0.refuseCorrB0 (A' o)) q := fun o => by
    rw [refuseCorrB0_eq]
    exact RefuseCorrB0.refuseCorrB0_queries (A' o) q (hq' o)
  have hU := boolBias_mixU_le_v1 Z K encPt lam encT decT qep oa ida idb A'
  simp only [← refuseCorrB0_eq] at hU
  have hUsEq :
      (prgAvg oa fun o => uniformStartDistinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
        (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
        (RefuseB0.refuseCorrB0 (A' o))) =
      (prefixPrgAvg oa fun o rc =>
        (R o).uniformStartRed.eval (fun _ => RefuseB0.refuseCorrB0 (A' o)) rc) := by
    funext rc
    unfold prgAvg CryptoVerification.E2E.prefixPrgAvg
    congr 1; funext o
    dsimp only
    rw [huniformStartRed o, v1SessionReds_uniformStartRed]
    exact
      (Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg.uniformStartRed_eval
        Z K Dh encPt encT decT (ida o) (idb o) lam ℓ q qep
        (RefuseB0.refuseCorrB0 (A' o)) rc (hqR o) hℓ).symm
  rw [hUsEq] at hU
  have hR := boolBias_mixR_le_v1 Z K hK_tot hℓ Dh hDh encPt encT decT hX hdec hD hinj hdum
    hz lam qep q hq32 δ hδ oa ida idb (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  have hAuthEq :
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q)
        (fun o => RefuseB0.refuseCorrB0 (A' o)) =
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
        (fun o => RefuseB0.refuseCorrB0 (A' o)) := by
    unfold fig8MixShortAuthV1
    simp only [← hfig8, ← hfs, ← hsimFig8]
  have hPrivEq :
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q)
        (fun o => RefuseB0.refuseCorrB0 (A' o)) =
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
        (fun o => RefuseB0.refuseCorrB0 (A' o)) := by
    unfold fig8MixShortPrivV1
    simp only [← hfig8, ← hfs, ← hsimFig8]
  have h1 := boolBias_mixFig8_le_fig8MixShortV1 Z K hD hℓ Dh hDh encPt encT decT hinj hdum lam qep q
    (by omega) oa ida idb (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  rw [hAuthEq, hPrivEq] at h1
  have h2 := evalDist_mixSimCNoneWin_le_fig8MixShortAuthV1 Z K hD hℓ Dh hDh encPt encT decT hinj hdum
    lam qep q (by omega) oa ida idb (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  rw [hAuthEq] at h2
  have h3 := evalDist_mixEps0_le_v1 Z K hℓ Dh encPt encT decT hX hdec hinj hdum
    lam qep q oa ida idb (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  have hEps0Eq :
      (prgAvg oa fun o => epoch0Distinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep
        (RefuseB0.refuseCorrB0 (A' o))) =
      (prefixPrgAvg oa fun o rc =>
        (R o).epoch0Red.eval (fun _ => RefuseB0.refuseCorrB0 (A' o)) rc) := by
    funext rc
    unfold prgAvg CryptoVerification.E2E.prefixPrgAvg
    congr 1; funext o
    dsimp only
    rw [hepoch0Red o, v1SessionReds_epoch0Red]
    exact
      (Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg.epoch0Red_eval
        Z K Dh encPt encT decT (ida o) (idb o) lam ℓ q qep
        (RefuseB0.refuseCorrB0 (A' o)) rc (hqR o) hℓ).symm
  rw [hEps0Eq] at h3
  have h4 := evalDist_mixHiddenSalt_le_v1_of_support Z K ℓ Dh encPt encT decT lam qep q δ
    oa ida idb R (fun o => RefuseB0.refuseCorrB0 (A' o))
    (fun o ho => by rw [hsup o ho]; exact hHid o ho)
  have hle :
      𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A' o)].boolBias ≤
        uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A' := by
    refine hU.trans ((add_le_add hR le_rfl).trans ?_)
    rw [mul_add, mul_add, mul_add]
    refine (add_le_add (add_le_add h1 (add_le_add le_rfl (add_le_add
      (add_le_add h2 (mul_le_mul_right h3 2)) (mul_le_mul_right h4 2)))) le_rfl).trans_eq ?_
    unfold CryptoVerification.E2E.uniformStartMixtureBound
      Signed.refineConst CryptoVerification.E2E.refineConst
    ring
  have hg :
      𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A' o)] =
      𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by
      rw [hsup o ho]
  rw [hg, uTermShortMixV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R _ _
    hsup] at hle
  exact hle

/-! ## Per-SPK-slot mixture bias -/

/-- Bounds the per-SPK-slot `sessionSchemeFixedSpk` mixture bias by `uniformStartMixtureBound` plus
the `Signed` PQXDH hop terms. -/
theorem boolBias_mixSpk_v1_le_of_v1SessionReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hK_tot : Encaps1Total K) (hD : ∀ k x, C.D k (C.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt,
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (R : ∀ o, SessionCostedReductions Pt ℓ C K (ida o) (idb o)
      Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hker : ∀ o (x : BitVec 256) (P₁ P₂ : Pt),
      Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh (s o) P₁ = Dh.dh (s o) P₂)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hHid : ∀ o ∈ support oa,
      let P := paramsV1 C K (ida o) (idb o)
      LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) lam qep
          (RefuseB0.refuseCorrB0 (A o)) ≤
        hiddenSaltBoundV1 C K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o)
          (RefuseB0.refuseCorrB0 (A o)))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8 := by
      intros; rfl)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).fs := by
      intros; rfl)
    (hsimFig8 : ∀ o, (R o).simFig8 =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).simFig8 := by
      intros; rfl)
    (hepoch0Red : ∀ o, (R o).epoch0Red =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).epoch0Red := by
      intros; rfl)
    (huniformStartRed : ∀ o, (R o).uniformStartRed =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT lam qep q).uniformStartRed := by
      intros; rfl) :
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    𝒟[oa >>= fun o =>
        SM.gameR (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      uniformStartMixtureBound C K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * Signed.hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
  intro spqr
  have hSpk := Signed.boolBias_mixSpkWithSpqr_le_of_support C spqr Dh encPt encT decT
    (by omega)
    (fun st rq st' salt msg h =>
      Nat.lt_of_le_of_lt (spqrV1Send_msg_len_le C.F K st rq st' salt msg h) (by decide))
    hDh hX hdec hz qep q oa ida idb s A hker hq
  have hU := boolBias_mixU_le_uTermShortMix_of_v1SessionReds C K hK_tot hD hℓ Dh hDh encPt encT
    decT hX hdec hinj hdum hz lam qep q hq32 δ hδ oa ida idb R A hq hHid hfig8 hfs hsimFig8
    hepoch0Red huniformStartRed
  exact hSpk.trans (add_le_add (add_le_add (add_le_add hU le_rfl) le_rfl) le_rfl)

/-! ## Composed headline bounds -/

/-- Packages a bounded `SessionCostedReductions` family satisfying the session-level
`hiddenSaltTerm` bound into `HiddenSaltBoundV1HoldsEx`. -/
theorem hiddenSaltBoundV1HoldsEx_of_v1SessionReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ)
    (v1Reds :
      (C : Crypto) → (K : LibsignalSpqrV1.MlKem) → (idA idB : IdentityKey) →
      (Dh : DHFun (BitVec 256) Pt) → (encPt : Pt → Bytes) →
      (encT : Pt → PublicKey) → (decT : PublicKey → Option Pt) →
      (lam : Pt) → (qep q : ℕ) →
      SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam)
    (hv1_bounds :
      ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
        (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
        (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ),
        qep ≤ q + 4 →
          sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
            (v1Reds C K idA idB Dh encPt encT decT lam qep q))
    (hHid :
      ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (_hK_tot : Encaps1Total K)
        (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
        (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
        (lam : Pt) (qep q : ℕ) (_hℓ : ℓ < 10 ^ 6)
        (_hDh : Dh.Commutes) (_hX : X25519RealizesDh C Dh encPt encT)
        (_hdec : ∀ T, decT (encT T) = some T) (_hinj : Function.Injective encT)
        (_hdum : ∀ T, encT T ≠ dummyKey)
        (_hz : ∀ x, Dh.dh x 0 = 0) (_hD : ∀ k x, C.D k (C.E k x) = x)
        (_hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
        (_hδ : ∀ Q : Pt,
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
        (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
        (_hq : SM.MakesAtMostQueries A q),
        let P := paramsV1 C K idA idB
        LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf idA idB) lam qep
            (RefuseB0.refuseCorrB0 A) ≤
          hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ
            (v1Reds C K idA idB Dh encPt encT decT lam qep q)
            (RefuseB0.refuseCorrB0 A))
    (hspk :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).spk =
          Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst
            ℓ C K idA idB Dh encPt encT decT lam q qep := by
      intros; rfl)
    (hfig8 :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).fig8 =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 := by
      intros; rfl)
    (hfs :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).fs =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fs := by
      intros; rfl)
    (hsimFig8 :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).simFig8 =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 := by
      intros; rfl)
    (hepoch0Red :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).epoch0Red =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red := by
      intros; rfl)
    (huniformStartRed :
      ∀ C K idA idB Dh encPt encT decT lam qep q,
        (v1Reds C K idA idB Dh encPt encT decT lam qep q).uniformStartRed =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed := by
      intros; rfl) :
    HiddenSaltBoundV1HoldsEx (Pt := Pt) ℓ := by
  intro C K idA idB Dh encPt encT decT lam qep q
  refine ⟨Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily ℓ v1Reds
      C K idA idB Dh encPt encT decT lam qep q,
    Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily_bounded ℓ v1Reds
      hv1_bounds C K idA idB Dh encPt encT decT lam qep q,
    ?_, ?_⟩
  · rw [Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily_fs, hfs]
    simp only [v1SessionReds_fs]
  · intro hqep
    rw [Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily_of_le ℓ v1Reds
      C K idA idB Dh encPt encT decT lam hqep]
    refine ⟨?_,
      hfig8 C K idA idB Dh encPt encT decT lam qep q,
      hsimFig8 C K idA idB Dh encPt encT decT lam qep q,
      hepoch0Red C K idA idB Dh encPt encT decT lam qep q,
      huniformStartRed C K idA idB Dh encPt encT decT lam qep q,
      ?_⟩
    · rw [hspk]
      intro hℓ hdec A hq
      exact
        ⟨fun s =>
          Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_evalSpkLeakRed
            (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep s A hq hℓ,
         Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_evalSpkLeakRedU
            (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep A hq hℓ,
         fun s j hj =>
          Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_evalHop2PrgRedK
            (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep s j A hdec hj hq hℓ,
         fun s j hj =>
          Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_evalHop2PrfRedK
            (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep s j A hdec hj hq hℓ⟩
    · intro hK_tot hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ A hq
      exact hHid C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD
        hq32 δ hδ A hq

open CryptoVerification.E2E.RefuseCorrB0 CryptoVerification.E2E.HeadlineU

private theorem forgeStage2CellBucketSumPaper_v1SessionRedsPaper_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
    (B_sm : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hqB : SM.MakesAtMostQueries B_sm q) :
    forgeStage2CellBucketSumPaper
        (lFig8 Dh encPt (paramsV1 C K idA idB).C (paramsV1 C K idA idB).codec ℓ encT
          (idsOf idA idB) 25000 lam)
        qep DeliverForge.sameHdrScheme
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (Proofs.Refinement.simDeliverForge (paramsV1 C K idA idB) ℓ Dh encPt encT decT
            (idsOf idA idB) lam qep B_sm)) =
      forgeStage2CellBucketSumPaper
        (lFig8 Dh encPt (paramsV1 C K idA idB).C (paramsV1 C K idA idB).codec ℓ encT
          (idsOf idA idB) 25000 lam)
        qep DeliverForge.sameHdrScheme
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).simDeliverForge.eval
            (fun _ => B_sm) ())) := by
  rw [v1SessionRedsPaper_simDeliverForge, v1SessionReds_simDeliverForge]
  unfold forgeStage2CellBucketSumPaper
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine Finset.sum_congr rfl fun t ht => ?_
    have ht2 : 2 ≤ t := (Finset.mem_Ico.mp ht).1
    have hc :=
      (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeRedProg_eq
        hℓ C K idA idB Dh encPt encT decT lam qep q (some (t - 2)) t B_sm hqB hq32).symm
    simpa only [DeliverForge.forgeGuessedAdvantageCellPaper, ht2, and_self, ↓reduceIte] using hc
  · refine Finset.sum_congr rfl fun t ht => ?_
    have ht3 : 3 ≤ t := (Finset.mem_Ico.mp ht).1
    have hne : ¬(2 ≤ t ∧ (some (t - 3) : Option ℕ) = some (t - 2)) := by simp; omega
    have hc :=
      (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeRedProg_eq
        hℓ C K idA idB Dh encPt encT decT lam qep q (some (t - 3)) t B_sm hqB hq32).symm
    simpa only [DeliverForge.forgeGuessedAdvantageCellPaper, hne, ht3, and_self, ↓reduceIte] using hc
  · refine Finset.sum_congr rfl fun tL _ => Finset.sum_congr rfl fun par _ => ?_
    exact
      (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeRedProg_eq
        hℓ C K idA idB Dh encPt encT decT lam qep q tL par B_sm hqB hq32).symm

/-- Bounds `hiddenSaltTerm` on `RefuseB0.refuseCorrB0 A` by `hiddenSaltBoundV1` plus
`K.kemFailFindAdvantage`. -/
theorem hiddenSaltTerm_le_hiddenSaltBoundV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (hK_tot : Encaps1Total K)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey)
    (hz : ∀ x, Dh.dh x 0 = 0) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q) :
    let P := paramsV1 C K idA idB
    LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf idA idB) lam qep
        (RefuseB0.refuseCorrB0 A) ≤
      hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ
        (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT
          lam qep q)
        (RefuseB0.refuseCorrB0 A) +
      K.kemFailFindAdvantage
        (Proofs.Refinement.redKemFailHiddenSalt P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep
          (RefuseB0.refuseCorrB0 A)) := by
  intro P
  have hqR : SM.MakesAtMostQueries A.refuseCorrB0 q :=
    RefuseCorrB0.refuseCorrB0_queries A q hq
  have hclamp := forgeStage2CellBucketSumPaper_v1SessionRedsPaper_eq
    hℓ C K idA idB Dh encPt encT decT lam qep q hq32 A.refuseCorrB0 hqR
  have hlazy := hiddenSaltTerm_le_add_spuriousStepTerm_v1_refuseCorrB0_lazy'
    C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD hq32
    (forgeStage2CellBucketSumPaper
      (lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam) qep DeliverForge.sameHdrScheme
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
        ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).simDeliverForge.eval
          (fun _ => A.refuseCorrB0) ())))
    δ hδ A hq (fun InvPQ _ hInv_top =>
      (CryptoVerification.LibsignalSession.HeadlineV1.evalDist_simulateQ_firstNESimImpl'_le_sum_cells
        P K rfl InvPQ hInv_top ℓ Dh hDh encPt encT decT (idsOf idA idB) ⟨rfl, rfl⟩ hX hinj hdec
        lam qep q A.refuseCorrB0).trans hclamp.le)
  have hpaper := sum_hiddenSaltCellTermPaperDF_le_hiddenSaltBoundV1_paper
    C K hD hℓ Dh hDh encPt encT decT hinj hdum idA idB lam qep q hq32 δ
    A.refuseCorrB0 hqR
  rw [refuseCorrB0_eq]
  exact hlazy.trans (add_le_add hpaper le_rfl)

/-- Establishes `HiddenSaltBoundV1HoldsEx` under zero `kemFailFindAdvantage`. -/
theorem hiddenSaltBoundV1HoldsEx
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ)
    (hK_zero : ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
      (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (lam : Pt) (qep : ℕ)
      (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes),
      K.kemFailFindAdvantage
        (Proofs.Refinement.redKemFailHiddenSalt (paramsV1 C K idA idB) K ℓ Dh encPt encT decT
          (idsOf idA idB) lam qep (RefuseB0.refuseCorrB0 A)) = 0) :
    HiddenSaltBoundV1HoldsEx (Pt := Pt) ℓ :=
  hiddenSaltBoundV1HoldsEx_of_v1SessionReds ℓ
    (v1SessionRedsPaper ℓ)
    (fun C K idA idB Dh encPt encT decT lam qep q hqep =>
      v1SessionRedsPaper_bounded ℓ C K idA idB Dh encPt encT decT lam qep q (by omega))
    (fun C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ
        A hq => by
      refine (hiddenSaltTerm_le_hiddenSaltBoundV1 C K hK_tot idA idB Dh encPt encT decT lam qep q
        hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ A hq).trans_eq ?_
      rw [hK_zero, add_zero])

open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedEvict
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedCouple

private theorem hiddenSaltBoundV1_rhs_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (R R₀ : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hchall : R.challSimDF.eval (fun _ => R.simDeliverForge.eval (fun _ => A) ()) () =
      DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
        (R.simDeliverForge.eval (fun _ => A) ()))
    (hfs : R.fs = R₀.fs)
    (hcka : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      (R₀.B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hprng : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      (R₀.B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hbfs : ∀ stage la : Bool, ∀ j ∈ Finset.range q, ∀ t ∈ Finset.range ((qep + 1) + 2),
      ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_fs stage la j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      (R₀.B_fs stage la j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hcka_u : ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      (R.B_cka_u tL par).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      (R₀.B_cka_u tL par).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hprng_u : ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      ∀ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
      (R.B_prng_u tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      (R₀.B_prng_u tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hbfs_u : ∀ stage la : Bool, ∀ j ∈ Finset.range q,
      ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      ∀ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
      (R.B_fs_u stage la j tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      (R₀.B_fs_u stage la j tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ()) :
    let qR := min (2 * q) (q + 2)
    let challAdvDF := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
      (R.simDeliverForge.eval (fun _ => A) ())
    ((∑ t ∈ Finset.Ico 2 ((qep + 1) + 2),
      let tL : Option ℕ := some (t - 2)
      (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          ((R₀.B_cka tL t).eval (fun _ => challAdvDF) ()) +
        PRFPRNG.advantage (rootPRNG Z.F encPt)
          ((R₀.B_prng tL t).eval (fun _ => challAdvDF) ()) +
        (∑ j ∈ Finset.range q,
          CryptoVerification.E2E.fsAeadAuthSlotSumBound Z qR R₀.fs
            (fun stage la => (R₀.B_fs stage la j tL t).eval (fun _ => challAdvDF) ())) +
        4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) +
      (∑ t ∈ Finset.Ico 3 ((qep + 1) + 2),
        let tL : Option ℕ := some (t - 3)
        (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
            ((R₀.B_cka tL t).eval (fun _ => challAdvDF) ()) +
          PRFPRNG.advantage (rootPRNG Z.F encPt)
            ((R₀.B_prng tL t).eval (fun _ => challAdvDF) ()) +
          (∑ j ∈ Finset.range q,
            CryptoVerification.E2E.fsAeadAuthSlotSumBound Z qR R₀.fs
              (fun stage la => (R₀.B_fs stage la j tL t).eval (fun _ => challAdvDF) ())) +
          4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) +
      (∑ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∑ par ∈ ({false, true} : Finset Bool),
        (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
            ((R₀.B_cka_u tL par).eval (fun _ => challAdvDF) ()) +
          (∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
            (PRFPRNG.advantage (rootPRNG Z.F encPt)
                ((R₀.B_prng_u tL par t).eval (fun _ => challAdvDF) ()) +
              (∑ j ∈ Finset.range q,
                CryptoVerification.E2E.fsAeadAuthSlotSumBound Z qR R₀.fs
                  (fun stage la => (R₀.B_fs_u stage la j tL par t).eval (fun _ => challAdvDF) ())))) +
          4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q))) +
      spuriousStepTerm Z.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ =
    hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT idA idB lam qep q δ R A := by
  unfold hiddenSaltBoundV1; dsimp only
  rw [hchall, hfs]
  refine congrArg (· + _) (congrArg (· + _)
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_))
  · refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ∈ Finset.range ((qep + 1) + 2) :=
      Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
    have htL' : some (t - 2) ∈ admissibleLastLeakGuesses 2 t := by
      have ht2 := (Finset.mem_Ico.mp ht).1
      simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      exact Or.inr ⟨t - 2, by omega, rfl⟩
    rw [hcka t ht' _ htL', hprng t ht' _ htL']
    refine congrArg (· + _) (congrArg (_ + ·) (Finset.sum_congr rfl fun j hj => ?_))
    exact congrArg (CryptoVerification.E2E.fsAeadAuthSlotSumBound Z _ R₀.fs)
      (funext fun stage => funext fun la => (hbfs stage la j hj t ht' _ htL').symm)
  · refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ∈ Finset.range ((qep + 1) + 2) :=
      Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
    have htL' : some (t - 3) ∈ admissibleLastLeakGuesses 2 t := by
      have ht3 := (Finset.mem_Ico.mp ht).1
      simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      exact Or.inr ⟨t - 3, by omega, rfl⟩
    rw [hcka t ht' _ htL', hprng t ht' _ htL']
    refine congrArg (· + _) (congrArg (_ + ·) (Finset.sum_congr rfl fun j hj => ?_))
    exact congrArg (CryptoVerification.E2E.fsAeadAuthSlotSumBound Z _ R₀.fs)
      (funext fun stage => funext fun la => (hbfs stage la j hj t ht' _ htL').symm)
  · refine Finset.sum_congr rfl fun tL htL => Finset.sum_congr rfl fun par _ => ?_
    rw [hcka_u tL htL par]
    refine congrArg (· + _) (congrArg (_ + ·) (Finset.sum_congr rfl fun t ht => ?_))
    rw [hprng_u tL htL par t ht]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun j hj => ?_)
    exact congrArg (CryptoVerification.E2E.fsAeadAuthSlotSumBound Z _ R₀.fs)
      (funext fun stage => funext fun la => (hbfs_u stage la j hj tL htL par t ht).symm)

/-- Generic cell-sum-to-`hiddenSaltBoundV1` bridge for any `SessionCostedReductions` bundle `R`
whose `challSimDF`, `fs`, `B_cka`, `B_prng`, `B_fs`, `B_cka_u`, `B_prng_u`, and `B_fs_u` agree on
evaluations with `v1SessionRedsPaper` and whose `dfAdv := R.simDeliverForge.eval (fun _ => A) ()`
satisfies `MakesAtMostQueriesDF`, `SendMsgsOkDF`, and `GuardedSMDFShort`. -/
theorem sum_hiddenSaltCellTermPaperDF_le_hiddenSaltBoundV1_of_dfReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
    (δ : ℝ≥0∞)
    (R : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq_df : DeliverForge.MakesAtMostQueriesDF (R.simDeliverForge.eval (fun _ => A) ()) q)
    (hsh_df : SendMsgsOkDF
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (R.simDeliverForge.eval (fun _ => A) ()))
    (hg_df : GuardedSMDFShort (R.simDeliverForge.eval (fun _ => A) ()))
    (hchall : R.challSimDF.eval (fun _ => R.simDeliverForge.eval (fun _ => A) ()) () =
      DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
        (R.simDeliverForge.eval (fun _ => A) ()))
    (hfs : R.fs = (v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).fs)
    (hcka : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      ((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hprng : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      ((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hbfs : ∀ stage la : Bool, ∀ j ∈ Finset.range q, ∀ t ∈ Finset.range ((qep + 1) + 2),
      ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_fs stage la j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      ((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_fs stage la j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) ())
    (hcka_u : ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      (R.B_cka_u tL par).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      ((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_cka_u tL par).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () := by intros; rfl)
    (hprng_u : ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      ∀ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
      (R.B_prng_u tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      ((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_prng_u tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () := by intros; rfl)
    (hbfs_u : ∀ stage la : Bool, ∀ j ∈ Finset.range q,
      ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      ∀ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
      (R.B_fs_u stage la j tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () =
      ((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_fs_u stage la j tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => A) ())) () := by intros; rfl) :
    let dfAdv := R.simDeliverForge.eval (fun _ => A) ()
    forgeStage2CellBucketSumPaper
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        qep DeliverForge.sameHdrScheme
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) +
      spuriousStepTerm Z.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ ≤
    hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT idA idB lam qep q δ R A := by
  intro dfAdv
  have hmain := forgeStage2CellBucketSumPaper_le_v1SessionRedsPaper_dfAdv
    Z K hD hℓ Dh hDh encPt encT decT hinj hdum idA idB lam qep q hq32 dfAdv hq_df hsh_df hg_df
  exact (add_le_add (add_le_add hmain le_rfl) le_rfl).trans_eq
    (hiddenSaltBoundV1_rhs_eq Z K Dh encPt encT decT idA idB lam qep q δ R
      (v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q) A
      hchall hfs hcka hprng hbfs hcka_u hprng_u hbfs_u)

/-- Bounds `hiddenSaltTermTrackHalted` on `RefuseB0.refuseCorrB0 A` by `hiddenSaltBoundV1` with no
`kemFailFindAdvantage` error term. -/
theorem hiddenSaltTermTrackHalted_le_hiddenSaltBoundV1_of_dfReds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (hK_tot : Encaps1Total K)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey)
    (hz : ∀ x, Dh.dh x 0 = 0) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (R : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q)
    (hq_df : DeliverForge.MakesAtMostQueriesDF
      (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()) q)
    (hsh_df : SendMsgsOkDF
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()))
    (hg_df : GuardedSMDFShort (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()))
    (hcell_le : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      DeliverForge.forgeGuessedAdvantageCellPaper
        (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        (qep + 1) DeliverForge.sameHdrScheme tL t
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (Proofs.Refinement.simDeliverForgeTrackHalted (paramsV1 C K idA idB) K ℓ Dh encPt encT
            decT (idsOf idA idB) lam qep (RefuseB0.refuseCorrB0 A))) ≤
      DeliverForge.forgeGuessedAdvantageCellPaper
        (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        (qep + 1) DeliverForge.sameHdrScheme tL t
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())))
    (hbucket_le : ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      DeliverForge.forgeBucketAdvantagePaper
        (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        1 (qep + 1) DeliverForge.sameHdrScheme tL par
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (Proofs.Refinement.simDeliverForgeTrackHalted (paramsV1 C K idA idB) K ℓ Dh encPt encT
            decT (idsOf idA idB) lam qep (RefuseB0.refuseCorrB0 A))) ≤
      DeliverForge.forgeBucketAdvantagePaper
        (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        1 (qep + 1) DeliverForge.sameHdrScheme tL par
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())))
    (hchall : R.challSimDF.eval
        (fun _ => R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()) () =
      DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
        (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()))
    (hfs : R.fs = (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).fs)
    (hcka : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () =
      ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_cka tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) ())
    (hprng : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () =
      ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_prng tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) ())
    (hbfs : ∀ stage la : Bool, ∀ j ∈ Finset.range q, ∀ t ∈ Finset.range ((qep + 1) + 2),
      ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      (R.B_fs stage la j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () =
      ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_fs stage la j tL t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) ())
    (hcka_u : ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      (R.B_cka_u tL par).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () =
      ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_cka_u tL par).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () := by intros; rfl)
    (hprng_u : ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      ∀ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
      (R.B_prng_u tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () =
      ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_prng_u tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () := by intros; rfl)
    (hbfs_u : ∀ stage la : Bool, ∀ j ∈ Finset.range q,
      ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      ∀ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
      (R.B_fs_u stage la j tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () =
      ((v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_fs_u stage la j tL par t).eval
        (fun _ => DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ())) () := by intros; rfl) :
    let P := paramsV1 C K idA idB
    Proofs.Refinement.hiddenSaltTermTrackHalted P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep
        (RefuseB0.refuseCorrB0 A) ≤
      hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ R
        (RefuseB0.refuseCorrB0 A) := by
  intro P
  let idOf := idsOf idA idB
  let dfAdv := R.simDeliverForge.eval (fun _ => RefuseB0.refuseCorrB0 A) ()
  have hsum_stage2 :
      forgeStage2CellBucketSumPaper
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        qep DeliverForge.sameHdrScheme
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (Proofs.Refinement.simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
            A.refuseCorrB0)) ≤
      forgeStage2CellBucketSumPaper
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        qep DeliverForge.sameHdrScheme
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) := by
    unfold forgeStage2CellBucketSumPaper
    refine add_le_add (add_le_add ?_ ?_) ?_
    · refine Finset.sum_le_sum fun t ht => ?_
      have ht2 := (Finset.mem_Ico.mp ht).1
      have ht' : t ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
      have htL : some (t - 2) ∈ admissibleLastLeakGuesses 2 t := by
        simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
        exact Or.inr ⟨t - 2, by omega, rfl⟩
      have hc := hcell_le t ht' (some (t - 2)) htL
      simp only [DeliverForge.forgeGuessedAdvantageCellPaper, ht2, and_self, ↓reduceIte] at hc
      rw [← refuseCorrB0_eq]
      exact hc
    · refine Finset.sum_le_sum fun t ht => ?_
      have ht3 := (Finset.mem_Ico.mp ht).1
      have ht' : t ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
      have htL : some (t - 3) ∈ admissibleLastLeakGuesses 2 t := by
        simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
        exact Or.inr ⟨t - 3, by omega, rfl⟩
      have hne : ¬(2 ≤ t ∧ (some (t - 3) : Option ℕ) = some (t - 2)) := by simp; omega
      have hc := hcell_le t ht' (some (t - 3)) htL
      simp only [DeliverForge.forgeGuessedAdvantageCellPaper, hne, ht3, and_self, ↓reduceIte] at hc
      rw [← refuseCorrB0_eq]
      exact hc
    · refine Finset.sum_le_sum fun tL htL => Finset.sum_le_sum fun par _ => ?_
      rw [← refuseCorrB0_eq]
      exact hbucket_le tL htL par
  have hlazy := hiddenSaltTermTrackHalted_le_add_spuriousStepTerm_v1_refuseCorrB0_lazy'
    C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD hq32
    (forgeStage2CellBucketSumPaper
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      qep DeliverForge.sameHdrScheme
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv))
    δ hδ A hq (fun InvPQ _ hInv_top =>
      (evalDist_simulateQ_firstNEHalted'_le_sum_cells P K rfl InvPQ hInv_top ℓ Dh hDh encPt encT
        decT idOf ⟨rfl, rfl⟩ hX hinj hdec lam qep q A.refuseCorrB0).trans hsum_stage2)
  have hreds := sum_hiddenSaltCellTermPaperDF_le_hiddenSaltBoundV1_of_dfReds
    C K hD hℓ Dh hDh encPt encT decT hinj hdum idA idB lam qep q hq32 δ R (RefuseB0.refuseCorrB0 A)
    hq_df hsh_df hg_df hchall hfs hcka hprng hbfs hcka_u hprng_u hbfs_u
  rw [← refuseCorrB0_eq] at hlazy
  exact hlazy.trans hreds

end

end CryptoVerification.E2E

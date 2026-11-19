/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SignedRefine -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SignedFSBound -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.RefuseCorrB0Core -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SignedPrims -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatements -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedFS -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8SourceCosts -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.QuerySubsumes -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem1 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.FSAEADRed -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.BucketAuthBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Encaps1Total -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.QueryBounds
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Queries
import Computational.Proofs.CryptoGames.SM.SessionProofs.BlankLemma18
import Computational.Proofs.E2E.SignedFig8
import Computational.Proofs.E2E.SignedThm1
import Computational.Proofs.E2E.SignedThm12
import Computational.Proofs.E2E.SignedThm8
import Computational.Proofs.HeadlineV1.SendShortC
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SpqrV1Sync.SendTotal
public import Computational.Proofs.E2E.SignedAdv -- proof-setup: allow-public-import

/-!
# Mixture refinement bounds with SPQR V1

Integrates the U-hop, simulator refinement, epoch-0 PRG, hidden-salt, Fig. 8, and FS-AEAD bounds
over a prefix distribution `oa` for `paramsV1 Z K (ida o) (idb o)`.-/

namespace CryptoVerification.E2E.Signed
public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec MeasureTheory ENNReal


open CryptoGames CryptoGames.SM CryptoGames.SM.Construction CryptoGames.Ratchet
  CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSM.Proofs CryptoVerification.E2E
  CryptoGames.LibsignalSession CryptoGames.CKA LibsignalProtoCodec CryptoGames.LibsignalSM
  CryptoGames.LibsignalSM.Proofs.Refinement CryptoGames.Ratchet.LibsignalSim
  CryptoGames.Ratchet.LibsignalSimC CryptoGames.SM.Construction.DeliverForge
  CryptoVerification.E2E.RefuseCorrB0 CryptoVerification.E2E.HeadlineU
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1Sync.SendTotal
  CryptoVerification.LibsignalSession.HeadlineV1

/-! ## `paramsV1` and `KemFailFind` mixture averaging -/

/-- Session `Params` for identity keys `(idA, idB)` with `spqrV1SessionUniformCoins Z.F K`. -/
abbrev paramsV1 (Z : Crypto) (K : MlKem) (idA idB : IdentityKey) :
    LibsignalSession.Params Bytes (BitVec 512) :=
  paramsIdsWithSpqr Z (spqrV1SessionUniformCoins Z.F K) idA idB

@[simp] theorem paramsV1_C (Z : Crypto) (K : MlKem) (idA idB : IdentityKey) :
    (paramsV1 Z K idA idB).C = Z := rfl

@[simp] theorem paramsV1_codec (Z : Crypto) (K : MlKem) (idA idB : IdentityKey) :
    (paramsV1 Z K idA idB).codec = protoSignalCodec := rfl

/-- Averages a family of `KemFailFind` adversaries over a prefix distribution `oa`. -/
def kemFailAvg {α : Type} (oa : ProbComp α) (B : α → MlKem.KemFailFindAdversary) :
    MlKem.KemFailFindAdversary :=
  oa >>= B

/-! ## U-mixture hop -/

@[simp] theorem sessionSchemeU_eq_libSessionU_poly {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ : ℕ) :
    sessionSchemeU P ℓ = libSessionU P ℓ := rfl

/-- Mixture U-hop bound for `paramsV1` with a single uniform `rootKdfAsPrg` distinguisher. -/
theorem boolBias_mixU_le_v1 {Pt α : Type} (Z : Crypto) (K : MlKem) {ℓ : ℕ}
    (encPt : Pt → Bytes) (lam : Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      𝒟[oa >>= fun o => SM.gameR (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam) 3 qep
          (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
          (A o).refuseCorrB0].boolBias
        + 2 * (LibsignalSim.rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => uniformStartDistinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
            (A o).refuseCorrB0) := by
  have hU : 𝒟[oa >>= fun o => SM.gameR (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (A o)] =
      𝒟[PRGScheme.prgIdealExperiment
        (prgAvg oa fun o => uniformStartDistinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
          (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
          (A o).refuseCorrB0)] := by
    rw [prgIdeal_avg]
    refine evalDist_bind_congr _ _ _ fun o => ?_
    rw [sessionSchemeU_eq_libSessionU_poly, ← evalDist_gameR_libSessionU_eq_prgIdeal]
    exact congrArg _ (gameR_withNoCorrB0_eq _ 3 qep
      (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) rfl (A o))
  have hR : 𝒟[oa >>= fun o => SM.gameR (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam) 3
        qep (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
        (A o).refuseCorrB0] =
      𝒟[(LibsignalSim.rootKdfAsPrg Z.F (encPt lam)).prgRealExperiment
        (prgAvg oa fun o => uniformStartDistinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
          (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
          (A o).refuseCorrB0)] := by
    rw [prgReal_avg]
    exact evalDist_bind_congr _ _ _ fun o => evalDist_gameR_libSessionR_eq_prgReal _ ℓ encPt lam _
      qep _
  unfold PRGScheme.prgAdvantage
  rw [hU, hR, Measure.boolDist_comm
    𝒟[(LibsignalSim.rootKdfAsPrg Z.F (encPt lam)).prgRealExperiment _]]
  exact SM.Construction.boolBias_le_add_two_mul_boolDist _ _

theorem boolDist_bind_le_add3 {α : Type} (oa : ProbComp α) (f g h₁ h₂ h₃ : α → ProbComp Bool)
    (c : ℝ≥0∞)
    (H : ∀ a, 𝒟[f a].boolDist 𝒟[g a] ≤
      c + (𝒟[h₁ a] {true} + 𝒟[h₂ a] {true} + 𝒟[h₃ a] {true})) :
    𝒟[oa >>= f].boolDist 𝒟[oa >>= g] ≤
      c + (𝒟[oa >>= h₁] {true} + 𝒟[oa >>= h₂] {true} + 𝒟[oa >>= h₃] {true}) := by
  refine Measure.boolDist_le_of_apply_le _ _ fun v => ?_
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral,
    evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral,
    evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa]
      ≤ ∫⁻ a, (𝒟[g a] {v} + (c + (𝒟[h₁ a] {true} + 𝒟[h₂ a] {true} + 𝒟[h₃ a] {true}))) ∂𝒟[oa] :=
        lintegral_mono fun a => (apply_le_add_boolDist _ _ v).trans (add_le_add le_rfl (H a))
    _ = ∫⁻ a, 𝒟[g a] {v} ∂𝒟[oa] +
          (c + (∫⁻ a, 𝒟[h₁ a] {true} ∂𝒟[oa] + ∫⁻ a, 𝒟[h₂ a] {true} ∂𝒟[oa] +
            ∫⁻ a, 𝒟[h₃ a] {true} ∂𝒟[oa])) := by
      rw [lintegral_add_left Measurable.of_discrete, lintegral_add_left measurable_const,
        lintegral_const, evalDist_apply_univ_eq_one, mul_one,
        lintegral_add_left Measurable.of_discrete, lintegral_add_left Measurable.of_discrete]

/-! ## Mixture refinement, epoch-0, and hidden-salt bounds -/

section RefineV1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Mixture simulator refinement bound for `paramsV1`. -/
theorem boolBias_mixR_le_v1 {α : Type} (Z : Crypto) (K : MlKem) (hK_tot : Encaps1Total K)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh Z Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0) (lam : Pt) (qep q : ℕ)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => SM.gameR (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) (A o)].boolBias ≤
      𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
          (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1
          (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
            (idsOf (ida o) (idb o)) lam qep (A o))].boolBias
        + 2 * (refineConst Z Dh encPt q qep δ +
          (𝒟[oa >>= fun o => simCNoneWinEvent (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o)] {true} +
           𝒟[oa >>= fun o => eps0Event (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam
              (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] {true} +
           𝒟[oa >>= fun o => hiddenSaltGame (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o)] {true})) := by
  refine (SM.Construction.boolBias_le_add_two_mul_boolDist _ _).trans (add_le_add le_rfl ?_)
  refine mul_le_mul_right ?_ 2
  refine boolDist_bind_le_add3 _ _ _ _ _ _ _ fun o => ?_
  have hL : LengthsOk (paramsV1 Z K (ida o) (idb o)) ℓ :=
    lengthsOk_paramsIdsWithSpqr_v1 Z K (ida o) (idb o) ℓ hℓ
  have hrt : RoundTrip.RtHyp (paramsV1 Z K (ida o) (idb o)) ℓ :=
    ⟨CryptoVerification.LibsignalSession.signalRoundTripShort_proto, hL,
      CryptoVerification.LibsignalSession.signalEncodeFits32_proto⟩
  have hS : Corr.SpqrSendCorrectQ (paramsV1 Z K (ida o) (idb o)).spqr q :=
    spqrV1SessionB_sendCorrectQ Z.F K hK_tot q (by omega)
  refine (sim_game_boolDist_le_C (paramsV1 Z K (ida o) (idb o)) ℓ Dh hDh encPt encT decT hX hdec
    hD hrt hinj hdum hz (idsOf (ida o) (idb o)) ⟨rfl, rfl⟩ lam qep q hS (by omega) δ hδ (A o)
    (hq o)).trans_eq ?_
  have hC : (paramsV1 Z K (ida o) (idb o)).C = Z := rfl
  have hcod : (paramsV1 Z K (ida o) (idb o)).codec = protoSignalCodec := rfl
  rw [hC, hcod]
  unfold refineConst hiddenSaltTerm
  ring

/-- Mixture epoch-0 bound for `paramsV1` with a single uniform `rootKdfAsPrg` distinguisher. -/
theorem evalDist_mixEps0_le_v1 {α : Type} (Z : Crypto) (K : MlKem) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hX : X25519RealizesDh Z Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => eps0Event (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] {true} ≤
      (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => epoch0Distinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
            (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o))
        + q * eps0IdealUnit Z.F := by
  have hR : 𝒟[oa >>= fun o => eps0Event (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] =
      𝒟[(rootKdfAsPrg Z.F (encPt lam)).prgRealExperiment
          (prgAvg oa fun o => epoch0Distinguisher (paramsV1 Z K (ida o) (idb o)) ℓ
            (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o))] := by
    rw [prgReal_avg]
    exact evalDist_bind_congr _ _ _ fun o => evalDist_eps0Event_eq_prgReal _ ℓ encPt lam _ qep _
  rw [hR]
  refine (Refinement.prgReal_true_le _ _).trans (add_le_add le_rfl ?_)
  rw [prgIdeal_avg]
  refine evalDist_bind_apply_le_const _ _ _ true fun o => ?_
  have hrt : RoundTrip.RtHyp (paramsV1 Z K (ida o) (idb o)) ℓ :=
    ⟨CryptoVerification.LibsignalSession.signalRoundTripShort_proto,
      lengthsOk_paramsIdsWithSpqr_v1 Z K (ida o) (idb o) ℓ hℓ,
      CryptoVerification.LibsignalSession.signalEncodeFits32_proto⟩
  exact eps0_ideal_le (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT hX hdec hinj hdum hrt
    qep q (A o) (hq o)

end RefineV1

/-! ## Mixture Fig. 8 bounds -/

section Fig8V1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Authenticity term of the mixture Fig. 8 bound for `libsignalToModularSchemeSim` on `paramsV1`. -/
@[expose] noncomputable def fig8MixAuth_v1 {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
    (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (advAvg oa fun o => redCKAAuth (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1)
            (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))))
      + PRFPRNG.advantage (rootPRNG Z.F encPt)
        (advAvg oa fun o => redPRNGAuth (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1)
            (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))))
      + ∫⁻ o, ∑ j ∈ Finset.range q,
          FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) j
              tL t (Thm1.challSim (2 + 1) (qep + 1)
                (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
                  (idsOf (ida o) (idb o)) lam qep (A o))))
          ∂𝒟[oa])

/-- Privacy term of the mixture Fig. 8 bound for `libsignalToModularSchemeSim` on `paramsV1`. -/
@[expose] noncomputable def fig8MixPriv_v1 {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  2 * ∑ i ∈ Finset.range ((qep + 1) + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (advAvg oa fun o => redCKAPriv (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
          (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ)
            (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))))
      + 2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
        (advAvg oa fun o => redPRNGPriv (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
          (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ)
            (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))))
      + 𝒟[oa >>= fun o =>
          FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSPriv (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ)
                (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
                  (idsOf (ida o) (idb o)) lam qep (A o))))].boolBias
      + 2 * ∫⁻ o,
          FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSPrivCoin (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ)
                (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
                  (idsOf (ida o) (idb o)) lam qep (A o))))
          ∂𝒟[oa])

section BucketAuthToAuthHelpers

open _root_.CryptoGames.SM.BucketAuthBridge (BucketState bucketAuthAdvantage
  bucketAuthGame bucketCfg bucketInjectImpl bucketOracleImpl bucketRun
  lemma17_bucket_mix liftGameStep run_win_prob_le_bucketAuth)
open CryptoGames.SM.Thm1L17 (coins_step_h corr_step_h deliver_step_h epMgmt_win
  eq_of_mem_support_fullImpl_of_win_true fullImpl inject_step_h samCoins transmit_step_h)
open CryptoGames.LibsignalSM.Proofs.BlankLemma18 (challMsgB challMsgB_zero gameB h3B_final_proof)

private theorem boolBias_mixH2_le_priv_s1 {α : Type} (Z : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (simH : α → Fig8Adv Pt ℓ)
    (heqPub : ∀ o, SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (simH o)) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) SM.Config.h2 (simH o)].boolBias ≤
      2 * ∑ i ∈ Finset.range ((qep + 1) + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
        (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
            (advAvg oa fun o => redCKAPriv (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))
          + 2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
            (advAvg oa fun o => redPRNGPriv (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))
          + 𝒟[oa >>= fun o =>
              FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
                (redFSPriv (dhScheme Dh) (rootPRNG Z.F encPt)
                  (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
                  (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))].boolBias
          + 2 * ∫⁻ o,
              FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
                (redFSPrivCoin (dhScheme Dh) (rootPRNG Z.F encPt)
                  (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
                  (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))
              ∂𝒟[oa]) := by
  let _ : MeasurableSpace α := ⊤
  let sm : α → _ := fun o =>
    lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam
  have htel : ∀ n : ℕ,
      𝒟[oa >>= fun o => SM.game (sm o) (2 + 1) (qep + 1) SM.Config.h2 (simH o)].boolBias ≤
        𝒟[oa >>= fun o => gameB (sm o) (2 + 1) (qep + 1) (challMsgB n (lBlank ℓ)) (simH o)].boolBias +
          2 * ∑ i ∈ Finset.range n, ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
            𝒟[oa >>= fun o =>
              privGame (sm o) (2 + 1) (qep + 1) tL i
                (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o))].boolBias := by
    intro n
    induction n with
    | zero =>
      simp only [challMsgB_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      exact le_rfl
    | succ n ih =>
      refine ih.trans ?_
      have h := lemma18B_mix sm (2 + 1) (qep + 1) (by omega) (lBlank ℓ) n oa simH
      rw [Finset.sum_range_succ, mul_add, add_comm (2 * ∑ i ∈ Finset.range n, _), ← add_assoc]
      exact add_le_add h le_rfl
  have hfin :
      𝒟[oa >>= fun o =>
          gameB (sm o) (2 + 1) (qep + 1) (challMsgB ((qep + 1) + 1) (lBlank ℓ)) (simH o)].boolBias = 0 :=
    boolBias_mix_eq_zero oa _ fun o =>
      h3B_final_proof (sm o) (2 + 1) (qep + 1)
        (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (lBlank ℓ)
        (fun _ _ h => by simp [lBlank, h]) (simH o) (heqPub o)
  have h18 := htel ((qep + 1) + 1)
  rw [hfin, zero_add] at h18
  refine h18.trans ?_
  gcongr with i _ tL _
  exact theorem12_mix (dhScheme Dh) (rootPRNG Z.F encPt)
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
    (dhScheme_correct Dh hDh) tL i oa _

end BucketAuthToAuthHelpers

end Fig8V1

/-! ## Mixture FS-AEAD bound -/

section ShortMixV1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

end ShortMixV1

/-! ## Generic simulator-family Fig. 8 mixture bounds -/

section Fig8GenV1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Authenticity term of the mixture Fig. 8 bound for a simulator family `simH`. -/
@[expose] noncomputable def fig8MixAuthGen_v1 {α : Type} (Z : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (simH : α → Fig8Adv Pt ℓ) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
    (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (advAvg oa fun o => redCKAAuth (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1) (simH o)))
      + PRFPRNG.advantage (rootPRNG Z.F encPt)
        (advAvg oa fun o => redPRNGAuth (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1) (simH o)))
      + ∫⁻ o, ∑ j ∈ Finset.range q,
          FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) j
              tL t (Thm1.challSim (2 + 1) (qep + 1) (simH o)))
          ∂𝒟[oa])

/-- Privacy term of the mixture Fig. 8 bound for a simulator family `simH`. -/
@[expose] noncomputable def fig8MixPrivGen_v1 {α : Type} (Z : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (simH : α → Fig8Adv Pt ℓ) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  2 * ∑ i ∈ Finset.range ((qep + 1) + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (advAvg oa fun o => redCKAPriv (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
          (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))
      + 2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
        (advAvg oa fun o => redPRNGPriv (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
          (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))
      + 𝒟[oa >>= fun o =>
          FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSPriv (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))].boolBias
      + 2 * ∫⁻ o,
          FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
            (redFSPrivCoin (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
              (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simH o)))
          ∂𝒟[oa])

/-- Stage-2 bucketed Fig. 8 H1 bias of any `simH` mixture satisfying `EqualPubChalls`
(`BucketAuthBridge.lemma17_bucket_mix` + `lemma18B_mix` + `theorem12_mix`). -/
theorem boolBias_mixFig8Gen_le_bucketAuth_v1 {α : Type} (Z : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (simH : α → Fig8Adv Pt ℓ)
    (heqPub : ∀ o, SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (simH o)) :
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simH o)].boolBias ≤
      2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
          𝒟[oa >>= fun o =>
            _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthGame
              (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
              (2 + 1) (qep + 1) tL (Thm1.challSim (2 + 1) (qep + 1) (simH o))] {true}
        + fig8MixPrivGen_v1 Z ℓ Dh encPt encT lam qep oa ida idb simH := by
  let _ : MeasurableSpace α := ⊤
  have h17 := _root_.CryptoGames.SM.BucketAuthBridge.lemma17_bucket_mix
    (fun o => lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
    (2 + 1) (qep + 1) (by omega) oa simH
  have hPriv := boolBias_mixH2_le_priv_s1 Z ℓ Dh hDh encPt encT lam qep oa ida idb simH heqPub
  calc _ ≤ _ := h17
    _ ≤ fig8MixPrivGen_v1 Z ℓ Dh encPt encT lam qep oa ida idb simH + _ :=
      add_le_add hPriv le_rfl
    _ = _ := add_comm _ _

end Fig8GenV1

/-! ## Tracker-halted simulator Fig. 8 mixture bounds -/

section Fig8TrackHaltedV1

open CryptoGames.Ratchet.LibsignalSimC

/-- Fig. 8 `win` event for `runLibsignalToModularSchemeSimTrackHalted`. -/
def simCNoneWinEventTrackHalted {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (CBC.Plain ℓ) (BitVec 512) (List (BitVec 8))) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, s) ← SM.run sm 3 (qep + 1) SM.Config.h1 b
    (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A)
  return s.win

end Fig8TrackHaltedV1

end

end CryptoVerification.E2E.Signed

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
import Computational.Proofs.SpecLemmas.Session.GameRCoinLogged
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
import Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp
public import Computational.Proofs.E2E.SignedSession -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedDF -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedHalt
public import Computational.Proofs.E2E.HeadlineComposed -- proof-setup: allow-public-import
import Computational.Proofs.E2E.HeadlineSpkSession
import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg
import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg
import Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog
import Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog
import Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEReds
import Computational.Proofs.E2E.RefuseCorrB0Core
import Computational.Proofs.E2E.HaltedSpkSession
import Computational.Proofs.E2E.HaltedSessionChain
import Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg
import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.HeadlineV1.SendShortC
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHeadline
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SpqrV1Sync.SendTotal
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedRefinesC
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCoupling
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedSanGame

/-!
# Lemma 2: single-session security with costed reductions

**Checked by Lean.** Proves `GameRCoinLoggedFaithful` (`gameRCoinLogged_faithful`) and
`SessionSecure ℓ` (`session_secure_proof`) by splitting the `SM.gameR` mixture bias into the
tracker-halted `gameRTrackHalted` bias plus `2 * sessionKemFailProb` and bounding the halted game
via the clamped costed reduction family `v1SessionRedsHaltedClamped`.-/

public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoGames.Ratchet.LibsignalSim
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Signed

local instance instInhabitedOfZeroHeadlineSession {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

/-! ## Epoch-cap clamping and generic session bound -/

/-- Clamps `qep` to `min qep (q + 4)` in `gameRTrackHalted` when every `A o` makes at most `q`
queries. -/
theorem evalDist_mixGameRTrackHalted_min_eq {α PQ : Type} [Inhabited PQ]
    (pqrOf : SampledSessionKey → BitVec 256)
    (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (P : α → Params PQ (BitVec 512)) (hF : ∀ o, (P o).C.F = F)
    (ℓ Δ qep q : ℕ) (s : α → BitVec 256)
    (cfg : SM.ConfigR (GhostState PQ) (CBC.Plain ℓ) Bytes)
    (oa : ProbComp α)
    (A : α → SM.Adversary (GhostState PQ) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted pqrOf F K
            (sessionSchemeFixedSpk (P o) ℓ (s o)) Δ qep cfg (A o)] =
      𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted pqrOf F K
            (sessionSchemeFixedSpk (P o) ℓ (s o)) Δ (min qep (q + 4)) cfg (A o)] :=
  Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.evalDist_mixGameRTrackHalted_min_eq
    pqrOf F K P hF ℓ Δ qep q s cfg oa A hq

/-- Forgetting the send-coin log recovers `SM.gameR`. -/
theorem gameRCoinLogged_faithful : GameRCoinLoggedFaithful :=
  Computational.Proofs.SpecLemmas.Session.GameRCoinLogged.gameRCoinLogged_faithful

theorem sessBound_eq_gen
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (spkLeakT : α → BitVec 256 →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (spkLeakUT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (hop2PrgT : α → BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      PRGScheme.PRGAdversary (BitVec 256 × BitVec 256))
    (hop2PrfT : α → BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (hdec : ∀ T, decT (encT T) = some T)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hspk : ∀ o ∈ support oa,
      SpkCostedEvalAgreesGen C K ℓ Dh encPt encT decT 0 q
        (spkLeakT o) (spkLeakUT o) (hop2PrgT o) (hop2PrfT o)
        (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).spk) :
    let R := fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q
    sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A =
      uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa ida idb R A
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o => spkLeakT o (s o) (A o)))
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o => spkLeakUT o (A o)))
        + 2 * (epoch0ChainForgeryTerm C.F q
            + (∑ j ∈ Finset.range spkSwapHybridCount,
                ((Ratchet.expandPRG C.F).prgAdvantage
                    (prefixPrgAvg oa (fun o => hop2PrgT o (s o) j (A o)))
                  + (extractPRF C.F encPt).prfAdvantage
                    (prefixPrfAvg oa (fun o => hop2PrfT o (s o) j (A o)))))
            + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q
            + spkSwapCreationPointHitTerm Dh q + spkSwapHiddenScalarGuessTerm Dh q) := by
  set R := fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q
  set Rspk := fun o => (R o).spk
  have hl1 :
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o => evalSpkLeakRed (Rspk o).spkLeakRed (s o) (A o))) =
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o => spkLeakT o (s o) (A o))) :=
    Signed.prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
      fun o ho => (hspk o ho hℓ hdec (A o) (hq o ho)).1 (s o)
  have hl2 :
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRedU (Rspk o).spkLeakRedU
            (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (A o)))) =
      (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o => spkLeakUT o (A o))) :=
    Signed.prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
      fun o ho => (hspk o ho hℓ hdec (A o) (hq o ho)).2.1
  have hsum :
      (∑ j ∈ Finset.range spkSwapHybridCount,
        ((Ratchet.expandPRG C.F).prgAdvantage
            (prefixPrgAvg oa (fun o =>
              evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (A o)))
          + (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o =>
              evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (A o))))) =
      (∑ j ∈ Finset.range spkSwapHybridCount,
        ((Ratchet.expandPRG C.F).prgAdvantage
            (prefixPrgAvg oa (fun o => hop2PrgT o (s o) j (A o)))
          + (extractPRF C.F encPt).prfAdvantage
            (prefixPrfAvg oa (fun o => hop2PrfT o (s o) j (A o))))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < spkSwapHybridCount := Finset.mem_range.mp hj
    have hprg :
        (Ratchet.expandPRG C.F).prgAdvantage
          (prefixPrgAvg oa (fun o =>
            evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (A o))) =
        (Ratchet.expandPRG C.F).prgAdvantage
          (prefixPrgAvg oa (fun o => hop2PrgT o (s o) j (A o))) :=
      Signed.prgAdvantage_prgAvg_congr_of_support' (Ratchet.expandPRG C.F) oa _ _
        fun o ho => (hspk o ho hℓ hdec (A o) (hq o ho)).2.2.1 (s o) j hj_lt
    have hprf :
        (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o =>
            evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (A o))) =
        (extractPRF C.F encPt).prfAdvantage
          (prefixPrfAvg oa (fun o => hop2PrfT o (s o) j (A o))) :=
      Signed.prfAdvantage_prfAvg_congr_of_support' (extractPRF C.F encPt) oa _ _
        fun o ho => (hspk o ho hℓ hdec (A o) (hq o ho)).2.2.2 (s o) j hj_lt
    rw [hprg, hprf]
  unfold sessionAdvantageBound
  dsimp only at hl1 hl2 hsum ⊢
  rw [hl1, hl2, hsum]

theorem sessBound_eq_signed
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hspk : ∀ o ∈ support oa,
      SpkCostedEvalAgrees C K (ida o) (idb o) ℓ Dh encPt encT decT 0 qep q
        (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).spk) :
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let R := fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q
    sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A =
      uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa ida idb R A
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (Signed.leakUAvgWithSpqr C spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * Signed.hop2TermAvgWithSpqr C spqr ℓ Dh encPt encT decT qep q oa ida idb s A :=
  let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
  sessBound_eq_gen ℓ hℓ D C K Dh encPt encT decT qep q δ oa ida idb s A
    (fun o s' A' => spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep s' A')
    (fun o A' => spkLeakRedU spkLeakRed (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep A')
    (fun o s' j A' => hop2PrgRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encPt encT decT qep s' j A')
    (fun o s' j A' => hop2PrfRedK (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ Dh encT decT qep s' j A')
    hdec hq (fun o ho => (spkCostedEvalAgrees_iff_gen C K (ida o) (idb o) ℓ Dh encPt encT decT 0 qep q _).mp (hspk o ho))

/-- Five-hop session bias bound into `sessionAdvantageBound` for any `SessionCostedReductionFamily`
whose outer reductions satisfy the evaluation-agreement hypotheses. -/
theorem boolBias_mixSpkGen_le_sessionAdvantageBound
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (gameFixedSpk gameU gameR : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (spkLeakT : α → BitVec 256 →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (spkLeakUT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (hop2PrgT : α → BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      PRGScheme.PRGAdversary (BitVec 256 × BitVec 256))
    (hop2PrfT : α → BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (uniformStartT epoch0T : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      (Ratchet.RootKey × BitVec 256) → ProbComp Bool)
    (simT : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT eps0Game hidGame : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hSpkChain :
      𝒟[oa >>= fun o => gameFixedSpk o (A o)].boolBias ≤
        𝒟[oa >>= fun o => gameU o (A o)].boolBias
          + 2 * (extractPRF C.F encPt).prfAdvantage
              (prefixPrfAvg oa (fun o => spkLeakT o (s o) (A o)))
          + 2 * (extractPRF C.F encPt).prfAdvantage
              (prefixPrfAvg oa (fun o => spkLeakUT o (A o)))
          + 2 * (epoch0ChainForgeryTerm C.F q
              + (∑ j ∈ Finset.range spkSwapHybridCount,
                  ((Ratchet.expandPRG C.F).prgAdvantage
                      (prefixPrgAvg oa (fun o => hop2PrgT o (s o) j (A o)))
                    + (extractPRF C.F encPt).prfAdvantage
                      (prefixPrfAvg oa (fun o => hop2PrfT o (s o) j (A o)))))
              + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q
              + spkSwapCreationPointHitTerm Dh q + spkSwapHiddenScalarGuessTerm Dh q))
    (hspk : ∀ o ∈ support oa,
      SpkCostedEvalAgreesGen C K ℓ Dh encPt encT decT 0 q
        (spkLeakT o) (spkLeakUT o) (hop2PrgT o) (hop2PrfT o)
        (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).spk)
    (hUR : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => gameU o (B o)].boolBias ≤
        𝒟[oa >>= fun o => gameR o (RefuseB0.refuseCorrB0 (B o))].boolBias
          + 2 * (rootKdfAsPrg C.F (encPt 0)).prgAdvantage
              (prefixPrgAvg oa fun o rc => uniformStartT o (RefuseB0.refuseCorrB0 (B o)) rc))
    (hRSim : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => gameR o (B o)].boolBias ≤
        𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt C protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 0) 3 (qep + 1) SM.Config.h1 (simT o (B o))].boolBias
          + 2 * (refineConst C Dh encPt q qep δ +
            (𝒟[oa >>= fun o => winT o (B o)] {true} +
             𝒟[oa >>= fun o => eps0Game o (B o)] {true} +
             𝒟[oa >>= fun o => hidGame o (B o)] {true})))
    (hEps0 : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => eps0Game o (B o)] {true} ≤
        (rootKdfAsPrg C.F (encPt 0)).prgAdvantage
          (prefixPrgAvg oa fun o rc => epoch0T o (B o) rc) + q * eps0IdealUnit C.F)
    (hHid : ∀ o ∈ support oa,
      𝒟[hidGame o (RefuseB0.refuseCorrB0 (A o))] {true} ≤
        hiddenSaltBoundV1 C K ℓ Dh encPt encT decT (ida o) (idb o) 0 qep q δ
          (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q)
          (RefuseB0.refuseCorrB0 (A o)))
    (hUE : ∀ o, UniformEpoch0CostedEvalAgreesGen C K (ida o) (idb o) ℓ Dh encPt encT decT 0 q
      (uniformStartT o) (epoch0T o) (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q))
    (hSim : ∀ o, SimFig8CostedEvalAgreesGen C K (ida o) (idb o) ℓ Dh encPt encT decT 0 qep q
      (simT o) (winT o) (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q))
    (hfig8 : ∀ o, (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).fig8 =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT 0 qep q).fig8)
    (hfs : ∀ o, (D C K (ida o) (idb o) Dh encPt encT decT 0 qep q).fs =
      (v1SessionReds ℓ C K (ida o) (idb o) Dh encPt encT decT 0 qep q).fs) :
    𝒟[oa >>= fun o => gameFixedSpk o (A o)].boolBias ≤
      sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A := by
  have hU := boolBias_mixUGen_le_uTermShortMix C K hD hℓ Dh hDh encPt encT decT hinj hdum (0 : Pt)
    qep q hq32 δ oa ida idb (fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q)
    gameU gameR uniformStartT epoch0T simT winT eps0Game hidGame A hq
    hUR hRSim hEps0 hHid hUE hSim hfig8 hfs
  have heq := sessBound_eq_gen ℓ hℓ D C K Dh encPt encT decT qep q δ oa ida idb s A
    spkLeakT spkLeakUT hop2PrgT hop2PrfT hdec hq hspk
  exact (hSpkChain.trans (add_le_add (add_le_add (add_le_add hU le_rfl) le_rfl) le_rfl)).trans_eq
    heq.symm

/-! ## Clamped tracker-halted reduction family -/

/-- Unclamped tracker-halted session reduction family wiring halted outer reductions onto
`v1SessionRedsPaper`. -/
@[nospecialize] def v1SessionRedsHaltedRaw
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionCostedReductionFamily Pt ℓ :=
  fun C K idA idB Dh encPt encT decT lam qep q =>
    { v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q with
      spk := Computational.Proofs.SessionCostedHalt.mkSpkCostedRedsHalted
        (Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg.spkLeakRedRInProgHalted
          (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
        (CryptoVerification.E2E.HeadlineSpk.spkLeakRedUAtomicProg (Pt := Pt) ℓ)
        (fun k =>
          Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrgProgHalted
            (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
        (fun k =>
          Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrfProgHalted
            (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      simFig8 :=
        Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simFig8RedProgHalted
          (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
      simDeliverForge :=
        Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted
          (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
      epoch0Red :=
        Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog.epoch0DistinguisherProgHalted
          C K Dh encPt encT decT idA idB lam ℓ q qep
      uniformStartRed :=
        Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog.uniformStartRedHalted
          C K Dh encPt encT decT idA idB lam ℓ q qep }

/-- Epoch-clamped tracker-halted session reduction family. -/
@[nospecialize] def v1SessionRedsHaltedClamped
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionCostedReductionFamily Pt ℓ :=
  Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily ℓ
    (v1SessionRedsHaltedRaw ℓ)

private theorem v1SessionRedsHaltedRaw_bounded_of_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hqep : qep ≤ q + 4) :
    sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
      (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  have hqep10 : qep ≤ q + 10 := by omega
  have hp := v1SessionRedsPaper_bounded ℓ C K idA idB Dh encPt encT decT lam qep q hqep10
  refine ⟨?_, hp.2.1, hp.2.2.1, ?_, ?_, ?_, ?_,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2⟩
  · exact Computational.Proofs.SessionCostedHalt.mkSpkCostedRedsHalted_bounds
      (Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg.spkLeakRedRInProgHalted_gRedBounded_tight
        (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep hqep10)
      (CryptoVerification.E2E.HeadlineSpk.spkLeakRedUAtomicProg_gRedBounded_tight (Pt := Pt) ℓ q)
      (fun k _ =>
        Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrgProgHalted_gRedBounded_tight
          (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k hqep10)
      (fun k _ =>
        Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrfProgHalted_gRedBounded_tight
          (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k hqep10)
  · exact Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simFig8RedProgHalted_gRedBounded
      (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q hqep10
  · exact Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted_gRedBounded
      (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q hqep10
  · exact Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog.epoch0DistinguisherProgHalted_gRedBounded_succ
      C K Dh encPt encT decT idA idB lam ℓ q qep hqep10
  · exact Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog.uniformStartRedHalted_gRedBounded_succ
      C K Dh encPt encT decT idA idB lam ℓ q qep hqep10

theorem v1SessionRedsHaltedClamped_bounded
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) :
    SessionCostedReductionFamilyBounded ℓ (v1SessionRedsHaltedClamped (Pt := Pt) ℓ) :=
  Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily_bounded ℓ
    (v1SessionRedsHaltedRaw ℓ) (v1SessionRedsHaltedRaw_bounded_of_le ℓ)

private theorem spkCostedEvalAgreesGen_v1SessionRedsHaltedRaw
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let P_s := paramsIdsWithSpqr C spqr idA idB
    SpkCostedEvalAgreesGen C K ℓ Dh encPt encT decT lam q
      (fun s' A' =>
        Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K P_s Dh encPt encT decT qep
          s' A')
      (fun A' =>
        spkLeakRedU (Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K)
          P_s Dh encPt encT decT qep A')
      (fun s' j A' =>
        Computational.Proofs.E2E.HaltedSpkDefs.hop2PrgRedKTrackHalted P_s K ℓ Dh encPt encT decT
          qep s' j A')
      (fun s' j A' =>
        Computational.Proofs.E2E.HaltedSpkDefs.hop2PrfRedKTrackHalted P_s K ℓ Dh encT decT qep s'
          j A')
      (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).spk := by
  dsimp only
  intro hℓ hdec A hq
  have h1 : ∀ s' : BitVec 256,
      evalSpkLeakRed
        (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).spk.spkLeakRed s' A =
      Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K
        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s' A :=
    fun s' =>
      Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg.spkLeakRedRInProgHalted_eval
        (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep s' A hq hℓ
  refine ⟨h1, ?_, ?_, ?_⟩
  · have hfn :
        (fun x => evalSpkLeakRed
          (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).spk.spkLeakRed x A) =
        (fun x => Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K
          (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
          Dh encPt encT decT qep x A) :=
      funext h1
    rw [hfn]
    exact CryptoVerification.E2E.HeadlineSpk.spkLeakRedUAtomicProg_eval (Pt := Pt) ℓ
      (Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K)
      (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
      Dh encPt encT decT qep A
  · intro s' j hj
    dsimp only [v1SessionRedsHaltedRaw]
    rw [Computational.Proofs.SessionCostedHalt.mkSpkCostedRedsHalted_hop2PrgRedK_of_lt _ _ _ _ hj]
    exact
      Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrgProgHalted_eval
        (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep j s' A hdec hj hq hℓ
  · intro s' j hj
    dsimp only [v1SessionRedsHaltedRaw]
    rw [Computational.Proofs.SessionCostedHalt.mkSpkCostedRedsHalted_hop2PrfRedK_of_lt _ _ _ _ hj]
    exact
      Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg.spkHop2PrfProgHalted_eval
        (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep j s' A hdec hj hq hℓ

private theorem uniformEpoch0CostedEvalAgreesGen_v1SessionRedsHaltedRaw
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    let P_v1 := paramsV1 C K idA idB
    let adm := ratchetKeyAdmissible protoSignalCodec decT encT
    UniformEpoch0CostedEvalAgreesGen C K idA idB ℓ Dh encPt encT decT lam q
      (fun B rc =>
        Computational.Proofs.E2E.HaltedSessionChain.uniformStartDistinguisherTrackHalted
          P_v1 K ℓ (configR1OnCurve adm) qep B rc)
      (fun B rc =>
        Computational.Proofs.E2E.HaltedSessionChain.epoch0DistinguisherTrackHalted
          P_v1 K ℓ adm qep B rc)
      (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  dsimp only
  intro hℓ B hq rc
  exact ⟨
    Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog.uniformStartRedHalted_eval_bridge
      C K Dh encPt encT decT idA idB lam ℓ q qep B rc hq hℓ,
    Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog.epoch0DistinguisherProgHalted_eval_bridge
      C K Dh encPt encT decT idA idB lam ℓ q qep B rc hq hℓ⟩

private theorem simFig8CostedEvalAgreesGen_v1SessionRedsHaltedRaw
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    let P_v1 := paramsV1 C K idA idB
    SimFig8CostedEvalAgreesGen C K idA idB ℓ Dh encPt encT decT lam qep q
      (fun B =>
        Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.libsignalToModularSchemeSimHalted
          P_v1 K ℓ Dh encPt encT decT (idsOf idA idB) lam qep B)
      (fun B =>
        Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simCNoneWinEventHalted
          P_v1 K ℓ Dh encPt encT decT (idsOf idA idB) lam qep B)
      (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  dsimp only
  intro hℓ B hq
  exact ⟨
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_queries
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_equalPub
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_sendAtomicShort
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_guardedSMShort
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq,
    (Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_sm_game_eq
      hℓ C K idA idB Dh encPt encT decT lam qep q SM.Config.h1 B hq).symm,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval.simFig8RedProgHalted_simCNoneWinEvent_eq
      hℓ C K idA idB Dh encPt encT decT lam qep q B hq⟩

/-! ### Tracker-Halted Bucket Coupling Helpers (`forgeBucketAdvantagePaper`) -/

open DeliverForge (AdversaryCompDF) in
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState) in
open Proofs.Refinement (KemFailTrackState stepKemFailSend) in
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame (GameSanInv keptInv_send) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling
  (BucketState runBucketDF bucketImplDF_liftM_probComp runBucketDF_transmitQueryDF_inv
   runBucketDF_challQueryDF_inv DFBucketSanInv) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase (semSendTrackHalted) in
private theorem semSendTrackHalted_bucket_dfSanInv
    {ℓ q m qep : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] {tL : Option ℕ} {par : Bool}
    (P : Params Bytes (BitVec 512)) (K : LibsignalSpqrV1.MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (ms : BucketState Pt ℓ) (Q : Party) (m₀ : CBC.Plain ℓ)
    (chal : Option (CBC.Plain ℓ)) (r : Option (BitVec 512)) (hInv : DFBucketSanInv q (m + 1) sC ms) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r) ms),
      DFBucketSanInv q m x.1.2.1.1 x.2 := by
  have hDrawRq : ∀ {α : Type} (k : BitVec 512 → AdversaryCompDF (SimFig8St Pt)
      (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (SimFig8C Pt) α) {x : α × BucketState Pt ℓ},
      x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        ((match r with | some rq => pure rq | none => liftM ($ᵗ (BitVec 512) : ProbComp (BitVec 512))) >>= k) ms) →
      ∃ rq, x ∈ support (runBucketDF P Dh encPt encT lam qep tL par (k rq) ms) := by
    intro α k x hx; cases r with
    | some rq => rw [pure_bind] at hx; exact ⟨rq, hx⟩
    | none =>
      dsimp only [runBucketDF] at hx ⊢
      simp only [simulateQ_bind, StateT.run_bind, bucketImplDF_liftM_probComp, bind_assoc, pure_bind, mem_support_bind_iff] at hx
      obtain ⟨rq, -, hx⟩ := hx; exact ⟨rq, hx⟩
  have hDrawRc : ∀ {α : Type} (k : Option (BitVec 256) → AdversaryCompDF (SimFig8St Pt)
      (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (SimFig8C Pt) α) {x : α × BucketState Pt ℓ},
      x ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        ((match r with | some _ => some <$> (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256))) | none => pure none) >>= k) ms) →
      ∃ rc, x ∈ support (runBucketDF P Dh encPt encT lam qep tL par (k rc) ms) := by
    intro α k x hx; cases r with
    | none => rw [pure_bind] at hx; exact ⟨none, hx⟩
    | some _ =>
      dsimp only [runBucketDF] at hx ⊢
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind, bucketImplDF_liftM_probComp, mem_support_bind_iff] at hx
      obtain ⟨rc, -, hx⟩ := hx; exact ⟨some rc, hx⟩
  rintro ⟨⟨_, ⟨sC₁, _⟩, _⟩, ms₁⟩ hx
  have hm1 : m + 1 ≤ q := hInv.hgame.hm; have hInv0 := hInv.mono (Nat.le_succ m); unfold semSendTrackHalted at hx
  by_cases href : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
    · by_cases hch : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp only [hch, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hx; obtain ⟨rq, hx⟩ := hDrawRq _ hx
        by_cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome = true
        · simp only [hcand, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte] at hx; obtain ⟨rc, hx⟩ := hDrawRc _ hx
          rcases hmk : mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
              BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;> simp only [hmk] at hx
          · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact hInv0
          · have hpost : ∀ (c : Fig8C Pt), GameSanInv q m ms₁.2.1 → c.2.1 ≤ q - m →
                sC₁ = scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq'
                  (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) c →
                DFBucketSanInv q m sC₁ ms₁ := by
              intro c hg' hc hsC₁; subst hsC₁; refine ⟨hg', fun R => ?_, hInv0.hchains, fun wc hwc => ?_⟩
              · unfold scPostSendPure; by_cases hR : R = Q
                · subst hR; simp only [Function.update_self]; exact (keptInv_send (hInv.hkept R)).mono (Nat.mul_le_mul_left 25000 (by omega))
                · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
              · unfold scPostSendPure at hwc; rcases List.mem_cons.mp hwc with rfl | hwc
                · exact hc
                · exact hInv0.hhonest wc hwc
            cases chal with
            | none =>
              simp only [runBucketDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx; obtain ⟨⟨res, ms'⟩, htr, hEq⟩ := hx
              obtain ⟨hg', hc⟩ := runBucketDF_transmitQueryDF_inv P Dh encPt encT lam Q (pub, m₀) rc ms ms' res hInv.hgame htr
              rcases res with _ | c <;> simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
              · rcases hEq with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
              · rcases hEq with ⟨⟨_, ⟨hsC₁, _⟩, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) hsC₁
            | some m₁ =>
              simp only [runBucketDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx; obtain ⟨⟨res, ms'⟩, hch', hEq⟩ := hx
              obtain ⟨hg', hc⟩ := runBucketDF_challQueryDF_inv P Dh encPt encT lam Q (pub, m₀) (pub, m₁) rc ms ms' res hInv.hgame hch'
              rcases res with _ | c <;> simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
              · rcases hEq with ⟨⟨_, ⟨rfl, _⟩, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
              · rcases hEq with ⟨⟨_, ⟨hsC₁, _⟩, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) hsC₁

open DeliverForge (challSimDF'Paper sameHdrScheme forgeGameBucketPaper) in
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC) in
open Proofs.Refinement (KemFailTrackState initKemFailTrack) in
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (semHandleHookDedupS) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle (simDeliverForgeOracleSan) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
  (simDeliverForgeOracleSan_inr_inl_eq simDeliverForgeOracleSan_inr_inr_eq_of_support) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling
  (idsOf_eq_paramsV1_id BucketState bucketImplDF runBucketDF bucketImplDF_liftM_probComp
   forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF runBucketDF_onCr_inv DFBucketSanInv
   dfBucketSanInv_init semRecvHook_bucket_dfSanInv semCorrHookDedup_bucket_dfSanInv simulateQ_runBucketDF_eq_of_inv) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
  (simDeliverForgeOracleSanTrackHalted simDeliverForgeClampSanTrackHalted) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedSanGame
  (simDeliverForgeOracleDedupTrackHalted simDeliverForgeClampDedupTrackHalted) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCoupling
  (simDeliverForgeClampTrackHalted run'_simulateQ_simDeliverForgeOracleDedupTrackHalted_eq) in
private theorem forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClampSanTrackHalted_eq
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) (hq : SM.MakesAtMostQueries A q) :
    let P := paramsV1 C K idA idB; let fig := lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam
    forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par (challSimDF'Paper (2 + 1) (qep + 1)
        (simDeliverForgeClampSanTrackHalted P K ℓ Dh encPt encT decT lam qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q) A)) =
      forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par (challSimDF'Paper (2 + 1) (qep + 1)
        (simDeliverForgeClampTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) A)) := by
  dsimp only []; let P := paramsV1 C K idA idB
  have hDedup : simDeliverForgeClampDedupTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) A =
      simDeliverForgeClampTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) A := by
    unfold simDeliverForgeClampDedupTrackHalted simDeliverForgeClampTrackHalted
    exact bind_congr fun _ => run'_simulateQ_simDeliverForgeOracleDedupTrackHalted_eq P K Dh encPt encT decT lam qep (2 ^ 32) A _
  rw [← hDedup, idsOf_eq_paramsV1_id C K idA idB, forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF, forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF]
  refine bind_congr fun k => bind_congr fun b => ?_; unfold simDeliverForgeClampSanTrackHalted simDeliverForgeClampDedupTrackHalted
  simp only [runBucketDF, simulateQ_bind, StateT.run_bind, bucketImplDF_liftM_probComp, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  have hStepInv : ∀ (m' : ℕ) (t : (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes).Domain)
      (st : (LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) × KemFailTrackState P.C.F) (ms : BucketState Pt ℓ),
      DFBucketSanInv q (m' + 1) st.1.1 ms →
      ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par ((simDeliverForgeOracleDedupTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) (.inr t)).run st) ms),
        DFBucketSanInv q m' x.1.2.1.1 x.2 := by
    rintro m' ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) ⟨⟨sC, ex⟩, tr⟩ ms hInv
    · exact semSendTrackHalted_bucket_dfSanInv P K Dh encPt encT lam sC ex tr ms Q m₀ none r hInv
    · exact semSendTrackHalted_bucket_dfSanInv P K Dh encPt encT lam sC ex tr ms Q m₀ (some m₁) r hInv
    · rintro ⟨⟨_, ⟨sC₁, ex₁⟩, _⟩, ms₁⟩ hx; unfold runBucketDF at hx
      dsimp only [simDeliverForgeOracleDedupTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim] at hx
      simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      obtain ⟨⟨⟨_, _, _⟩, _⟩, hrec, ⟨_, ⟨rfl, rfl⟩, _⟩, rfl⟩ := hx
      exact semRecvHook_bucket_dfSanInv (PQC := BitVec 512) P Dh encPt encT lam decT (2 ^ 32) sC ex ms Q w true hInv _ hrec
    · rintro ⟨⟨_, ⟨sC₁, ex₁⟩, _⟩, ms₁⟩ hx; unfold runBucketDF at hx
      dsimp only [simDeliverForgeOracleDedupTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim] at hx
      simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      obtain ⟨⟨⟨_, _, _⟩, _⟩, hrec, ⟨_, ⟨rfl, rfl⟩, _⟩, rfl⟩ := hx
      exact semRecvHook_bucket_dfSanInv (PQC := BitVec 512) P Dh encPt encT lam decT (2 ^ 32) sC ex ms Q w false hInv _ hrec
    · rintro ⟨⟨_, ⟨sC₁, ex₁⟩, _⟩, ms₁⟩ hx; unfold runBucketDF at hx
      dsimp only [simDeliverForgeOracleDedupTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim] at hx
      simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      obtain ⟨⟨⟨_, _, _⟩, _⟩, hcor, ⟨_, ⟨rfl, rfl⟩, _⟩, rfl⟩ := hx
      exact semCorrHookDedup_bucket_dfSanInv (PQC := BitVec 512) P Dh encPt encT lam sC ex ms Q hInv _ hcor
  have h1 := simulateQ_runBucketDF_eq_of_inv (q := q) (qep := qep) (tL := tL) (par := par) P Dh encPt encT lam
    (simDeliverForgeOracleSanTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q))
    (simDeliverForgeOracleDedupTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32)) (fun st => st.1.1)
    (fun _ => by dsimp only [simDeliverForgeOracleSanTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim])
    (fun _ => by dsimp only [simDeliverForgeOracleDedupTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim])
    (fun m' t st ms hInv' => by
      rcases st with ⟨⟨sC, ex⟩, tr⟩; have hm1 : m' + 1 ≤ q := hInv'.hgame.hm
      rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · rfl
      · rfl
      · have hdl := simDeliverForgeOracleSan_inr_inl_eq P Dh encPt encT decT lam qep (.inl (.inr (Q, w))) (sC, ex)
          (B0 := 25000 * (q - (m' + 1))) (T := 50000 * q) (Kc := 25001 * q + 25000) (Bsk := 25000 * q) (B := 2 ^ 32)
          (by omega) hInv'.hkept (by omega) (fun R g hg => by have := hInv'.hchains R g hg; omega)
        have hpost : (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onDeliverPost = fun _ _ _ ex' => pure ex' := rfl
        dsimp only [simDeliverForgeOracleSan, simDeliverForgeOracleDedup, StateT.run, StateT.mk] at hdl
        unfold semHandleHookDedupS semHandleHookDedup at hdl; dsimp only [] at hdl; rw [hpost] at hdl; simp only [pure_bind, Prod.mk.eta, bind_pure] at hdl
        dsimp only [simDeliverForgeOracleSanTrackHalted, simDeliverForgeOracleDedupTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk]; rw [hdl]; rfl
      · have hij := simDeliverForgeOracleSan_inr_inl_eq P Dh encPt encT decT lam qep (.inr (Q, w)) (sC, ex)
          (B0 := 25000 * (q - (m' + 1))) (T := 50000 * q) (Kc := 25001 * q + 25000) (Bsk := 25000 * q) (B := 2 ^ 32)
          (by omega) hInv'.hkept (by omega) (fun R g hg => by have := hInv'.hchains R g hg; omega)
        dsimp only [simDeliverForgeOracleSan, simDeliverForgeOracleDedup, semHandleHookDedupS, semHandleHookDedup, StateT.run, StateT.mk] at hij
        dsimp only [simDeliverForgeOracleSanTrackHalted, simDeliverForgeOracleDedupTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk]; rw [hij]
      · unfold runBucketDF; dsimp only [simDeliverForgeOracleSanTrackHalted, simDeliverForgeOracleDedupTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim]
        simp only [StateT.run_mk]; rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]; congr 1
        exact simDeliverForgeOracleSan_inr_inr_eq_of_support P Dh encPt encT decT lam qep Q (sC, ex)
          (bucketImplDF P Dh encPt encT lam qep tL par) ms (T := 50000 * q) (Kc := 25001 * q + 25000) (Bsk := 25000 * q) (B := 2 ^ 32)
          fun x hx fig8st hres t_ep v hv => by
            rcases x with ⟨⟨res, ex'⟩, ms'⟩
            obtain ⟨-, hst_eq⟩ := runBucketDF_onCr_inv (PQC := BitVec 512) P Dh encPt encT lam Q ex ex' ms ms' res hInv'.hgame hx
            rw [hst_eq fig8st hres] at hv; exact ((hInv'.hgame.hparty Q).2 t_ep v hv).mono (by omega))
    hStepInv A q ((makesAtMostQueries_iff_isGameQuery A q).mp hq)
    ((initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), []), initKemFailTrack P.C.F pqrKey)
    ({ st := fun _ => (), b := b }, (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB) 25000 lam) k false, none))
    (dfBucketSanInv_init P Dh encPt encT lam q k pqrKey false b none)
  dsimp only [runBucketDF] at h1; rw [h1]

open DeliverForge (AdversaryCompDF) in
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState) in
open Proofs.Refinement (KemFailTrackState DeliverForgeM fig8ToDFImpl) in
private noncomputable def runDFMTrackB {Pt α : Type} {F : ShaCompress} {ℓ : ℕ}
    (m : StateT (LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState F) (DeliverForgeM Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt)) (tr : KemFailTrackState F) :
    AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt)
      (α × ((LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) × KemFailTrackState F)) :=
  (m.run (sC, tr)).run ex >>= fun ⟨⟨a, sC', tr'⟩, ex'⟩ => pure (a, ((sC', ex'), tr'))

open DeliverForge (AdversaryCompDF) in
open Proofs.Refinement (fig8ToDFImpl) in
private theorem fig8ToDFImpl_liftProbB {Pt α : Type} {ℓ : ℕ} (p : ProbComp α) (ex : List (SimFig8C Pt)) :
    let liftProbB : ∀ {ι : Type} {S : OracleSpec ι} {β : Type}, ProbComp β → OracleComp (unifSpec + S) β := fun q => liftM q
    (simulateQ (fig8ToDFImpl Pt ℓ) (liftProbB (S := SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (SimFig8C Pt)) p)).run ex =
      ((liftM p : AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (SimFig8C Pt) α) >>= fun a => pure (a, ex)) := by
  dsimp only []; let liftProbB : ∀ {ι : Type} {S : OracleSpec ι} {β : Type}, ProbComp β → OracleComp (unifSpec + S) β := fun q => liftM q
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (fig8ToDFImpl Pt ℓ) (query (spec := unifSpec + SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl t) >>=
        fun u => liftProbB (S := SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (SimFig8C Pt)) (mx u))).run ex =
      ((query (spec := unifSpec + DeliverForge.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl t) >>= fun u => liftM (mx u)) >>= fun a => pure (a, ex))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    change (StateT.lift (query (spec := unifSpec + DeliverForge.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl t)) >>= fun u => simulateQ (fig8ToDFImpl Pt ℓ) (liftProbB (mx u))).run ex = _
    simp only [StateT.run_bind, LibsignalSim.stateT_lift_run, bind_assoc, pure_bind]; exact bind_congr fun u => ih u

open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState) in
open Proofs.Refinement (KemFailTrackState stepKemFailSend fig8ToDFImpl deliverForgeHook simSendCTrackHalted) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase (semSendTrackHalted) in
private theorem semSendTrackHalted_bucket_deliverForge_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ} (P : Params Bytes (BitVec 512)) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (SimFig8C Pt))
    (tr : KemFailTrackState P.C.F) (Q : Party) (m₀ : CBC.Plain ℓ) (chal : Option (CBC.Plain ℓ)) (r : Option (BitVec 512)) :
    semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      runDFMTrackB (simSendCTrackHalted P K qep fig (deliverForgeHook Pt ℓ) Q m₀ chal r) sC ex tr := by
  have hTrQ : ∀ Q' (m : LibsignalMsgPublicPart × CBC.Plain ℓ) rc (ex' : List (SimFig8C Pt)),
      (simulateQ (fig8ToDFImpl Pt ℓ) (SM.transmitQuery Q' m rc)).run ex' = (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onTr Q' m rc ex' := fun Q' m rc ex' => by
    simp only [SM.transmitQuery, query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, fig8ToDFImpl, deliverForgeSemHook, StateT.run_bind, LibsignalSim.stateT_lift_run, pure_bind, bind_assoc]
    exact bind_congr fun res => by cases res <;> rfl
  have hChQ : ∀ Q' (m₀' m₁' : LibsignalMsgPublicPart × CBC.Plain ℓ) rc (ex' : List (SimFig8C Pt)),
      (simulateQ (fig8ToDFImpl Pt ℓ) (SM.challQuery Q' m₀' m₁' rc)).run ex' = (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onCh Q' m₀' m₁' rc ex' := fun Q' m₀' m₁' rc ex' => by
    simp only [SM.challQuery, query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, fig8ToDFImpl, deliverForgeSemHook, StateT.run_bind, LibsignalSim.stateT_lift_run, pure_bind, bind_assoc]
    exact bind_congr fun res => by cases res <;> rfl
  dsimp only []; unfold semSendTrackHalted runDFMTrackB simSendCTrackHalted scPostSendPure; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases href : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q))
  · simp only [Bool.false_eq_true, ↓reduceIte]; rcases sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp only [StateT.run_pure, pure_bind]
    · dsimp only []; cases hch : (chal.isSome && !(s₁.safeCh 3 Q))
      · simp only [Bool.false_eq_true, ↓reduceIte]; rcases r with _ | rq
        · simp only [deliverForgeHook, StateT.run_bind, LibsignalSim.stateT_lift_run, pure_bind, bind_assoc]
          erw [fig8ToDFImpl_liftProbB]; simp only [bind_assoc, pure_bind]; refine bind_congr fun x => ?_
          cases hcand : (stepKemFailSend P.C.F K tr Q x).cand.isSome
          · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_bind, LibsignalSim.stateT_lift_run, pure_bind]
            rcases mkPub (P := P) sC.base Q x (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
            · dsimp only []; cases chal <;> simp only [StateT.run_bind, LibsignalSim.stateT_lift_run, hTrQ, hChQ, deliverForgeSemHook, pure_bind, bind_assoc]
              all_goals refine bind_congr fun res => ?_; rcases res with _ | c
              · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
              · rcases (sC.kept Q).full with _ | st
                · simp
                · simp; rfl
              · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
              · rcases (sC.kept Q).full with _ | st
                · simp
                · simp; rfl
          · simp only [↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        · simp only [deliverForgeHook, simulateQ_pure, StateT.run_bind, LibsignalSim.stateT_lift_run, pure_bind]
          cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
          · simp only [Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_pure, StateT.run_bind, LibsignalSim.stateT_lift_run, pure_bind, bind_assoc]
            erw [fig8ToDFImpl_liftProbB]; simp only [bind_assoc, pure_bind]; refine bind_congr fun x => ?_
            rcases mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
            · cases chal <;> simp only [StateT.run_bind, LibsignalSim.stateT_lift_run, hTrQ, hChQ, deliverForgeSemHook, pure_bind, bind_assoc]
              all_goals refine bind_congr fun res => ?_; rcases res with _ | c
              · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
              · rcases (sC.kept Q).full with _ | st
                · simp
                · simp; rfl
              · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
              · rcases (sC.kept Q).full with _ | st
                · simp
                · simp; rfl
          · simp only [↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      · simp only [↓reduceIte, StateT.run_pure, pure_bind]
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]

open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState) in
open Proofs.Refinement (KemFailTrackState stepKemFailSend) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling
  (BucketState runBucketDF runBucketDF_bind bucketImplDF_liftM_probComp) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg
  (deliverForgeBucketSemHook deliverForgeBucketSemHookClampInv) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase (semSendTrackHalted) in
private theorem semSendTrackHalted_bucket_preserves_clampInv
    {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ m : ℕ} (P : Params Bytes (BitVec 512)) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (SimFig8C Pt)) (tr : KemFailTrackState P.C.F) (s : BucketState Pt ℓ)
    (Q : Party) (m₀ : CBC.Plain ℓ) (chal : Option (CBC.Plain ℓ)) (r : Option (BitVec 512))
    (hBase : SimBaseClampInv (2 ^ 32) (m + 1) sC.base) (hCell : CellGameClampInv (2 ^ 32) (m + 1) s.2.1) :
    ∀ x ∈ support (runBucketDF P Dh encPt encT lam qep tL par (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r) s),
      SimBaseClampInv (2 ^ 32) m x.1.2.1.1.base ∧ CellGameClampInv (2 ^ 32) m x.2.2.1 := by
  rintro ⟨⟨_, ⟨⟨sC', _⟩, _⟩⟩, s'⟩ hx
  have hmono : SimBaseClampInv (2 ^ 32) m sC.base ∧ CellGameClampInv (2 ^ 32) m s.2.1 := ⟨hBase.mono (Nat.le_succ m), hCell.mono (Nat.le_succ m)⟩
  unfold semSendTrackHalted at hx
  cases href : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q))
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx; rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
    · cases hch : (chal.isSome && !(s₁.safeCh 3 Q))
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, runBucketDF_bind, mem_support_bind_iff] at hx; obtain ⟨⟨rq, s_rq⟩, hrq, hx⟩ := hx
        have hs_rq : s_rq = s := by
          rcases r with _ | _ <;> simp only [runBucketDF, simulateQ_pure, StateT.run_pure, bucketImplDF_liftM_probComp, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hrq
          · obtain ⟨_, _, ⟨_, rfl⟩⟩ := hrq; rfl
          · exact hrq.2
        subst s_rq; dsimp only [] at hx; cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte, runBucketDF_bind, mem_support_bind_iff] at hx; obtain ⟨⟨rc, s_rc⟩, hrc, hx⟩ := hx
          have hs_rc : s_rc = s := by
            rcases r with _ | _ <;> simp only [runBucketDF, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bucketImplDF_liftM_probComp, bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hrc
            · exact hrc.2
            · obtain ⟨_, _, ⟨_, rfl⟩⟩ := hrc; rfl
          subst s_rc; dsimp only [] at hx
          rcases hmk : mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;> simp only [hmk] at hx
          · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
          · rw [runBucketDF_bind, mem_support_bind_iff] at hx; obtain ⟨⟨res, s_res⟩, hres, hx⟩ := hx
            have hHook : CellGameClampInv (2 ^ 32) m s_res.2.1 ∧ ∀ c, res = some c → c.1.1 + m + 1 ≤ 2 ^ 32 ∧ c.2.1 + m + 1 ≤ 2 ^ 32 := by
              rcases chal with _ | m₁
              · refine (deliverForgeBucketSemHookClampInv (PQC := BitVec 512) P Dh encPt encT lam qep (2 ^ 32) tL par).onTr_inv (Q := Q) (msg := (pub, m₀)) (rc := rc) (ex := (ex, s)) hCell (res, (match res with | some c => c :: ex | none => ex, s_res)) ?_
                simp only [deliverForgeBucketSemHook, deliverForgeSemHook, runBucketDF_bind, bind_assoc, mem_support_bind_iff]
                refine ⟨(res, s_res), hres, ?_⟩; rcases res with _ | c <;> simp [runBucketDF, simulateQ_pure, StateT.run_pure]
              · refine (deliverForgeBucketSemHookClampInv (PQC := BitVec 512) P Dh encPt encT lam qep (2 ^ 32) tL par).onCh_inv (Q := Q) (m₀ := (pub, m₀)) (m₁ := (pub, m₁)) (rc := rc) (ex := (ex, s)) hCell (res, (match res with | some c => c :: ex | none => ex, s_res)) ?_
                simp only [deliverForgeBucketSemHook, deliverForgeSemHook, runBucketDF_bind, bind_assoc, mem_support_bind_iff]
                refine ⟨(res, s_res), hres, ?_⟩; rcases res with _ | c <;> simp [runBucketDF, simulateQ_pure, StateT.run_pure]
            rcases res with _ | c <;> simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            · rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact ⟨hBase.mono (Nat.le_succ m), hHook.1⟩
            · rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩
              exact ⟨scPostSendPure_clampInv P Dh encPt encT lam hep m₀ chal.isSome pq' _ c hBase (hHook.2 c rfl), hHook.1⟩
        · simp only [hcand, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
      · simp only [hch, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono
  · simp only [href, ↓reduceIte, runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, ⟨⟨rfl, _⟩, _⟩⟩, rfl⟩; exact hmono

open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState guardC simImplC) in
open Proofs.Refinement (KemFailTrackState stepKemFailDeliver DeliverForgeM deliverForgeHook simSendCTrackHalted simImplCTrackHalted) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling (BucketState bucketImplDF runBucketDF runBucketDF_bind bucketImplDF_inl) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg
  (deliverForgeBucketSemHook deliverForgeBucketSemHookClampInv runBucketDF_semRecvHook runBucketDF_semCorrHook) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase (semSendTrackHalted) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCoupling (simDeliverForgeOracleTrackHalted) in
private theorem simulateQ_runBucketDF_simDeliverForgeOracleTrackHalted_eq
    {Pt α : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ} (P : Params Bytes (BitVec 512)) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) α)
    (m : ℕ) (hm : oa.IsQueryBoundP (isGameQuery (G := SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)) m)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (SimFig8C Pt)) (tr : KemFailTrackState P.C.F) (s : BucketState Pt ℓ)
    (hInv : SimBaseClampInv (2 ^ 32) m sC.base ∧ CellGameClampInv (2 ^ 32) m s.2.1) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam; let fs := lFS P.C P.codec ℓ encT idOf 25000
    runBucketDF P Dh encPt encT lam qep tL par ((simulateQ (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32)) oa).run ((sC, ex), tr)) s =
      runBucketDF P Dh encPt encT lam qep tL par (runDFMTrackB (simulateQ (simImplCTrackHalted P K encT decT qep fig fs (deliverForgeHook Pt ℓ) Dh) oa) sC ex tr) s := by
  dsimp only []
  let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig0 := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam; let fs0 := lFS P.C P.codec ℓ encT idOf0 25000
  let bucketHook := deliverForgeBucketSemHook (PQC := BitVec 512) (ℓ := ℓ) P Dh encPt encT lam qep tL par
  have hHookInv := deliverForgeBucketSemHookClampInv (PQC := BitVec 512) (ℓ := ℓ) P Dh encPt encT lam qep (2 ^ 32) tL par
  have hDFMBind : ∀ {β γ : Type} (m₀ : StateT (LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState P.C.F) (DeliverForgeM Pt ℓ) β)
      (f : β → StateT (LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState P.C.F) (DeliverForgeM Pt ℓ) γ) sC₀ ex₀ tr₀,
      runDFMTrackB (m₀ >>= f) sC₀ ex₀ tr₀ = (runDFMTrackB m₀ sC₀ ex₀ tr₀ >>= fun ⟨a, ⟨⟨sC', ex'⟩, tr'⟩⟩ => runDFMTrackB (f a) sC' ex' tr') := by
    intro β γ m₀ f sC₀ ex₀ tr₀; simp only [runDFMTrackB, StateT.run_bind, bind_assoc, pure_bind]
  have hDFMLiftS : ∀ {β : Type} (m₀ : StateT (LibsignalToModularSchemeSimState Bytes Pt ℓ) (DeliverForgeM Pt ℓ) β)
      (sC₀ : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex₀ : List (Fig8C Pt)) (tr₀ : KemFailTrackState P.C.F),
      runDFMTrackB (do let x ← get; let y ← StateT.lift (m₀.run x.1); set (y.2, x.2); pure y.1) sC₀ ex₀ tr₀ =
        (runDFM m₀ sC₀ ex₀ >>= fun x => pure (x.1, (x.2, tr₀))) := by
    intro β m₀ sC₀ ex₀ tr₀; simp only [runDFMTrackB, runDFM, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, LibsignalSim.stateT_lift_run, pure_bind, bind_assoc]
  induction oa using OracleComp.inductionOn generalizing m sC ex tr s with
  | pure a => simp only [runBucketDF, runDFMTrackB, simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind qy u ih =>
    rw [isQueryBoundP_query_bind_iff] at hm; rcases hm with ⟨hq0, hu⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, hDFMBind, runBucketDF_bind, runBucketDF_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift, MonadLift.monadLift]
    rcases qy with n | t
    · simp only [isGameQuery, ↓reduceIte] at hu
      have hinlEq : (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) (.inl n)).run ((sC, ex), tr) =
          runDFMTrackB (simImplCTrackHalted P K encT decT qep fig0 fs0 (deliverForgeHook Pt ℓ) Dh (.inl n)) sC ex tr := by
        have hinl : (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) (.inl n)).run ((sC, ex), tr) =
            (fun u => (u, ((sC, ex), tr))) <$> query (spec := unifSpec + DeliverForge.specDF (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n) := by
          dsimp only [simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim]; simp [StateT.run_lift]
        rw [hinl]; dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, deliverForgeHook, runDFMTrackB]
        rw [LibsignalSim.stateT_lift_run, StateT.run_bind]; erw [fig8ToDFImpl_liftProbB]
        simp only [StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]; rfl
      rw [← hinlEq]; refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨r, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
      have hInlB : runBucketDF P Dh encPt encT lam qep tL par ((simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) (.inl n)).run ((sC, ex), tr)) s =
          (query (spec := unifSpec) n >>= fun r => pure ((r, ((sC, ex), tr)), s)) := by
        dsimp only [simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim]
        change (bucketImplDF P Dh encPt encT lam qep tL par (.inl n) s >>= fun ⟨r, s₁⟩ => pure ((r, ((sC, ex), tr)), s₁)) = _
        rw [bucketImplDF_inl]; simp only [bind_assoc, pure_bind]
      rw [hInlB] at hmem; simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, ⟨_, ⟨⟨rfl, rfl⟩, rfl⟩⟩, rfl⟩ := hmem; exact ih r m (hu r) _ _ _ _ hInv
    · simp only [isGameQuery, ↓reduceIte] at hq0 hu
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hq0.resolve_left (by decide); omega⟩
      have hep : ∀ R, sC.base.mir.epoch R + 1 ≤ 2 ^ 32 := fun R => by have := hInv.1.hep R; omega
      have hch : ∀ R, ∀ g ∈ sC.base.chains R, g.epoch ≤ 2 ^ 32 := fun R g hg => by have := hInv.1.hch R g hg; omega
      rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · change (runBucketDF P Dh encPt encT lam qep tL par (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ none r) s >>= _) =
          (runBucketDF P Dh encPt encT lam qep tL par (runDFMTrackB (simSendCTrackHalted P K qep fig0 (deliverForgeHook Pt ℓ) Q m₀ none r) sC ex tr) s >>= _)
        rw [← semSendTrackHalted_bucket_deliverForge_eq]
        exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem =>
          ih res m' (by simpa using hu res) sC' ex' tr' s' (semSendTrackHalted_bucket_preserves_clampInv P K Dh encPt encT lam qep tL par sC ex tr s Q m₀ none r hInv.1 hInv.2 _ hmem)
      · change (runBucketDF P Dh encPt encT lam qep tL par (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ (some m₁) r) s >>= _) =
          (runBucketDF P Dh encPt encT lam qep tL par (runDFMTrackB (simSendCTrackHalted P K qep fig0 (deliverForgeHook Pt ℓ) Q m₀ (some m₁) r) sC ex tr) s >>= _)
        rw [← semSendTrackHalted_bucket_deliverForge_eq]
        exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem =>
          ih res m' (by simpa using hu res) sC' ex' tr' s' (semSendTrackHalted_bucket_preserves_clampInv P K Dh encPt encT lam qep tL par sC ex tr s Q m₀ (some m₁) r hInv.1 hInv.2 _ hmem)
      · have hStep := semHandleHook_deliverForge_eq (PQC := BitVec 512) P Dh encPt encT decT lam qep (2 ^ 32) (.inl (.inl (.inr (Q, w)))) sC ex (by omega) hep hch (fun _ => Or.inl (Nat.le_refl _))
        have hp : (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onDeliverPost = fun _ _ _ ex₁ => pure ex₁ := rfl
        unfold semHandleHook at hStep; dsimp only [simImplC, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim] at hStep; rw [hp] at hStep; simp only [pure_bind, Prod.mk.eta, bind_pure] at hStep
        have hRhs : runDFMTrackB (simImplCTrackHalted P K encT decT qep fig0 fs0 (deliverForgeHook Pt ℓ) Dh (.inr (.inl (.inl (.inr (Q, w)))))) sC ex tr =
          (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) (.inr (.inl (.inl (.inr (Q, w)))))).run ((sC, ex), tr) := by
          dsimp only [simImplCTrackHalted, simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk]
          have hget : runDFMTrackB (get : StateT _ (DeliverForgeM Pt ℓ) _) sC ex tr = pure ((sC, tr), ((sC, ex), tr)) := rfl
          rw [hDFMBind]; change (runDFMTrackB get sC ex tr >>= _) = _; rw [hget, pure_bind]; dsimp only []; rw [hDFMBind]; erw [hDFMLiftS (guardC _)]; rw [← hStep, bind_assoc]
          refine bind_congr fun ⟨res, sC₁, ex₁⟩ => ?_; simp only [pure_bind]
          suffices ∀ j? : Option ℕ,
              runDFMTrackB (match res, j? with | some (.accepted _ _ _), some j => do modify fun x : LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState P.C.F => (x.1, stepKemFailDeliver P.C.F K x.2 Q j); pure res | _, _ => pure res) sC₁ ex₁ tr =
              pure (res, (sC₁, ex₁), match res, j? with | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j | _, _ => tr) from
            this (List.findIdx? (fun wc : Bytes × SimFig8C Pt => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) sC.base.honest.reverse)
          intro j?; rcases res with _ | (_ | ⟨t', i', pm'⟩)
          · simp only [runDFMTrackB, StateT.run_pure, pure_bind]
          · simp only [runDFMTrackB, StateT.run_pure, pure_bind]
          · rcases j? with _ | j
            · simp only [runDFMTrackB, StateT.run_pure, pure_bind]
            · have hmod : (modify (fun x : LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState P.C.F => (x.1, stepKemFailDeliver P.C.F K x.2 Q j)) : StateT _ (DeliverForgeM Pt ℓ) PUnit).run (sC₁, tr) = pure ((), (sC₁, stepKemFailDeliver P.C.F K tr Q j)) := rfl
              simp only [runDFMTrackB, StateT.run_bind, hmod, pure_bind, StateT.run_pure]
        rw [hRhs]; refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
        dsimp only [simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk] at hmem
        rw [runBucketDF_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨⟨res₁, sC₁, ex₁⟩, s₁⟩, hrec, htail⟩ := hmem
        simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        rcases htail with ⟨⟨h1, ⟨h2, h3⟩, _⟩, h5⟩; subst res sC' ex' s'
        have hmem' : (res₁, (sC₁, (ex₁, s₁))) ∈ support (semRecvHook P Dh encPt encT decT lam bucketHook qep (2 ^ 32) sC (ex, s) Q w true) := by
          rw [← runBucketDF_semRecvHook (PQC := BitVec 512) P Dh encPt encT decT lam qep (2 ^ 32) tL par sC ex s Q w true, support_map]; exact ⟨((res₁, (sC₁, ex₁)), s₁), hrec, rfl⟩
        exact ih res₁ m' (by simpa using hu res₁) sC₁ ex₁ tr' s₁ (semRecvHook_preserves_clampInv P Dh encPt encT decT lam hHookInv m' qep (Nat.le_refl _) sC (ex, s) Q w true hInv.1 hInv.2 _ hmem')
      · have hStep := semHandleHook_deliverForge_eq (PQC := BitVec 512) P Dh encPt encT decT lam qep (2 ^ 32) (.inl (.inr (Q, w))) sC ex (by omega) hep hch (fun _ => Or.inl (Nat.le_refl _))
        dsimp only [semHandleHook, simImplC, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim] at hStep
        have hRhs : runDFMTrackB (simImplCTrackHalted P K encT decT qep fig0 fs0 (deliverForgeHook Pt ℓ) Dh (.inr (.inl (.inr (Q, w))))) sC ex tr =
          (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) (.inr (.inl (.inr (Q, w))))).run ((sC, ex), tr) := by
          dsimp only [simImplCTrackHalted, simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk]; erw [hDFMLiftS (guardC _)]; rw [← hStep]
        rw [hRhs]; refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
        dsimp only [simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk] at hmem
        rw [runBucketDF_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨⟨res₁, sC₁, ex₁⟩, s₁⟩, hrec, htail⟩ := hmem
        simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        rcases htail with ⟨⟨h1, ⟨h2, h3⟩, h4⟩, h5⟩; subst res sC' ex' tr' s'
        have hmem' : (res₁, (sC₁, (ex₁, s₁))) ∈ support (semRecvHook P Dh encPt encT decT lam bucketHook qep (2 ^ 32) sC (ex, s) Q w false) := by
          rw [← runBucketDF_semRecvHook (PQC := BitVec 512) P Dh encPt encT decT lam qep (2 ^ 32) tL par sC ex s Q w false, support_map]; exact ⟨((res₁, (sC₁, ex₁)), s₁), hrec, rfl⟩
        exact ih res₁ m' (by simpa using hu res₁) sC₁ ex₁ tr s₁ (semRecvHook_preserves_clampInv P Dh encPt encT decT lam hHookInv m' qep (Nat.le_refl _) sC (ex, s) Q w false hInv.1 hInv.2 _ hmem')
      · have hStep := semHandleHook_deliverForge_eq (PQC := BitVec 512) P Dh encPt encT decT lam qep (2 ^ 32) (.inr Q) sC ex (by omega) hep hch (fun _ => Or.inl (Nat.le_refl _))
        dsimp only [semHandleHook, simImplC, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim] at hStep
        have hRhs : runDFMTrackB (simImplCTrackHalted P K encT decT qep fig0 fs0 (deliverForgeHook Pt ℓ) Dh (.inr (.inr Q))) sC ex tr =
          (simDeliverForgeOracleTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) (.inr (.inr Q))).run ((sC, ex), tr) := by
          dsimp only [simImplCTrackHalted, simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk]; erw [hDFMLiftS (guardC _)]; rw [← hStep]
        rw [hRhs]; refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ⟨⟨sC', ex'⟩, tr'⟩⟩, s'⟩ hmem => ?_
        dsimp only [simDeliverForgeOracleTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, StateT.run, StateT.mk] at hmem
        rw [runBucketDF_bind, mem_support_bind_iff] at hmem; obtain ⟨⟨⟨res₁, sC₁, ex₁⟩, s₁⟩, hrec, htail⟩ := hmem
        simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        rcases htail with ⟨⟨h1, ⟨h2, h3⟩, h4⟩, h5⟩; subst res sC' ex' tr' s'
        have hmem' : (res₁, (sC₁, (ex₁, s₁))) ∈ support (semCorrHook P Dh encT bucketHook sC (ex, s) Q) := by
          rw [← runBucketDF_semCorrHook (PQC := BitVec 512) P Dh encPt encT lam qep tL par sC ex s Q, support_map]; exact ⟨((res₁, (sC₁, ex₁)), s₁), hrec, rfl⟩
        exact ih res₁ m' (by simpa using hu res₁) sC₁ ex₁ tr s₁ (semCorrHook_preserves_clampInv P Dh encT hHookInv m' sC (ex, s) Q hInv.1 hInv.2 _ hmem')

open DeliverForge (AdversaryCompDF challSimDF'Paper sameHdrScheme forgeGameBucketPaper forgeBucketAdvantagePaper) in
open CryptoGames.Ratchet.LibsignalSimC (initSimC) in
open Proofs.Refinement (initKemFailTrack deliverForgeHook simImplCTrackHalted simRunCTrackHaltedWith simDeliverForgeTrackHalted) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling
  (idsOf_eq_paramsV1_id runBucketDF runBucketDF_bind bucketImplDF_liftM_probComp forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase (simDeliverForgeClampSanQTrackHalted) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCoupling (simDeliverForgeClampTrackHalted) in
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted (simDeliverForgeRedProgHalted simDeliverForgeRedProgHalted_eval_sanQ) in
private theorem forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeRedProgHalted_eq
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let P := paramsV1 C K idA idB; let fig := lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam
    forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par (challSimDF'Paper (2 + 1) (qep + 1)
        ((simDeliverForgeRedProgHalted ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ())) =
      forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par (challSimDF'Paper (2 + 1) (qep + 1)
        (simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep A)) := by
  dsimp only []; let P := paramsV1 C K idA idB
  let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig0 := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam; let fs0 := lFS P.C P.codec ℓ encT idOf0 25000
  have hClampEq : forgeGameBucketPaper (lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam) 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1) (simDeliverForgeClampTrackHalted P K Dh encPt encT decT lam qep (2 ^ 32) A)) =
      forgeGameBucketPaper (lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam) 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1) (simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep A)) := by
    have hid : idsOf idA idB = idOf0 := idsOf_eq_paramsV1_id C K idA idB
    rw [hid, forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF, forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF]
    refine bind_congr fun k => bind_congr fun b => ?_
    have hTrEq : simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf0 lam qep A =
        ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
            AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (SimFig8C Pt) (BitVec 256)) >>=
          fun pqrKey => runDFMTrackB (simulateQ (simImplCTrackHalted P K encT decT qep fig0 fs0 (deliverForgeHook Pt ℓ) Dh) A)
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) [] (initKemFailTrack P.C.F pqrKey) >>= fun r => pure r.1) := by
      unfold simDeliverForgeTrackHalted simRunCTrackHaltedWith; dsimp only [deliverForgeHook, fig0, fs0]
      rw [StateT.run'_eq, StateT.run_bind]; erw [fig8ToDFImpl_liftProbB]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun pqrKey => ?_; dsimp only [runDFMTrackB]
      simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rw [hTrEq]; unfold simDeliverForgeClampTrackHalted
    simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, runBucketDF_bind, bind_assoc]
    simp only [runBucketDF, bucketImplDF_liftM_probComp, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    refine bind_congr fun pqrKey => ?_; have hqB : q + 3 ≤ 2 ^ 32 := by omega
    have hSim := simulateQ_runBucketDF_simDeliverForgeOracleTrackHalted_eq P K Dh encPt encT decT lam qep tL par A q ((makesAtMostQueries_iff_isGameQuery A q).mp hq)
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) [] (initKemFailTrack P.C.F pqrKey)
      ({ st := fun _ => (), b := b }, (SM.initState fig0 k false, none))
      ⟨simBaseClampInv_init (2 ^ 32) q _ _ hqB, cellGameClampInv_init P Dh encPt encT lam idOf0 (2 ^ 32) q k false hqB⟩
    unfold runBucketDF at hSim; rw [hSim]
  rw [simDeliverForgeRedProgHalted_eval_sanQ ℓ C K idA idB Dh encPt encT decT lam qep q hℓ A hq]
  dsimp only [simDeliverForgeClampSanQTrackHalted, forgeBucketAdvantagePaper]
  rw [forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClampSanTrackHalted_eq C K idA idB Dh encPt encT decT lam qep q tL par A hq, hClampEq]

private theorem hiddenSalt_v1SessionRedsHaltedRaw_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hK_tot : Encaps1Total K)
    (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey)
    (hz : ∀ x, Dh.dh x 0 = 0) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q) :
    let P_v1 := paramsV1 C K idA idB
    𝒟[Proofs.Refinement.hiddenSaltGameTrackHalted P_v1 K ℓ Dh encPt encT decT (idsOf idA idB)
        lam qep (RefuseB0.refuseCorrB0 A)] {true} ≤
      hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ
        (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q)
        (RefuseB0.refuseCorrB0 A) := by
  have hA_ref : SM.MakesAtMostQueries (RefuseB0.refuseCorrB0 A) q := by
    rw [refuseCorrB0_eq]
    exact RefuseCorrB0.refuseCorrB0_queries A q hq
  have hq_df :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted_makesAtMostQueriesDF
      C K idA idB Dh encPt encT decT lam qep q (RefuseB0.refuseCorrB0 A) hA_ref
  exact hiddenSaltTermTrackHalted_le_hiddenSaltBoundV1_of_dfReds
    C K hK_tot idA idB Dh encPt encT decT lam qep q hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q) A hq
    hq_df
    (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted_sendAtomicShortDF
      hℓ C K idA idB Dh encPt encT decT lam qep q _ hA_ref)
    (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.simDeliverForgeRedProgHalted_guardedSMDFShort
      hℓ C K idA idB Dh encPt encT decT lam qep q _ hA_ref)
    (fun t _ tL _ => le_of_eq
      (Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHalted.forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeRedProgHalted_eq
        hℓ C K idA idB Dh encPt encT decT lam qep q tL t _ hA_ref hq32).symm)
    (fun tL _ par => le_of_eq
      (forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeRedProgHalted_eq
        hℓ C K idA idB Dh encPt encT decT lam qep q tL par _ hA_ref hq32).symm)
    (v1SessionRedsPaper_challSimDF_eval
      ℓ hℓ C K idA idB Dh encPt encT decT lam qep q _ hq_df)
    rfl
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ _ => rfl)

private theorem boolBias_mixRTrackHalted_le_v1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hK_tot : Encaps1Total K)
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
    let adm := ratchetKeyAdmissible protoSignalCodec decT encT
    𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.libsignalSessionPqrOf
            Z.F K
            (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam)
            3 qep (configR1OnCurve adm) (A o)].boolBias ≤
      𝒟[oa >>= fun o =>
          SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
            3 (qep + 1) SM.Config.h1
            (Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.libsignalToModularSchemeSimHalted
              (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT
              (idsOf (ida o) (idb o)) lam qep (A o))].boolBias
        + 2 * (refineConst Z Dh encPt q qep δ +
          (𝒟[oa >>= fun o =>
              Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simCNoneWinEventHalted
                (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT
                (idsOf (ida o) (idb o)) lam qep (A o)] {true} +
           𝒟[oa >>= fun o =>
              Computational.Proofs.E2E.HaltedSessionChain.eps0EventTrackHalted
                (paramsV1 Z K (ida o) (idb o)) K ℓ encPt lam adm qep (A o)] {true} +
           𝒟[oa >>= fun o =>
              Proofs.Refinement.hiddenSaltGameTrackHalted
                (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT
                (idsOf (ida o) (idb o)) lam qep (A o)] {true})) := by
  intro adm
  refine (boolBias_le_add_two_mul_boolDist _ _).trans (add_le_add le_rfl ?_)
  refine mul_le_mul_right ?_ 2
  refine Signed.boolDist_bind_le_add3 _ _ _ _ _ _ _ fun o => ?_
  have hL : LengthsOk (paramsV1 Z K (ida o) (idb o)) ℓ :=
    HeadlineV1.lengthsOk_paramsIdsWithSpqr_v1 Z K (ida o) (idb o) ℓ hℓ
  have hrt : Proofs.RoundTrip.RtHyp (paramsV1 Z K (ida o) (idb o)) ℓ :=
    ⟨signalRoundTripShort_proto, hL, signalEncodeFits32_proto⟩
  have hS : Corr.SpqrSendCorrectQ (paramsV1 Z K (ida o) (idb o)).spqr q :=
    CryptoVerification.SpqrV1Sync.SendTotal.spqrV1SessionB_sendCorrectQ Z.F K hK_tot q (by omega)
  refine (Proofs.Refinement.sim_game_boolDist_le_C_trackHalted
    (paramsV1 Z K (ida o) (idb o)) K ℓ Dh hDh encPt encT decT
    hX hdec hD hrt hinj hdum hz (idsOf (ida o) (idb o)) ⟨rfl, rfl⟩
    lam qep q hS (by omega) δ hδ (A o) (hq o)).trans_eq ?_
  have hwin :
      Proofs.Refinement.simCNoneWinEventTrackHalted (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt
        encT decT (idsOf (ida o) (idb o)) lam qep (A o) =
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simCNoneWinEventHalted
        (paramsV1 Z K (ida o) (idb o)) K ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) lam qep
        (A o) := rfl
  have heps :
      Proofs.Refinement.eps0EventTrackHalted (paramsV1 Z K (ida o) (idb o)) K ℓ encPt lam
        (ratchetKeyAdmissible (paramsV1 Z K (ida o) (idb o)).codec decT encT) qep (A o) =
      Computational.Proofs.E2E.HaltedSessionChain.eps0EventTrackHalted
        (paramsV1 Z K (ida o) (idb o)) K ℓ encPt lam adm qep (A o) := rfl
  have hC : (paramsV1 Z K (ida o) (idb o)).C = Z := rfl
  rw [hwin, heps, hC]
  unfold refineConst Proofs.Refinement.hiddenSaltTermTrackHalted
  ring

private theorem sessionAdvantageBound_min_le_clamp
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    sessionAdvantageBound ℓ D C K Dh encPt encT decT (min qep (q + 4)) q δ oa ida idb s A ≤
      sessionAdvantageBound ℓ
        (Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily ℓ D)
        C K Dh encPt encT decT qep q δ oa ida idb s A := by
  by_cases hqep : qep ≤ q + 4
  · rw [Nat.min_eq_left hqep,
      Computational.Proofs.SessionCostedHalt.sessionAdvantageBound_clampSessionCostedReductionFamily_eq_of_le
        ℓ D C K Dh encPt encT decT hqep δ oa ida idb s A]
  · have hgt : q + 4 < qep := Nat.lt_of_not_ge hqep
    rw [Nat.min_eq_right (Nat.le_of_lt hgt)]
    let D' : SessionCostedReductionFamily Pt ℓ :=
      fun C' K' idA' idB' Dh' encPt' encT' decT' lam' _ q' =>
        Computational.Proofs.SessionCostedHalt.clampSessionCostedReductions (q' + 4)
          (D C' K' idA' idB' Dh' encPt' encT' decT' lam' (q' + 4) q')
    have hle :
        sessionAdvantageBound ℓ D' C K Dh encPt encT decT (q + 4) q δ oa ida idb s A ≤
          sessionAdvantageBound ℓ D' C K Dh encPt encT decT qep q δ oa ida idb s A := by
      unfold sessionAdvantageBound
      dsimp only [D']
      have hu := Computational.Proofs.SessionCostedHalt.uniformStartMixtureBound_mono_qep
        C K ℓ Dh encPt encT decT (0 : Pt) (Nat.le_of_lt hgt) q δ oa ida idb
        (fun o => D' C K (ida o) (idb o) Dh encPt encT decT 0 qep q) A
      gcongr
    have heqL :
        sessionAdvantageBound ℓ D' C K Dh encPt encT decT (q + 4) q δ oa ida idb s A =
          sessionAdvantageBound ℓ D C K Dh encPt encT decT (q + 4) q δ oa ida idb s A := by
      unfold sessionAdvantageBound
      dsimp only [D']
      simp only [Computational.Proofs.SessionCostedHalt.clampSessionCostedReductions_spk]
      rw [Computational.Proofs.SessionCostedHalt.uniformStartMixtureBound_clampSessionCostedReductions_eq
        C K ℓ Dh encPt encT decT (0 : Pt) le_rfl q δ oa ida idb
        (fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 (q + 4) q) A]
    have heqR :
        sessionAdvantageBound ℓ D' C K Dh encPt encT decT qep q δ oa ida idb s A =
          sessionAdvantageBound ℓ
            (Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily ℓ D)
            C K Dh encPt encT decT qep q δ oa ida idb s A := by
      unfold sessionAdvantageBound
      dsimp only [D']
      simp only [Computational.Proofs.SessionCostedHalt.clampSessionCostedReductionFamily_of_gt
        ℓ D C K _ _ Dh encPt encT decT _ hgt]
    rw [← heqL, ← heqR]
    exact hle

/-- Tracker-halted single-session 5-hop bias bound (with zero `sessionKemFailProb` slack) into
`sessionAdvantageBound` on `v1SessionRedsHaltedClamped ℓ`. -/
theorem boolBias_gameRTrackHalted_session_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt)
    (hK : Encaps1Total K) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hℓ : ℓ < 10 ^ 6) (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hdum : ∀ T, encT T ≠ dummyKey)
    (hz : ∀ x, Dh.dh x 0 = 0) (hker : DhKerUniform Dh)
    (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
            C.F K
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) (ida o) (idb o))
              ℓ (s o))
            3 qep (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
      sessionAdvantageBound ℓ (v1SessionRedsHaltedClamped (Pt := Pt) ℓ)
        C K Dh encPt encT decT qep q δ oa ida idb s A := by
  let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
  let adm := ratchetKeyAdmissible protoSignalCodec decT encT
  have hinj : Function.Injective encT := fun x y h =>
    Option.some.inj (by rw [← hdec x, ← hdec y, h])
  have hℓ31 : ℓ < 2 ^ 31 := by omega
  have h_clamp :
      𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
            C.F K
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o))
            3 qep (configRefuseEarlyBobCorr decT encT) (A o)] =
      𝒟[oa >>= fun o =>
        Prod.fst <$>
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
            C.F K
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o))
            3 (min qep (q + 4)) (configRefuseEarlyBobCorr decT encT) (A o)] :=
    evalDist_mixGameRTrackHalted_min_eq
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
      C.F K (fun o => paramsIdsWithSpqr C spqr (ida o) (idb o)) (fun _ => rfl)
      ℓ 3 qep q s (configRefuseEarlyBobCorr decT encT) oa A hA
  rw [h_clamp]
  set qep_c := min qep (q + 4) with hqep_c
  clear_value qep_c
  refine (boolBias_mixSpkGen_le_sessionAdvantageBound
    ℓ hℓ (v1SessionRedsHaltedRaw ℓ) C K hD Dh hDh encPt encT decT hdec hinj hdum
    qep_c q hq32 δ oa ida idb s
    (fun o B =>
      Prod.fst <$>
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.sampledSessionPqrOf
          C.F K
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o))
          3 qep_c (configRefuseEarlyBobCorr decT encT) B)
    (fun o B =>
      Prod.fst <$>
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
          Computational.Proofs.E2E.HaltedSessionChain.pqrOfSessionU
          C.F K
          (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ)
          3 qep_c (configRefuseEarlyBobCorr decT encT) B)
    (fun o B =>
      Prod.fst <$>
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.gameRTrackHalted
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.libsignalSessionPqrOf
          C.F K
          (libsignalSessionScheme (paramsV1 C K (ida o) (idb o)) ℓ encPt 0)
          3 qep_c (configR1OnCurve adm) B)
    (fun o s' B =>
      Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep_c s' B)
    (fun o B =>
      spkLeakRedU (Computational.Proofs.E2E.HaltedSpkDefs.spkLeakRedTrackHalted K)
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep_c B)
    (fun o s' j B =>
      Computational.Proofs.E2E.HaltedSpkDefs.hop2PrgRedKTrackHalted
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) K ℓ Dh encPt encT decT qep_c s' j B)
    (fun o s' j B =>
      Computational.Proofs.E2E.HaltedSpkDefs.hop2PrfRedKTrackHalted
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) K ℓ Dh encT decT qep_c s' j B)
    (fun o B rc =>
      Computational.Proofs.E2E.HaltedSessionChain.uniformStartDistinguisherTrackHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ (configR1OnCurve adm) qep_c B rc)
    (fun o B rc =>
      Computational.Proofs.E2E.HaltedSessionChain.epoch0DistinguisherTrackHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ adm qep_c B rc)
    (fun o B =>
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.libsignalToModularSchemeSimHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) 0 qep_c B)
    (fun o B =>
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted.simCNoneWinEventHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) 0 qep_c B)
    (fun o B =>
      Computational.Proofs.E2E.HaltedSessionChain.eps0EventTrackHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ encPt (0 : Pt) adm qep_c B)
    (fun o B =>
      Proofs.Refinement.hiddenSaltGameTrackHalted
        (paramsV1 C K (ida o) (idb o)) K ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) 0 qep_c B)
    A hA
    (Computational.Proofs.E2E.HaltedSpkSession.boolBias_mixSpkTrackHaltedWithSpqr_le_of_support
      C K hℓ31 Dh hDh encPt encT decT hX hdec hz qep_c q oa ida idb s A
      (fun o x P₁ P₂ => hker (s o) x P₁ P₂) hA)
    (fun o _ =>
      spkCostedEvalAgreesGen_v1SessionRedsHaltedRaw ℓ C K (ida o) (idb o) Dh encPt encT decT
        0 qep_c q)
    (fun B _ => by
      have href : ∀ o, (B o).refuseCorrB0 = RefuseB0.refuseCorrB0 (B o) :=
        fun o => (refuseCorrB0_eq (B o)).symm
      refine (Computational.Proofs.E2E.HaltedSessionChain.boolBias_mixUTrackHaltedWithSpqr_le
        C K spqr encPt (0 : Pt) encT decT qep_c oa ida idb B).trans_eq ?_
      simp_rw [href]
      rfl)
    (fun B hB =>
      boolBias_mixRTrackHalted_le_v1 C K hK hℓ Dh hDh encPt encT decT
        hX hdec hD hinj hdum hz (0 : Pt) qep_c q hq32 δ hδ oa ida idb B hB)
    (fun B hB =>
      Computational.Proofs.E2E.HaltedSessionChain.evalDist_mixEps0TrackHalted_le_v1
        C K hℓ Dh encPt encT decT hX hdec hinj hdum (0 : Pt) qep_c q oa ida idb B hB)
    (fun o ho =>
      hiddenSalt_v1SessionRedsHaltedRaw_le ℓ C K hK (ida o) (idb o) Dh encPt encT
        decT (0 : Pt) qep_c q hℓ hDh hX hdec hinj hdum hz hD hq32 δ hδ (A o) (hA o ho))
    (fun o =>
      uniformEpoch0CostedEvalAgreesGen_v1SessionRedsHaltedRaw ℓ C K (ida o) (idb o) Dh encPt
        encT decT (0 : Pt) qep_c q)
    (fun o =>
      simFig8CostedEvalAgreesGen_v1SessionRedsHaltedRaw ℓ C K (ida o) (idb o) Dh encPt
        encT decT (0 : Pt) qep_c q)
    (fun o =>
      (v1SessionRedsPaper_fig8 ℓ C K (ida o) (idb o) Dh encPt encT decT 0 qep_c q).trans
        (v1SessionReds_fig8 ℓ C K (ida o) (idb o) Dh encPt encT decT 0 qep_c q).symm)
    (fun o =>
      (v1SessionRedsPaper_fs ℓ C K (ida o) (idb o) Dh encPt encT decT 0 qep_c q).trans
        (v1SessionReds_fs ℓ C K (ida o) (idb o) Dh encPt encT decT 0 qep_c q).symm)).trans ?_
  rw [hqep_c]
  exact sessionAdvantageBound_min_le_clamp ℓ (v1SessionRedsHaltedRaw ℓ)
    C K Dh encPt encT decT qep q δ oa ida idb s A

/-- Single-session security (`SessionSecure ℓ`, Lemma 2) with costed reductions. -/
theorem session_secure_proof
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) :
    SessionSecure (Pt := Pt) ℓ := by
  refine ⟨v1SessionRedsHaltedClamped (Pt := Pt) ℓ, v1SessionRedsHaltedClamped_bounded ℓ, ?_⟩
  intro C K Dh encPt encT decT hK hD hℓ hDh hX hdec hdum hz hker qep q hq32 δ hδ
    α oa ida idb s A hA
  exact
    (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.boolBias_session_le_trackHalted_add_two_mul_sessionKemFailProb
      C K ℓ decT encT qep oa ida idb s A).trans
      (add_le_add
        (boolBias_gameRTrackHalted_session_le ℓ C K Dh encPt encT decT
          hK hD hℓ hDh hX hdec hdum hz hker qep q hq32 δ hδ oa ida idb s A hA)
        le_rfl)

end CryptoVerification.E2E

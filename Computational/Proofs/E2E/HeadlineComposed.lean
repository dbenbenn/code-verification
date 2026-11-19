/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedDF -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Fig8Atomic
import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimC
public import Computational.Proofs.SpecLemmas.Session.StatementComposed -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SignedSession
import Computational.Proofs.CryptoGames.SM.BucketAuthBridge
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.E2E.HeadlineSpkSession
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Queries
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.E2E.SignedCoin
import Computational.Proofs.E2E.SignedFig8
import Computational.Proofs.E2E.SignedThm1
import Computational.Proofs.E2E.SignedThm8
import Computational.Proofs.E2E.Fig8Stage2MixHelpers
import Computational.Proofs.SessionCostedDFStage2Auth
import Computational.Proofs.SessionCostedDFStage2Priv
import Computational.Proofs.SessionCostedFig8.BundlesEval
import Computational.Proofs.SessionCostedFig8.BucketCKAEval
import Computational.Proofs.SessionCostedFig8.BucketCKASwap
import Computational.Proofs.SessionCostedFig8.BucketPRNGSwap
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridge
import Computational.Proofs.SessionCostedFig8.QuerySubsumes
import Computational.Proofs.SessionCostedFig8.RedFSUniSafePost
import Computational.Proofs.CryptoGames.SM.Theorem8.Stage2Bucket
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth
import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.Fig8SchemeBridge

/-!
# Composed PQXDH + Double Ratchet Security with SPQR V1

**Checked by Lean.** Defines semantic evaluation agreement predicates (`SpkCostedEvalAgrees`,
`SimFig8CostedEvalAgreesGen`) and the existential hidden-salt bound `HiddenSaltBoundV1HoldsEx`,
and assembles the mixture bounds for `ComposedSecurePrefixMixV1`.

**DEV-C5 (formalization): Bounded-query prefix-step hybrids and mixture reductions.**
`ComposedSecurePrefixMixV1` bounds the `qStart`-step prefix hybrid via prefix-step mixture
reductions over `support (composedPrefixWithSpqr ...)`, avoiding the `N_spk_tot * N_send_tot`
slot-hybrid multiplicity.-/

namespace CryptoVerification.E2E
public section

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory


open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst CryptoGames.LibsignalSM.Proofs
  Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CryptoGames.SM.Thm1 CryptoGames.SM.ThmB
  CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoGames.Ratchet.LibsignalSim
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Signed CryptoVerification.E2E.HeadlineU
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)

local instance instInhabitedOfZeroHeadlineComposed {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

/-- Semantic evaluation agreement of `Rspk` with `spkLeakRed`, `spkLeakRedU`, `hop2PrgRedK`, and
`hop2PrfRedK` on `paramsV1 C K idA idB`. -/
@[expose] def SpkCostedEvalAgrees {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (Rspk : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam) : Prop :=
  ∀ (_hℓ : ℓ < 10 ^ 6)
    (_hdec : ∀ T, decT (encT T) = some T)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (_hq : SM.MakesAtMostQueries A q),
    let P := paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB
    (∀ s : BitVec 256,
      evalSpkLeakRed Rspk.spkLeakRed s A = spkLeakRed P Dh encPt encT decT qep s A) ∧
    (evalSpkLeakRedU Rspk.spkLeakRedU (fun x => evalSpkLeakRed Rspk.spkLeakRed x A) =
      spkLeakRedU spkLeakRed P Dh encPt encT decT qep A) ∧
    (∀ (s : BitVec 256) (j : ℕ), j < spkSwapHybridCount →
      evalSpkSwapPrgHybrid (Rspk.hop2PrgRedK j) s A =
        hop2PrgRedK P ℓ Dh encPt encT decT qep s j A) ∧
    (∀ (s : BitVec 256) (j : ℕ), j < spkSwapHybridCount →
      evalSpkSwapPrfHybrid (Rspk.hop2PrfRedK j) s A =
        hop2PrfRedK P ℓ Dh encT decT qep s j A)

/-- Semantic evaluation agreement of `Rspk` with target reductions `(spkLeakT, spkLeakUT, hop2PrgT,
hop2PrfT)`. -/
@[expose] def SpkCostedEvalAgreesGen {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (q : ℕ)
    (spkLeakT : BitVec 256 →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (spkLeakUT : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (hop2PrgT : BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      PRGScheme.PRGAdversary (BitVec 256 × BitVec 256))
    (hop2PrfT : BitVec 256 → ℕ →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      MACScheme.PRFAdversary Pt (BitVec 256))
    (Rspk : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam) : Prop :=
  ∀ (_hℓ : ℓ < 10 ^ 6)
    (_hdec : ∀ T, decT (encT T) = some T)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (_hq : SM.MakesAtMostQueries A q),
    (∀ s : BitVec 256, evalSpkLeakRed Rspk.spkLeakRed s A = spkLeakT s A) ∧
    (evalSpkLeakRedU Rspk.spkLeakRedU (fun x => evalSpkLeakRed Rspk.spkLeakRed x A) =
      spkLeakUT A) ∧
    (∀ (s : BitVec 256) (j : ℕ), j < spkSwapHybridCount →
      evalSpkSwapPrgHybrid (Rspk.hop2PrgRedK j) s A = hop2PrgT s j A) ∧
    (∀ (s : BitVec 256) (j : ℕ), j < spkSwapHybridCount →
      evalSpkSwapPrfHybrid (Rspk.hop2PrfRedK j) s A = hop2PrfT s j A)

theorem spkCostedEvalAgrees_iff_gen {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (Rspk : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam) :
    let P := paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB
    SpkCostedEvalAgrees C K idA idB ℓ Dh encPt encT decT lam qep q Rspk ↔
      SpkCostedEvalAgreesGen C K ℓ Dh encPt encT decT lam q
        (fun s A => spkLeakRed P Dh encPt encT decT qep s A)
        (fun A => spkLeakRedU spkLeakRed P Dh encPt encT decT qep A)
        (fun s j A => hop2PrgRedK P ℓ Dh encPt encT decT qep s j A)
        (fun s j A => hop2PrfRedK P ℓ Dh encT decT qep s j A)
        Rspk :=
  Iff.rfl

/-- Semantic evaluation agreement of `R.uniformStartRed` and `R.epoch0Red` with `(uniformStartT,
epoch0T)`. -/
@[expose] def UniformEpoch0CostedEvalAgreesGen {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q : ℕ)
    (uniformStartT epoch0T :
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      (Ratchet.RootKey × BitVec 256) → ProbComp Bool)
    (R : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam) : Prop :=
  ∀ (_hℓ : ℓ < 10 ^ 6)
    (B : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (_hq : SM.MakesAtMostQueries B q) (rc : Ratchet.RootKey × BitVec 256),
    R.uniformStartRed.eval (fun _ => B) rc = uniformStartT B rc ∧
    R.epoch0Red.eval (fun _ => B) rc = epoch0T B rc

/-- Existential `SessionCostedReductions` witness satisfying `sessionCostedReductionsBounded`,
`SpkCostedEvalAgrees`, and `hiddenSaltTerm ≤ hiddenSaltBoundV1` for `qep ≤ q + 4`. -/
@[expose] def HiddenSaltBoundV1HoldsEx {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : Prop :=
  ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ),
    ∃ (R : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam),
      sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q R ∧
      R.fs = (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fs ∧
      (qep ≤ q + 4 →
        SpkCostedEvalAgrees C K idA idB ℓ Dh encPt encT decT lam qep q R.spk ∧
        R.fig8 = (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 ∧
        R.simFig8 = (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 ∧
        R.epoch0Red = (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red ∧
        R.uniformStartRed =
          (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed ∧
        ∀ (_hK_tot : Encaps1Total K)
          (_hℓ : ℓ < 10 ^ 6)
          (_hDh : Dh.Commutes) (_hX : X25519RealizesDh C Dh encPt encT)
          (_hdec : ∀ T, decT (encT T) = some T) (_hinj : Function.Injective encT)
          (_hdum : ∀ T, encT T ≠ dummyKey)
          (_hz : ∀ x, Dh.dh x 0 = 0) (_hD : ∀ k x, C.D k (C.E k x) = x)
          (_hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
          (_hδ : ∀ Q : Pt,
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
          (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
          (_hq : SM.MakesAtMostQueries A q),
          let P := paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB
          LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf idA idB) lam qep
              (RefuseB0.refuseCorrB0 A) ≤
            hiddenSaltBoundV1 C K ℓ Dh encPt encT decT idA idB lam qep q δ R
              (RefuseB0.refuseCorrB0 A))

theorem evalDist_mixHiddenSaltGen_le_v1_of_support
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hidGame : α → ProbComp Bool)
    (hHid : ∀ o ∈ support oa,
      𝒟[hidGame o] {true} ≤
        hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o) (A o)) :
    𝒟[oa >>= hidGame] {true} ≤
      hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [Signed.evalDist_bind_apply_lintegral]
  refine (lintegral_mono_of_support oa _ _ hHid).trans_eq ?_
  unfold hiddenSaltBoundV1 hiddenSaltMixtureBound
  change (∫⁻ o, _ ∂𝒟[oa]) = _
  simp only [lintegral_add_left Measurable.of_discrete,
    lintegral_finsetSum _ fun _ _ => Measurable.of_discrete,
    lintegral_const, evalDist_apply_univ_eq_one, mul_one]

/-- Semantic evaluation contract for `R.simFig8` against a Figure-8 simulator `simT` and win-event
game `winT`. -/
@[expose] def SimFig8CostedEvalAgreesGen {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (simT : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (R : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam) : Prop :=
  ∀ (_hℓ : ℓ < 10 ^ 6)
    (B : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (_hq : SM.MakesAtMostQueries B q),
    let simAdv := R.simFig8.eval (fun _ => B) ()
    let smFig8 := lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam
    SM.MakesAtMostQueries simAdv q ∧
    SM.EqualPubChalls (·.1) simAdv ∧
    SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) simAdv ∧
    SessionShort.GuardedSMShort simAdv ∧
    SM.game smFig8 3 (qep + 1) SM.Config.h1 simAdv =
      SM.game smFig8 3 (qep + 1) SM.Config.h1 (simT B) ∧
    winT B = (do
      let b ← $ᵗ Bool
      let (_, s) ← SM.run smFig8 3 (qep + 1) SM.Config.h1 b simAdv
      return s.win)

private theorem evalDist_bind_apply_le_sum_hc {α κ : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (u : Finset κ) (g : κ → α → ProbComp Bool)
    (H : ∀ a, 𝒟[f a] {true} ≤ ∑ k ∈ u, 𝒟[g k a] {true}) :
    𝒟[oa >>= f] {true} ≤ ∑ k ∈ u, 𝒟[oa >>= g k] {true} := by
  simpa using evalDist_bind_apply_le_sum_sum oa f ({()} : Finset Unit) (fun _ => u) (fun _ => g)
    (fun a => by simpa using H a)

/-- Generic mixture Fig. 8 Stage-2 bucketed authenticity sum on `(R o).simFig8.eval` bounded above
by `fig8MixShortAuthV1` evaluated on `R`. -/
theorem fig8MixAuth_of_simFig8_le_fig8MixShortAuthV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hqSim : ∀ o, SM.MakesAtMostQueries ((R o).simFig8.eval (fun _ => A o) ()) q)
    (hshSim : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      ((R o).simFig8.eval (fun _ => A o) ()))
    (hgSim : ∀ o, SessionShort.GuardedSMShort ((R o).simFig8.eval (fun _ => A o) ()))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    letI : MeasurableSpace α := ⊤
    let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
    (hDh : Dh.Commutes) →
    2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
      𝒟[oa >>= fun o =>
        _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthGame
          (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
          (2 + 1) (qep + 1) tL
          (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true} ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  intro simAdv hDh
  let _ : MeasurableSpace α := ⊤
  let idOf : α → Party → IdentityKey := fun o => idsOf (ida o) (idb o)
  let B0 : ℕ := (q + 1) * (maxForwardJumps + 1)
  let B : α → Fig8Adv Pt ℓ := fun o => Thm1.challSim (2 + 1) (qep + 1) (simAdv o)
  have hChallField : ∀ o, (R o).fig8.challSim =
      (Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt Z protoSignalCodec ℓ
        encT (idOf o) lam (qep + 1) q).challSim := fun o => by
    rw [hfig8 o]; rfl
  have hCKAField : ∀ o, (R o).fig8.redCKAAuth =
      (Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt Z protoSignalCodec ℓ
        encT (idOf o) lam (qep + 1) q).redCKAAuth := fun o => by
    rw [hfig8 o]; rfl
  have hFsInst : ∀ o, (R o).fs =
      fsCostedRedsInst Z protoSignalCodec ℓ encT (idOf o) (min (2 * q) (q + 2)) := fun o => by
    rw [hfs o]; rfl
  have hChallEq : ∀ o,
      (R o).fig8.challSim.eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) () = B o := fun o => by
    rw [hChallField o]
    exact Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_challSim_eval
      Dh encPt Z protoSignalCodec ℓ hℓ encT (idOf o) lam (qep + 1) q (simAdv o) (hqSim o)
  have hqB : ∀ o, SM.MakesAtMostQueries (B o) q := fun o =>
    Thm1.challSim_queries (2 + 1) (qep + 1) (simAdv o) q (hqSim o)
  have heqB : ∀ o, SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (B o) :=
    fun o => CryptoGames.LibsignalSM.Proofs.RestrictedReds.challSim_equalPub (2 + 1) (qep + 1)
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (simAdv o)
  have hshB0 : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) (B o) := fun o =>
    SessionShort.challSim_sendOk (2 + 1) (qep + 1)
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) (simAdv o) (hshSim o)
  have hshB : ∀ o, SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) (B o) := fun o =>
    CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
      (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) (hshB0 o)
  have hgB : ∀ o, SessionShort.GuardedSMShort (B o) := fun o =>
    SessionShort.challSim_guardedSMShort (2 + 1) (qep + 1) (simAdv o) (hgSim o)
  refine Computational.Proofs.E2E.Fig8Stage2MixHelpers.fig8MixAuth_le_fig8MixShortAuthV1_of_fig8Eval
    Z K Dh hDh encPt encT decT lam qep q oa ida idb R A ?_ ?_ ?_ ?_
  · -- Hop 1 (`h9`): `bucketAuthAdvantage ≤ CKA.branch ... false (redCKAAuthBucket ...)`
    intro tL _ o
    exact CryptoGames.SM.Construction.lemma9_bucket_at (dhScheme Dh) (rootPRNG Z.F encPt)
      (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) lam 1 (qep + 1)
      (CryptoGames.CKA.dhScheme_correct Dh hDh) tL (B o)
  · -- Hop 2a (`hCKAAuth`): `redCKAAuth.eval = redCKAAuthBucket` under `CKA.advantage ... (prefixAdvAvg oa ...)`
    intro tL _
    simp only [hChallEq]
    change CKA.advantage (dhScheme Dh) 1 (healEpoch tL) (advAvg oa _) =
      CKA.advantage (dhScheme Dh) 1 (healEpoch tL) (advAvg oa _)
    simp only [hCKAField]
    rw [Computational.Proofs.SessionCostedFig8.QuerySubsumes.ckaAdvantage_advAvg_congr
      (dhScheme Dh) 1 (healEpoch tL) oa fun o =>
        Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_redCKAAuth_coinSimEquiv
          Dh encPt Z protoSignalCodec ℓ hℓ encT (idOf o) lam (qep + 1) q tL (B o)]
    rw [CKA.advantage_eq_boolDist, CKA.advantage_eq_boolDist,
      ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, ckaBranch_avg]
    have hBr : ∀ b,
        (oa >>= fun o => CKA.branch (dhScheme Dh) 1 (healEpoch tL) b
          ((CryptoGames.SM.Construction.redCKAAuthBucketProg (q + 1) B0 1 (qep + 1)
              maxForwardJumps tL :
            ReductionDsl.CostedReduction
              (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt Z Dh encPt encT
                (idOf o) lam B0)
              (CKA.ckaIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
                (BitVec 256) (BitVec 256) (BitVec 256)
                (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
                (LibsignalMsgPublicPart × CBC.Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
                ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
              _ _ .unit .unit .bool .bool).eval (fun _ => B o) ())) =
        (oa >>= fun o => CKA.branch (dhScheme Dh) 1 (healEpoch tL) b
          (_root_.Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.redCKAAuthBucket
            (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idOf o) maxForwardJumps)
            lam 1 (qep + 1) tL (B o))) :=
      fun b => bind_congr fun o => by
        rw [Computational.Proofs.SessionCostedFig8.BucketCKAEval.redCKAAuthBucketProg_eval_atomic
          Dh encPt Z ℓ encT (idOf o) lam (qep + 1) q tL (B o) (hqB o),
          ← _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaBranch_dhSchemeFb_eq]
        exact Computational.Proofs.SessionCostedFig8.BucketCKASwap.ckaBranch_redCKAAuthBucket_atomic_eq
          Dh (rootPRNG Z.F encPt) Z ℓ encT (idOf o) lam B0 q 1 (healEpoch tL) (qep + 1) tL b
          (Nat.le_refl _) (B o) q (hqB o) (Nat.le_refl q) (hshB0 o)
    rw [hBr true, hBr false]; rfl
  · -- Hop 2b (`hPRNGAuth`): `redPRNGAuthBucketHybrid ≤ redPRNGAuth.eval` (with equality)
    intro tL _ t _
    simp only [hChallEq]
    refine le_of_eq ?_
    symm
    change PRFPRNG.advantage (rootPRNG Z.F encPt) (advAvg oa _) =
      PRFPRNG.advantage (rootPRNG Z.F encPt) (advAvg oa _)
    have hPRNGCoin : ∀ o,
        Computational.Proofs.ReductionDsl.PureAuxMacroLift.CoinSimEquiv _
          (((R o).fig8.redPRNGAuth tL t).eval (fun _ => B o) ())
          ((_root_.Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.redPRNGAuthBucketHybridProg
              (q + 1) B0 1 (qep + 1) maxForwardJumps tL t :
            ReductionDsl.CostedReduction
              (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt Z Dh encPt encT
                (idOf o) lam B0)
              (PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
                (BitVec 256) (BitVec 256) (BitVec 256)
                (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
                (LibsignalMsgPublicPart × CBC.Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
                ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
              _ _ .unit .unit .bool .bool).eval (fun _ => B o) ()) := fun o => by
      rw [hfig8 o]
      exact Computational.Proofs.SessionCostedFig8.BundlesEval.compilePrngAtomic_coinSimEquiv
        ℓ Pt Z Dh encPt encT (idOf o) lam hℓ B0 _ (B o)
    rw [Computational.Proofs.SessionCostedFig8.QuerySubsumes.prngAdvantage_advAvg_congr
      (rootPRNG Z.F encPt) oa hPRNGCoin]
    rw [PRFPRNG.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist,
      prngBranch_avg, prngBranch_avg, prngBranch_avg, prngBranch_avg]
    have hBr : ∀ b,
        (oa >>= fun o => PRFPRNG.branch (rootPRNG Z.F encPt) b
          ((_root_.Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.redPRNGAuthBucketHybridProg
              (q + 1) B0 1 (qep + 1) maxForwardJumps tL t :
            ReductionDsl.CostedReduction
              (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt Z Dh encPt encT
                (idOf o) lam B0)
              (PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
                (BitVec 256) (BitVec 256) (BitVec 256)
                (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
                (LibsignalMsgPublicPart × CBC.Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
                ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
              _ _ .unit .unit .bool .bool).eval (fun _ => B o) ())) =
        (oa >>= fun o => PRFPRNG.branch (rootPRNG Z.F encPt) b
          (_root_.Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.redPRNGAuthBucketHybrid
            (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idOf o) maxForwardJumps)
            lam 1 (qep + 1) tL t (B o))) :=
      fun b => bind_congr fun o => by
        rw [Computational.Proofs.SessionCostedFig8.BucketPRNGSwap.redPRNGAuthBucketHybridProg_branch_eval_atomic
          Dh encPt Z ℓ encT (idOf o) lam (qep + 1) q tL t (B o) (hqB o) b,
          Computational.Proofs.SessionCostedFig8.BucketPRNGSwap.redPRNGAuthBucketHybrid_atomic_eq
            Dh (rootPRNG Z.F encPt) Z ℓ encT (idOf o) lam B0 q 1 (qep + 1) tL t
            (Nat.le_refl _) (B o) q (hqB o) (Nat.le_refl q) (hshB0 o)]
    rw [hBr true, hBr false]; rfl
  · -- Hop 3 (`hFSAuth`): 4-branch multi-session FS-AEAD + MAC bound at `qR = min (2 * q) (q + 2)`
    intro tL _
    exact Computational.Proofs.SessionCostedDFStage2Auth.localAuthBucketMix_par_le_sum_fsAeadAuthMixtureCompBound
      Z hD hℓ Dh hDh encPt encT hinj hdum oa idOf lam (qep + 1) q hq32
      (fun o => (R o).fs) hFsInst tL B hqB heqB hshB hgB
      (fun stage la j t o =>
        ((R o).fig8.redFSAuth stage la j tL t).eval
          (fun _ => (R o).fig8.challSim.eval (fun _ => simAdv o) ()) ())
      (fun j t _ _ _ stage la o => by
        rw [hChallEq o, hfig8 o]
        rfl)

theorem fig8MixPriv_of_simFig8_le_fig8MixShortPrivV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hqSim : ∀ o, SM.MakesAtMostQueries ((R o).simFig8.eval (fun _ => A o) ()) q)
    (hshSim : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      ((R o).simFig8.eval (fun _ => A o) ()))
    (hgSim : ∀ o, SessionShort.GuardedSMShort ((R o).simFig8.eval (fun _ => A o) ()))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    letI : MeasurableSpace α := ⊤
    let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
    (hDh : Dh.Commutes) →
    (∀ o ∈ support oa,
      SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (simAdv o)) →
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) SM.Config.h2 (simAdv o)].boolBias ≤
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  intro simAdv hDh heqSim
  let _ : MeasurableSpace α := ⊤
  let idOf : α → Party → IdentityKey := fun o => idsOf (ida o) (idb o)
  let Rfig8 : ∀ o, Fig8CostedReds Dh encPt Z protoSignalCodec ℓ encT (idOf o) lam :=
    fun o => Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt Z
      protoSignalCodec ℓ encT (idOf o) lam (qep + 1) q
  have hPrivBField : ∀ o, (R o).fig8.privRedB = (Rfig8 o).privRedB := fun o => by rw [hfig8 o]; rfl
  have hCKAPrivField : ∀ o, (R o).fig8.redCKAPriv = (Rfig8 o).redCKAPriv := fun o => by rw [hfig8 o]; rfl
  have hCKAPrivUField : ∀ o, (R o).fig8.redCKAPrivU = (Rfig8 o).redCKAPrivU := fun o => by rw [hfig8 o]; rfl
  have hPRNGPrivField : ∀ o, (R o).fig8.redPRNGPriv = (Rfig8 o).redPRNGPriv := fun o => by rw [hfig8 o]; rfl
  have hFSPrivField : ∀ o, (R o).fig8.redFSPriv = (Rfig8 o).redFSPriv := fun o => by rw [hfig8 o]; rfl
  have hFSPrivCoinField : ∀ o, (R o).fig8.redFSPrivCoin = (Rfig8 o).redFSPrivCoin := fun o => by rw [hfig8 o]; rfl
  have hFsInst : ∀ o, (R o).fs =
      fsCostedRedsInst Z protoSignalCodec ℓ encT (idOf o) (min (2 * q) (q + 2)) :=
    fun o => by rw [hfs o]; rfl
  let privAdv : ℕ → α → Fig8Adv Pt ℓ := fun i o =>
    ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) ((R o).simFig8.eval (fun _ => A o) ())
  have hPrivEq : ∀ i o,
      ((R o).fig8.privRedB i).eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) () = privAdv i o :=
    fun i o => by
      rw [hPrivBField o]
      exact Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_privRedB_eval
        Dh encPt Z protoSignalCodec ℓ hℓ encT (idOf o) lam (qep + 1) q i (simAdv o) (hqSim o)
  have hqPriv : ∀ i o, SM.MakesAtMostQueries (privAdv i o) q := fun i o =>
    CryptoGames.LibsignalSM.Proofs.PrivRedQueries.privRedB_queries
      (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o) q (hqSim o)
  have hshPriv : ∀ i o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) (privAdv i o) :=
    fun i o =>
      SessionShort.privRedB_sendOk (2 + 1) (qep + 1) i
        (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
        (lBlank ℓ) (fun _ => rfl) (simAdv o) (hshSim o)
  refine Computational.Proofs.E2E.Fig8Stage2MixHelpers.fig8MixPriv_le_fig8MixShortPrivV1_of_fig8Eval
    Z K hD hℓ Dh hDh encPt encT decT hinj hdum lam qep q hq32 oa ida idb R A hFsInst heqSim
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i _ tL _
    simp only [hPrivEq i, hCKAPrivField]
    change CKA.advantage (dhScheme Dh) 1 (healEpoch tL) (advAvg oa _) =
      CKA.advantage (dhScheme Dh) 1 (healEpoch tL) (advAvg oa _)
    exact _root_.CryptoVerification.LibsignalSession.fig8RedsInst_redCKAPriv_advAvg_advantage
      Dh encPt Z protoSignalCodec rfl ℓ hℓ encT oa idOf lam (qep + 1) q (healEpoch tL) tL i
      (privAdv i) (hqPriv i) (hshPriv i)
  · intro i _ tL _
    simp only [hPrivEq i, hCKAPrivUField]
    change CKA.advantage (dhScheme Dh) 1 (healEpoch tL) (advAvg oa _) =
      CKA.advantage (dhScheme Dh) 1 (healEpoch tL) (advAvg oa _)
    exact Computational.Proofs.SessionCostedDFStage2Priv.fig8RedsInst_redCKAPrivU_semantic_advAvg_advantage
      Dh encPt Z protoSignalCodec rfl ℓ hℓ encT oa idOf lam (qep + 1) q (healEpoch tL) tL i
      (privAdv i) (hqPriv i) (hshPriv i)
  · intro i _ tL _
    simp only [hPrivEq i, hPRNGPrivField]
    change PRFPRNG.advantage (rootPRNG Z.F encPt) (advAvg oa _) =
      PRFPRNG.advantage (rootPRNG Z.F encPt) (advAvg oa _)
    exact _root_.CryptoVerification.LibsignalSession.fig8RedsInst_redPRNGPriv_advAvg_advantage
      Dh encPt Z protoSignalCodec rfl ℓ hℓ encT oa idOf lam (qep + 1) q tL i
      (privAdv i) (hqPriv i) (hshPriv i)
  · intro i _
    refine EvalDistEq.rfl.bind fun o => ?_
    rw [hPrivEq i o, hFSPrivField o]
    exact Computational.Proofs.SessionCostedDFStage2Priv.fig8RedsInst_redFSPriv_semantic_game_evalDistEq
      Dh encPt Z protoSignalCodec rfl ℓ hℓ encT (idOf o) lam (qep + 1) q i
      (privAdv i o) (hqPriv i o) (hshPriv i o)
  · intro i _ o
    rw [hFSPrivField o, hPrivBField o]
    exact (Computational.Proofs.SessionCostedFig8.RedFSUniSafePost.fig8RedsInst_priv_fsOk_min_and_encAtomicShort
      Dh encPt Z protoSignalCodec rfl ℓ hℓ encT (idOf o) lam (qep + 1) q i
      (simAdv o) (hqSim o) (hshSim o) (hgSim o)).1
  · intro i _
    refine EvalDistEq.rfl.bind fun o => ?_
    rw [hPrivEq i o, hFSPrivCoinField o]
    exact Computational.Proofs.SessionCostedDFStage2Priv.fig8RedsInst_redFSPrivCoin_semantic_game_evalDistEq
      Dh encPt Z protoSignalCodec rfl ℓ hℓ encT (idOf o) lam (qep + 1) q i
      (privAdv i o) (hqPriv i o) (hshPriv i o)
  · intro i _ o
    rw [hFSPrivCoinField o, hPrivBField o]
    exact (Computational.Proofs.SessionCostedFig8.RedFSUniSafePost.fig8RedsInst_priv_fsOk_min_and_encAtomicShort
      Dh encPt Z protoSignalCodec rfl ℓ hℓ encT (idOf o) lam (qep + 1) q i
      (simAdv o) (hqSim o) (hshSim o) (hgSim o)).2

theorem boolBias_mixFig8_of_simFig8_le_fig8MixShortV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (simT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hSim : ∀ o, SimFig8CostedEvalAgreesGen Z K (ida o) (idb o) ℓ Dh encPt encT decT lam qep q
      (simT o) (winT o) (R o))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simT o (A o))].boolBias ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A +
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
  have hS := fun o => hSim o hℓ (A o) (hq o)
  have hGame :
      (oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simT o (A o))) =
      (oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simAdv o)) :=
    bind_congr fun o => (hS o).2.2.2.2.1.symm
  rw [hGame]
  have h17 := _root_.CryptoGames.SM.BucketAuthBridge.lemma17_bucket_mix
    (fun o => lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
    (2 + 1) (qep + 1) (by omega) oa simAdv
  calc _ ≤ _ := h17
    _ ≤ fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A +
        fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A :=
      add_le_add
        (fig8MixPriv_of_simFig8_le_fig8MixShortPrivV1 Z K hD hℓ Dh encPt encT decT hinj hdum lam qep q
          hq32 oa ida idb R A (fun o => (hS o).1) (fun o => (hS o).2.2.1) (fun o => (hS o).2.2.2.1)
          hfig8 hfs hDh (fun o _ => (hS o).2.1))
        (fig8MixAuth_of_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh encPt encT decT hinj hdum lam qep q
          hq32 oa ida idb R A (fun o => (hS o).1) (fun o => (hS o).2.2.1) (fun o => (hS o).2.2.2.1)
          hfig8 hfs hDh)
    _ = _ := add_comm _ _

theorem evalDist_mixWin_of_simFig8_le_fig8MixShortAuthV1
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (simT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hSim : ∀ o, SimFig8CostedEvalAgreesGen Z K (ida o) (idb o) ℓ Dh encPt encT decT lam qep q
      (simT o) (winT o) (R o))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    2 * 𝒟[oa >>= fun o => winT o (A o)] {true} ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  let simAdv : α → Fig8Adv Pt ℓ := fun o => (R o).simFig8.eval (fun _ => A o) ()
  have hS := fun o => hSim o hℓ (A o) (hq o)
  have hWin :
      𝒟[oa >>= fun o => winT o (A o)] {true} ≤
        ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
          𝒟[oa >>= fun o =>
            _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthGame
              (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
              (2 + 1) (qep + 1) tL
              (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true} :=
    evalDist_bind_apply_le_sum_hc oa _ _ _ fun o => by
      rw [(hS o).2.2.2.2.2]
      exact _root_.CryptoGames.SM.BucketAuthBridge.run_win_prob_le_bucketAuth
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
        (2 + 1) (qep + 1) (by omega) (simAdv o)
  exact (mul_le_mul_right hWin 2).trans
    (fig8MixAuth_of_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb R A (fun o => (hS o).1) (fun o => (hS o).2.2.1) (fun o => (hS o).2.2.2.1)
      hfig8 hfs hDh)

/-- Bounds the `boolBias` of `oa >>= gameU` by `uniformStartMixtureBound` across Uniform-Start,
Figure-8, epoch-0, and hidden-salt hops. -/
theorem boolBias_mixUGen_le_uTermShortMix
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (gameU gameR : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (uniformStartT epoch0T : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes →
      (Ratchet.RootKey × BitVec 256) → ProbComp Bool)
    (simT : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → Fig8Adv Pt ℓ)
    (winT eps0Game hidGame : α →
      SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes → ProbComp Bool)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q)
    (hUR : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => gameU o (B o)].boolBias ≤
        𝒟[oa >>= fun o => gameR o (RefuseB0.refuseCorrB0 (B o))].boolBias
          + 2 * (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
              (prefixPrgAvg oa fun o rc => uniformStartT o (RefuseB0.refuseCorrB0 (B o)) rc))
    (hRSim : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => gameR o (B o)].boolBias ≤
        𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simT o (B o))].boolBias
          + 2 * (refineConst Z Dh encPt q qep δ +
            (𝒟[oa >>= fun o => winT o (B o)] {true} +
             𝒟[oa >>= fun o => eps0Game o (B o)] {true} +
             𝒟[oa >>= fun o => hidGame o (B o)] {true})))
    (hEps0 : ∀ B : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes,
      (∀ o, SM.MakesAtMostQueries (B o) q) →
      𝒟[oa >>= fun o => eps0Game o (B o)] {true} ≤
        (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prefixPrgAvg oa fun o rc => epoch0T o (B o) rc) + q * eps0IdealUnit Z.F)
    (hHid : ∀ o ∈ support oa,
      𝒟[hidGame o (RefuseB0.refuseCorrB0 (A o))] {true} ≤
        hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o)
          (RefuseB0.refuseCorrB0 (A o)))
    (hUE : ∀ o, UniformEpoch0CostedEvalAgreesGen Z K (ida o) (idb o) ℓ Dh encPt encT decT lam q
      (uniformStartT o) (epoch0T o) (R o))
    (hSim : ∀ o, SimFig8CostedEvalAgreesGen Z K (ida o) (idb o) ℓ Dh encPt encT decT lam qep q
      (simT o) (winT o) (R o))
    (hfig8 : ∀ o, (R o).fig8 =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fig8)
    (hfs : ∀ o, (R o).fs =
      (v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).fs) :
    𝒟[oa >>= fun o => gameU o (A o)].boolBias ≤
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
  have hU := hUR A' hq'
  have hUsEq :
      (prefixPrgAvg oa fun o rc => uniformStartT o (RefuseB0.refuseCorrB0 (A' o)) rc) =
      (prefixPrgAvg oa fun o rc =>
        (R o).uniformStartRed.eval (fun _ => RefuseB0.refuseCorrB0 (A' o)) rc) := by
    funext rc
    unfold prefixPrgAvg
    congr 1; funext o
    exact ((hUE o hℓ (RefuseB0.refuseCorrB0 (A' o)) (hqR o) rc).1).symm
  rw [hUsEq] at hU
  have hR := hRSim (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  have h1 := boolBias_mixFig8_of_simFig8_le_fig8MixShortV1 Z K hD hℓ Dh hDh encPt encT decT hinj
    hdum lam qep q (by omega) oa ida idb R simT winT (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
    hSim hfig8 hfs
  have h2 := evalDist_mixWin_of_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh hDh encPt encT decT hinj
    hdum lam qep q (by omega) oa ida idb R simT winT (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
    hSim hfig8 hfs
  have h3 := hEps0 (fun o => RefuseB0.refuseCorrB0 (A' o)) hqR
  have hEps0Eq :
      (prefixPrgAvg oa fun o rc => epoch0T o (RefuseB0.refuseCorrB0 (A' o)) rc) =
      (prefixPrgAvg oa fun o rc =>
        (R o).epoch0Red.eval (fun _ => RefuseB0.refuseCorrB0 (A' o)) rc) := by
    funext rc
    unfold prefixPrgAvg
    congr 1; funext o
    exact ((hUE o hℓ (RefuseB0.refuseCorrB0 (A' o)) (hqR o) rc).2).symm
  rw [hEps0Eq] at h3
  have h4 := evalDist_mixHiddenSaltGen_le_v1_of_support Z K ℓ Dh encPt encT decT lam qep q δ
    oa ida idb R (fun o => RefuseB0.refuseCorrB0 (A' o))
    (fun o => hidGame o (RefuseB0.refuseCorrB0 (A' o)))
    (fun o ho => by rw [hsup o ho]; exact hHid o ho)
  have hle :
      𝒟[oa >>= fun o => gameU o (A' o)].boolBias ≤
        uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A' := by
    refine hU.trans ((add_le_add hR le_rfl).trans ?_)
    rw [mul_add, mul_add, mul_add]
    refine (add_le_add (add_le_add h1 (add_le_add le_rfl (add_le_add
      (add_le_add h2 (mul_le_mul_right h3 2)) (mul_le_mul_right h4 2)))) le_rfl).trans_eq ?_
    unfold uniformStartMixtureBound
    ring
  have hg :
      𝒟[oa >>= fun o => gameU o (A' o)] =
      𝒟[oa >>= fun o => gameU o (A o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by
      rw [hsup o ho]
  rw [hg, uTermShortMixV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R _ _
    hsup] at hle
  exact hle

end

end CryptoVerification.E2E

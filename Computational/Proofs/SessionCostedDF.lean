/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFs -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8 -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.DFProgBoundsBase
public import Computational.Proofs.SessionCostedFig8.DFProgBucketBounds -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs
import Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds
public import Computational.Proofs.SessionCostedDFStage2 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.BucketAuthBridge
public import Computational.Proofs.E2E.SpkCostedAndHeadlineSlice -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.DeliverForgeShifted
import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF
public import Computational.Specifications.Session.StatementComposed
import Computational.Proofs.ReductionDsl.SpkHop2Red
import Computational.Proofs.ReductionDsl.SpkLeakRedU
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Queries
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.CryptoGames.SM.Theorem6Libsignal
import Computational.Proofs.E2E.SignedCoin
import Computational.Proofs.E2E.SignedFig8
import Computational.Proofs.E2E.SignedSession
import Computational.Proofs.E2E.SignedThm1
import Computational.Proofs.E2E.SignedThm8
import Computational.Proofs.E2E.SpkCostedEval
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.GameHop.StateSim
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRed
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.SessionCostedFig8.RedFSUniSafePost
import Computational.Proofs.SessionCostedDFStage2Priv
import Computational.Proofs.SessionCostedDFStage2Auth
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.SessionCostedFig8.BundlesEval
import Computational.Proofs.SessionCostedFig8.QuerySubsumes
import Computational.Proofs.SessionCostedFig8.BucketCKAEval
import Computational.Proofs.SessionCostedFig8.BucketCKASwap
import Computational.Proofs.SessionCostedFig8.BucketPRNGSwap
import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.E2E.RefuseCorrB0Core -- proof-setup: allow-public-import
import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK
import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNGPotOK
import Computational.Proofs.ReductionDsl.SM.DeliverForgePotOK
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import Computational.Proofs.E2E.SpkHop2
import Computational.Proofs.E2E.SpkHop2A
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdSkip
import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
import Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc
import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepSend
import Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap
import Computational.Proofs.HeadlineV1.CouplingV1
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedBase
import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.PubRed

/-!
# Per-Session Costed `DeliverForge` Reductions and `SessionCostedReductions` Instance

Defines `v1SessionReds`, proves `v1SessionReds_bounded`, and establishes evaluation agreement
with the mixture bounds of `StatementComposed`.-/

namespace CryptoVerification.E2E
public section

set_option exponentiation.threshold 1024

open _root_.ReductionDsl OracleSpec OracleComp ENNReal MeasureTheory
open Computational.Proofs.GameHop.ReductionDsl.CostUB
open Computational.Proofs.GameHop.StateSim
open _root_.CryptoGames _root_.CryptoGames.LibsignalSM _root_.CryptoGames.LibsignalSM.Inst
open _root_.CryptoGames.Ratchet _root_.CryptoGames.CKA _root_.CryptoGames.SM _root_.CryptoGames.SM.Construction
open _root_.CryptoGames.SM.Engine _root_.CryptoGames.SM.Thm1 _root_.CryptoGames.SM.ThmB
open _root_.CryptoGames.LibsignalSession _root_.CryptoGames.Ratchet.LibsignalInst
open _root_.CryptoGames.Ratchet.LibsignalSim _root_.CryptoGames.LibsignalSM.Proofs
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

local instance {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

/-! ## `SessionCostedReductions` instance and bounds -/

abbrev spkCostedRedsInst {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ) :
    SpkCostedReds Pt ℓ C K Dh encPt encT decT lam :=
  Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst
    ℓ C K idA idB Dh encPt encT decT lam q qep

theorem hop2PrfRedK_queryBudget_le_old (q : ℕ) :
    q ≤ 2 * q :=
  Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.hop2PrfRedK_queryBudget_le_old q

theorem spkCostedBounds_imp_old {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {Dh : CKA.DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (q qep : ℕ) (R : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam)
    (h : spkCostedBounds q qep R) :
    GRedBounded R.spkLeakRed (fun _ => 1) (fun _ => 0)
      q (q + 1) (ratchetCostBudget q qep) ∧
    GRedBounded R.spkLeakRedU (fun _ => 1) (fun _ => 0)
      (q + 1) (q + 1) (ratchetCostBudget q qep) ∧
    (∀ k : ℕ, k < spkSwapHybridCount →
      GRedBounded (R.hop2PrgRedK k) Empty.elim (fun _ => 0)
        q 0 (ratchetCostBudget q qep)) ∧
    (∀ k : ℕ, k < spkSwapHybridCount →
      GRedBounded (R.hop2PrfRedK k) (fun _ => 1) (fun _ => 0)
        q (2 * q) (ratchetCostBudget q qep)) :=
  Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedBounds_imp_old q qep R h

theorem spkCostedRedsInst_bounds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (hqep : qep ≤ q + 10) :
    spkCostedBounds q qep
      (spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep) :=
  Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_bounds
    ℓ C K idA idB Dh encPt encT decT lam q qep hqep

/-- `SessionCostedReductions` instance combining `SpkCostedAndHeadlineSlice.spkCostedRedsInst`,
`fig8RedsInst`, `fsCostedRedsInst`, the promoted outer session reductions (`simFig8RedProg`,
`simDeliverForgeRedProg`, `epoch0Red`, `uniformStartRed`), and the atomic Stage-2
`DeliverForge` reductions (`challSimDFAtomicProg`, `red{CKA,PRNG}AuthDFAtomicProg`,
`redFSAuthDFMultiAtomicProg`, `redCKAAuthDFBucketAtomicProg`, `redPRNGAuthDFBucketHybridAtomicProg`,
`redFSAuthDFMultiBucketAtomicProg`). -/
@[expose] def v1SessionReds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam where
  spk :=
    Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst
      ℓ C K idA idB Dh encPt encT decT lam q qep
  fig8 :=
    fig8RedsInst Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam (qep + 1) q
  fs :=
    fsCostedRedsInst C protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2))
  simFig8 :=
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
      ℓ C K idA idB Dh encPt encT decT lam qep q
  simDeliverForge :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg
      ℓ C K idA idB Dh encPt encT decT lam qep q
  epoch0Red :=
    Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg.epoch0Red
      C K Dh encPt encT decT idA idB lam ℓ q qep
  uniformStartRed :=
    Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg.uniformStartRed
      C K Dh encPt encT decT idA idB lam ℓ q qep
  challSimDF :=
    challSimDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
  B_cka := fun tL t =>
    redCKAAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t
  B_prng := fun tL t =>
    redPRNGAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t
  B_fs := fun stage la j tL t =>
    Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFMultiAtomicProg
      ℓ Pt C Dh encPt encT (idsOf idA idB) lam stage la j (min (2 * q) (q + 2)) q (qep + 1) tL t
  B_cka_u := fun tL par =>
    Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redCKAAuthDFBucketAtomicProg
      Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
      (Computational.Proofs.SessionCostedDFStage2.clampDFBucketLeakGuess qep tL) par
  B_prng_u := fun tL par t =>
    Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFBucketHybridAtomicProg
      Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
      (Computational.Proofs.SessionCostedDFStage2.clampDFBucketLeakGuess qep tL) par
      (Computational.Proofs.SessionCostedDFStage2.clampDFBucketEpoch qep t)
  B_fs_u := fun stage la j tL par _t =>
    Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFMultiBucketAtomicProg
      ℓ Pt C Dh encPt encT (idsOf idA idB) lam stage la j (min (2 * q) (q + 2)) q (qep + 1)
      (Computational.Proofs.SessionCostedDFStage2.clampDFBucketLeakGuess qep tL) par

/-- `v1SessionReds` satisfies `sessionCostedReductionsBounded` under `qep ≤ q + 10`. -/
theorem v1SessionReds_bounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ q + 10) :
    sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  have ⟨hB1, hB2, hBu, hQ12, hQu⟩ :=
    Computational.Proofs.SessionCostedDFStage2.v1SessionReds_nonFs_df_bounded
      ℓ C idA idB Dh encPt encT lam qep q hqep
  refine ⟨Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_bounds
      ℓ C K idA idB Dh encPt encT decT lam q qep hqep,
    by apply fig8RedsInst_bounds; omega,
    fsCostedRedsInst_bounds C protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)) (qep + 1),
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_gRedBounded
      ℓ C K idA idB Dh encPt encT decT lam qep q,
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg_gRedBounded
      ℓ C K idA idB Dh encPt encT decT lam qep q hqep,
    Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg.epoch0Red_gRedBounded_succ
      C K Dh encPt encT decT idA idB lam ℓ q qep hqep,
    Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg.uniformStartRed_gRedBounded_succ
      C K Dh encPt encT decT idA idB lam ℓ q qep hqep,
    by apply Computational.Proofs.SessionCostedFig8.DFProgBoundsBase.challSimDFAtomicProg_gRedBounded; omega,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨(hB1 t ht).1, (hB1 t ht).2, fun j _ stage la => by
      apply Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds.redFSAuthDFMultiAtomicProg_gRedBounded; omega⟩
  · intro t ht
    exact ⟨(hB2 t ht).1, (hB2 t ht).2, fun j _ stage la => by
      apply Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds.redFSAuthDFMultiAtomicProg_gRedBounded; omega⟩
  · intro tL _ par
    exact ⟨(hBu tL par).1, fun t _ => ⟨(hBu tL par).2 t, fun j _ stage la => by
      apply Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds.redFSAuthDFMultiBucketAtomicProg_gRedBounded; omega⟩⟩
  · intro t _ A hA
    exact ⟨(hQ12 t A hA).1, fun j _ stage la =>
      Computational.Proofs.SessionCostedDFStage2.redFSAuthDFMultiAtomicProg_makesAtMostQueries
        ℓ C Dh encPt encT (idsOf idA idB) lam stage la j q (qep + 1) (some (t - 2)) t A hA⟩
  · intro t _ A hA
    exact ⟨(hQ12 t A hA).2, fun j _ stage la =>
      Computational.Proofs.SessionCostedDFStage2.redFSAuthDFMultiAtomicProg_makesAtMostQueries
        ℓ C Dh encPt encT (idsOf idA idB) lam stage la j q (qep + 1) (some (t - 3)) t A hA⟩
  · intro tL _ par t _ A hA
    exact ⟨hQu tL par t A hA, fun j _ stage la =>
      Computational.Proofs.SessionCostedDFStage2.redFSAuthDFMultiBucketAtomicProg_makesAtMostQueries
        ℓ C Dh encPt encT (idsOf idA idB) lam stage la j q (qep + 1)
        (Computational.Proofs.SessionCostedDFStage2.clampDFBucketLeakGuess qep tL) par A hA⟩

/-! ## Evaluation agreement for mixture bounds -/

section EvalBridges

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total)
open CryptoVerification.LibsignalSession.HeadlineV1
open CryptoVerification.E2E.Signed
open _root_.CryptoGames.SM.Construction.AuthL11
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open _root_.CryptoGames.LibsignalSM.Proofs.Refinement (simCNoneWinEvent)

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

@[simp] theorem v1SessionReds_spk (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).spk =
      spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep := rfl

@[simp] theorem v1SessionReds_fig8 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 =
      fig8RedsInst Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam (qep + 1) q := rfl

@[simp] theorem v1SessionReds_fs (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fs =
      fsCostedRedsInst C protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)) := rfl

@[simp] theorem v1SessionReds_simFig8 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 =
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
        ℓ C K idA idB Dh encPt encT decT lam qep q := rfl

@[simp] theorem v1SessionReds_simDeliverForge (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simDeliverForge =
      Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg
        ℓ C K idA idB Dh encPt encT decT lam qep q := rfl

@[simp] theorem v1SessionReds_epoch0Red (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red =
      Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg.epoch0Red
        C K Dh encPt encT decT idA idB lam ℓ q qep := rfl

@[simp] theorem v1SessionReds_uniformStartRed (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed =
      Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg.uniformStartRed
        C K Dh encPt encT decT idA idB lam ℓ q qep := rfl

@[simp] theorem v1SessionReds_challSimDF (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).challSimDF =
      challSimDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q := rfl

@[simp] theorem v1SessionReds_B_cka (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).B_cka tL t =
      redCKAAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t := rfl

@[simp] theorem v1SessionReds_B_prng (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).B_prng tL t =
      redPRNGAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t := rfl

@[simp] theorem v1SessionReds_B_fs_stage2 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (stage la : Bool) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).B_fs stage la j tL t =
      Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFMultiAtomicProg
        ℓ Pt C Dh encPt encT (idsOf idA idB) lam stage la j (min (2 * q) (q + 2)) q (qep + 1) tL t := rfl

@[simp] theorem v1SessionReds_B_cka_u (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (par : Bool) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).B_cka_u tL par =
      Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redCKAAuthDFBucketAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
        (Computational.Proofs.SessionCostedDFStage2.clampDFBucketLeakGuess qep tL) par := rfl

@[simp] theorem v1SessionReds_B_prng_u (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).B_prng_u tL par t =
      Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFBucketHybridAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
        (Computational.Proofs.SessionCostedDFStage2.clampDFBucketLeakGuess qep tL) par
        (Computational.Proofs.SessionCostedDFStage2.clampDFBucketEpoch qep t) := rfl

@[simp] theorem v1SessionReds_B_fs_u_stage2 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (stage la : Bool) (j : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).B_fs_u stage la j tL par t =
      Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFMultiBucketAtomicProg
        ℓ Pt C Dh encPt encT (idsOf idA idB) lam stage la j (min (2 * q) (q + 2)) q (qep + 1)
        (Computational.Proofs.SessionCostedDFStage2.clampDFBucketLeakGuess qep tL) par := rfl

omit [Zero Pt] [SampleableType Pt] in
theorem deliverForgeFSCompBoundWith_inst_eq (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    CryptoVerification.E2E.fsAeadSlotSumBound C qR
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR) A =
      Proofs.Refinement.deliverForgeFSCompBound C protoSignalCodec ℓ encT idOf qR A :=
  CryptoVerification.LibsignalSession.deliverForgeFSCompBoundWith_inst_eq
    C ℓ encT idOf qR hℓ hinj A hA hshort

omit [Zero Pt] [SampleableType Pt] in
theorem fsPrgMixWith_inst_eq {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR m : ℕ) (hℓ : ℓ < 10 ^ 6) (hm : m ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    fsChainPrgMixtureTerm C oa qR (fun o => fsCostedRedsInst C codec ℓ encT (idOf o) qR) A m =
      FSMix.fsPrgMix C protoSignalCodec ℓ encT oa idOf 25000 A m :=
  CryptoVerification.LibsignalSession.fsPrgMixWith_inst_eq
    C codec ℓ encT oa idOf qR m hℓ hm hinj A hA hshort

omit [Zero Pt] [SampleableType Pt] in
theorem fsSWMixWith_inst_eq {α : Type} (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR m : ℕ) (hℓ : ℓ < 10 ^ 6) (hm : m ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    fsSaltWireMixtureTerm C protoSignalCodec ℓ oa qR
        (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR) A m =
      FSMix.fsSWMix C protoSignalCodec ℓ encT oa idOf 25000 qR A m :=
  CryptoVerification.LibsignalSession.fsSWMixWith_inst_eq
    C ℓ encT oa idOf qR m hℓ hm hinj A hA hshort

omit [Zero Pt] [SampleableType Pt] in
theorem fsShortBoundMixWith_inst_eq {α : Type} (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR qd : ℕ) (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    fsAeadMixtureBound C protoSignalCodec ℓ oa (q := qR) (qd := qd)
        (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR) A =
      FSMix.fsShortBoundMix C protoSignalCodec ℓ encT oa idOf 25000 qR qd A :=
  CryptoVerification.LibsignalSession.fsShortBoundMixWith_inst_eq
    C ℓ encT oa idOf qR qd hℓ hinj A hA hshort

theorem prngAdvantage_advAvg_congr {KR Sig I K α : Type}
    [SampleableType KR] [SampleableType I] [SampleableType K] [DecidableEq I]
    (prng : PRFPRNG KR Sig I K) (oa : ProbComp α)
    (D₁ D₂ : α → PRFPRNG.Adversary Sig I K)
    (hBr : ∀ o b, PRFPRNG.branch prng b (D₁ o) = PRFPRNG.branch prng b (D₂ o)) :
    PRFPRNG.advantage prng (advAvg oa D₁) = PRFPRNG.advantage prng (advAvg oa D₂) := by
  rw [PRFPRNG.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist,
    prngBranch_avg, prngBranch_avg, prngBranch_avg, prngBranch_avg]
  have hT : (oa >>= fun o => PRFPRNG.branch prng true (D₁ o)) =
      (oa >>= fun o => PRFPRNG.branch prng true (D₂ o)) :=
    bind_congr fun o => hBr o true
  have hF : (oa >>= fun o => PRFPRNG.branch prng false (D₁ o)) =
      (oa >>= fun o => PRFPRNG.branch prng false (D₂ o)) :=
    bind_congr fun o => hBr o false
  rw [hT, hF]

/-- Mixture CKA advantage evaluation + `(dhSchemeFb, fsAtomicB) → (dhScheme, lFS)` bridge for
`fig8RedsInst.redCKAAuth` (`redCKAAuthBucketProg` → `redCKAAuthBucket`). -/
private theorem fig8RedsInst_redCKAAuth_semantic_advAvg_advantage_stage2
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Dh : _root_.CryptoGames.CKA.DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : _root_.CryptoGames.LibsignalSession.Crypto)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → _root_.CryptoGames.LibsignalSession.PublicKey)
    (oa : ProbComp α)
    (idOf : α → _root_.CryptoGames.Party → _root_.CryptoGames.LibsignalSession.IdentityKey)
    (lam : Pt) (qep q : ℕ)
    (tStar : ℕ) (tL : Option ℕ) (A : α → _root_.CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hqA : ∀ o, _root_.CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ =>
        Computational.Proofs.ReductionDsl.Fig8Atomic.atomicShortPubB m.1) (A o)) :
    _root_.CryptoGames.CKA.advantage (_root_.CryptoGames.CKA.dhScheme Dh) 1 tStar
      (CryptoVerification.E2E.prefixAdvAvg oa fun o =>
        ((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt C
          CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o) lam qep q).redCKAAuth
            tL).eval (fun _ => A o) ()) =
    _root_.CryptoGames.CKA.advantage (_root_.CryptoGames.CKA.dhScheme Dh) 1 tStar
      (CryptoVerification.E2E.prefixAdvAvg oa fun o =>
        _root_.CryptoGames.SM.Construction.redCKAAuthBucket
          (_root_.CryptoGames.CKA.dhScheme Dh) (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lFS C
            CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o)
            _root_.CryptoGames.LibsignalSession.maxForwardJumps)
          lam 1 qep tL (A o)) := by
  let _ : Inhabited Pt := ⟨0⟩
  let B0 := (q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)
  change _root_.CryptoGames.CKA.advantage (_root_.CryptoGames.CKA.dhScheme Dh) 1 tStar
      (CryptoVerification.E2E.Signed.advAvg oa _) =
    _root_.CryptoGames.CKA.advantage (_root_.CryptoGames.CKA.dhScheme Dh) 1 tStar
      (CryptoVerification.E2E.Signed.advAvg oa _)
  rw [Computational.Proofs.SessionCostedFig8.QuerySubsumes.ckaAdvantage_advAvg_congr
      (_root_.CryptoGames.CKA.dhScheme Dh) 1 tStar oa fun o => by
    dsimp only [Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst]
    exact Computational.Proofs.SessionCostedFig8.BundlesEval.compileCkaAtomic_coinSimEquiv
      ℓ Pt C Dh encPt encT (idOf o) lam hℓ B0 _ (A o)]
  rw [_root_.CryptoGames.CKA.advantage_eq_boolDist, _root_.CryptoGames.CKA.advantage_eq_boolDist,
    CryptoVerification.E2E.Signed.ckaBranch_avg, CryptoVerification.E2E.Signed.ckaBranch_avg,
    CryptoVerification.E2E.Signed.ckaBranch_avg, CryptoVerification.E2E.Signed.ckaBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => _root_.CryptoGames.CKA.branch (_root_.CryptoGames.CKA.dhScheme Dh) 1 tStar b
        ((_root_.CryptoGames.SM.Construction.redCKAAuthBucketProg (q + 1) B0 1 qep
          _root_.CryptoGames.LibsignalSession.maxForwardJumps tL :
          _root_.ReductionDsl.CostedReduction
            (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT
              (idOf o) lam B0)
            (_root_.CryptoGames.CKA.ckaIface (BitVec 256)
              (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
              (BitVec 256) (BitVec 256) (BitVec 256)
              (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
              (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
              (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
              (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
              ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
            _ _ .unit .unit .bool .bool).eval (fun _ => A o) ())) =
      (oa >>= fun o => _root_.CryptoGames.CKA.branch (_root_.CryptoGames.CKA.dhScheme Dh) 1 tStar b
        (_root_.CryptoGames.SM.Construction.redCKAAuthBucket
          (_root_.CryptoGames.CKA.dhScheme Dh) (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lFS C
            CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o)
            _root_.CryptoGames.LibsignalSession.maxForwardJumps)
          lam 1 qep tL (A o))) :=
    fun b => bind_congr fun o => by
      rw [Computational.Proofs.SessionCostedFig8.BucketCKAEval.redCKAAuthBucketProg_eval_atomic
        Dh encPt C ℓ encT (idOf o) lam qep q tL (A o) (hqA o)]
      rw [← CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaBranch_dhSchemeFb_eq]
      exact Computational.Proofs.SessionCostedFig8.BucketCKASwap.ckaBranch_redCKAAuthBucket_atomic_eq
        Dh (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt) C ℓ encT (idOf o)
        lam B0 q 1 tStar qep tL b (Nat.le_refl _)
        (A o) q (hqA o) (Nat.le_refl q) (hshA o)
  rw [hBr true, hBr false]

/-- Mixture PRF-PRNG advantage evaluation + `(dhSchemeFb, fsAtomicB) → (dhScheme, lFS)` bridge for
`fig8RedsInst.redPRNGAuth` (`redPRNGAuthBucketHybridProg` → `redPRNGAuthBucketHybrid`). -/
private theorem fig8RedsInst_redPRNGAuth_semantic_advAvg_advantage_stage2
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (Dh : _root_.CryptoGames.CKA.DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : _root_.CryptoGames.LibsignalSession.Crypto)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → _root_.CryptoGames.LibsignalSession.PublicKey)
    (oa : ProbComp α)
    (idOf : α → _root_.CryptoGames.Party → _root_.CryptoGames.LibsignalSession.IdentityKey)
    (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : α → _root_.CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hqA : ∀ o, _root_.CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ =>
        Computational.Proofs.ReductionDsl.Fig8Atomic.atomicShortPubB m.1) (A o)) :
    _root_.CryptoGames.PRFPRNG.advantage (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt)
      (CryptoVerification.E2E.prefixAdvAvg oa fun o =>
        ((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt C
          CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o) lam qep q).redPRNGAuth
            tL t).eval (fun _ => A o) ()) =
    _root_.CryptoGames.PRFPRNG.advantage (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt)
      (CryptoVerification.E2E.prefixAdvAvg oa fun o =>
        Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.redPRNGAuthBucketHybrid
          (_root_.CryptoGames.CKA.dhScheme Dh) (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lFS C
            CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o)
            _root_.CryptoGames.LibsignalSession.maxForwardJumps)
          lam 1 qep tL t (A o)) := by
  let _ : Inhabited Pt := ⟨0⟩
  let B0 := (q + 1) * (_root_.CryptoGames.LibsignalSession.maxForwardJumps + 1)
  change _root_.CryptoGames.PRFPRNG.advantage (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt)
      (CryptoVerification.E2E.Signed.advAvg oa _) =
    _root_.CryptoGames.PRFPRNG.advantage (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt)
      (CryptoVerification.E2E.Signed.advAvg oa _)
  rw [Computational.Proofs.SessionCostedFig8.QuerySubsumes.prngAdvantage_advAvg_congr
      (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt) oa fun o => by
    dsimp only [Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst]
    exact Computational.Proofs.SessionCostedFig8.BundlesEval.compilePrngAtomic_coinSimEquiv
      ℓ Pt C Dh encPt encT (idOf o) lam hℓ B0 _ (A o)]
  rw [_root_.CryptoGames.PRFPRNG.advantage_eq_boolDist, _root_.CryptoGames.PRFPRNG.advantage_eq_boolDist,
    CryptoVerification.E2E.Signed.prngBranch_avg, CryptoVerification.E2E.Signed.prngBranch_avg,
    CryptoVerification.E2E.Signed.prngBranch_avg, CryptoVerification.E2E.Signed.prngBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => _root_.CryptoGames.PRFPRNG.branch (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt) b
        ((Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.redPRNGAuthBucketHybridProg
          (q + 1) B0 1 qep _root_.CryptoGames.LibsignalSession.maxForwardJumps tL t :
          _root_.ReductionDsl.CostedReduction
            (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT
              (idOf o) lam B0)
            (_root_.CryptoGames.PRFPRNG.prngIface (BitVec 256)
              (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
              (BitVec 256) (BitVec 256) (BitVec 256)
              (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
              (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
              (_root_.CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × _root_.CryptoGames.CBC.Plain ℓ)
              (ℕ × _root_.CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
              ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
            _ _ .unit .unit .bool .bool).eval (fun _ => A o) ())) =
      (oa >>= fun o => _root_.CryptoGames.PRFPRNG.branch (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt) b
        (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs.redPRNGAuthBucketHybrid
          (_root_.CryptoGames.CKA.dhScheme Dh) (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lFS C
            CryptoVerification.LibsignalProtoCodec.protoSignalCodec ℓ encT (idOf o)
            _root_.CryptoGames.LibsignalSession.maxForwardJumps)
          lam 1 qep tL t (A o))) :=
    fun b => bind_congr fun o => by
      rw [Computational.Proofs.SessionCostedFig8.BucketPRNGSwap.redPRNGAuthBucketHybridProg_branch_eval_atomic
          Dh encPt C ℓ encT (idOf o) lam qep q tL t (A o) (hqA o) b,
        Computational.Proofs.SessionCostedFig8.BucketPRNGSwap.redPRNGAuthBucketHybrid_atomic_eq
          Dh (_root_.CryptoGames.Ratchet.rootPRNG C.F encPt) C ℓ encT (idOf o) lam B0 q 1 qep tL t
          (Nat.le_refl _) (A o) q (hqA o) (Nat.le_refl q) (hshA o)]
  rw [hBr true, hBr false]

/-- Mixture Fig. 8 `(tL, par)`-bucket authenticity sum on `simFig8RedProg` is bounded above by
`fig8MixShortAuthV1` evaluated on `v1SessionReds`. -/
theorem fig8MixAuth_simFig8_le_fig8MixShortAuthV1 {α : Type} (Z : Crypto) (K : MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    let simAdv : α → Fig8Adv Pt ℓ := fun o =>
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
        ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
    2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
      𝒟[oa >>= fun o => _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthGame
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
        (2 + 1) (qep + 1) tL (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true} ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A := by
  let simAdv : α → Fig8Adv Pt ℓ := fun o =>
    (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
      ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
  have hqChall : ∀ o, SM.MakesAtMostQueries (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) q :=
    fun o => Thm1.challSim_queries (2 + 1) (qep + 1) (simAdv o) q
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_queries
        hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o))
  have hshChall : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ =>
        Computational.Proofs.ReductionDsl.Fig8Atomic.atomicShortPubB m.1)
      (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) :=
    fun o => SessionShort.challSim_sendOk (2 + 1) (qep + 1)
      (fun m : LibsignalMsgPublicPart × Plain ℓ =>
        Computational.Proofs.ReductionDsl.Fig8Atomic.atomicShortPubB m.1)
      (simAdv o)
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_sendAtomicShort
        hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o))
  exact Computational.Proofs.SessionCostedDFStage2Auth.fig8MixAuth_simFig8_le_fig8MixShortAuthV1_of_stage2Inst
    Z K hD hℓ Dh hDh encPt encT decT hinj hdum lam qep q hq32 oa ida idb
    (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A hq
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun tL _ =>
      fig8RedsInst_redCKAAuth_semantic_advAvg_advantage_stage2 Dh encPt Z ℓ hℓ encT oa
        (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q (healEpoch tL) tL
        (fun o => Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) hqChall hshChall)
    (fun tL _ t _ =>
      (fig8RedsInst_redPRNGAuth_semantic_advAvg_advantage_stage2 Dh encPt Z ℓ hℓ encT oa
        (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL t
        (fun o => Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) hqChall hshChall).symm.le)
    (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/-- Mixture Fig. 8 `Config.h2` privacy bias on `simFig8RedProg` is bounded above by
`fig8MixShortPrivV1` evaluated on `v1SessionReds`. -/
theorem fig8MixPriv_simFig8_le_fig8MixShortPrivV1 {α : Type} (Z : Crypto) (K : MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    let simAdv : α → Fig8Adv Pt ℓ := fun o =>
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
        ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) SM.Config.h2 (simAdv o)].boolBias ≤
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A :=
  Computational.Proofs.SessionCostedDFStage2Priv.fig8MixPriv_simFig8_le_fig8MixShortPrivV1_of_fsOk2q
    Z K hD hℓ Dh hDh encPt encT decT hinj hdum lam qep q hq32 oa ida idb
    (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A hq
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun simAdv heq =>
      SM.lemma18_h2_blank_mix_stage2
        (fun o => lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
        (2 + 1) (qep + 1) (by omega) oa
        (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (lBlank ℓ)
        (fun ⟨_, _⟩ ⟨_, _⟩ h => by dsimp [lBlank] at h ⊢; subst h; rfl)
        simAdv heq)
    (fun o i =>
      Computational.Proofs.SessionCostedFig8.RedFSUniSafePost.fig8RedsInst_priv_fsOk_2q_and_encAtomicShort
        Dh encPt Z protoSignalCodec rfl ℓ hℓ encT (idsOf (ida o) (idb o)) lam (qep + 1) q i _
        (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_queries
          hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o))
        (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_sendAtomicShort
          hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o))
        (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_guardedSMShort
          hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)))

/-- Fig. 8 H1 bias of the `libsignalToModularSchemeSim` mixture is bounded by `fig8MixShortAuthV1 + fig8MixShortPrivV1` on `v1SessionReds`. -/
theorem boolBias_mixFig8_le_fig8MixShortV1 {α : Type} (Z : Crypto) (K : MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1
        (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
          (idsOf (ida o) (idb o)) lam qep (A o))].boolBias ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A +
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A :=
  Computational.Proofs.SessionCostedDFStage2Auth.boolBias_mixFig8_le_fig8MixShortV1_of_bucketAndPriv
    Z K hℓ Dh encPt encT decT lam qep q oa ida idb
    (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A hq
    (fig8MixAuth_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh hDh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb A hq)
    (fig8MixPriv_simFig8_le_fig8MixShortPrivV1 Z K hD hℓ Dh hDh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb A hq)

/-- Twice `simCNoneWinEvent` of the mixture is bounded by `fig8MixShortAuthV1` on `v1SessionReds`. -/
theorem evalDist_mixSimCNoneWin_le_fig8MixShortAuthV1 {α : Type} (Z : Crypto) (K : MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    2 * 𝒟[oa >>= fun o => simCNoneWinEvent (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
        (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A :=
  Computational.Proofs.SessionCostedDFStage2Auth.evalDist_mixSimCNoneWin_le_fig8MixShortAuthV1_of_bucket
    Z K hℓ Dh encPt encT decT lam qep q oa ida idb
    (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A hq
    (fig8MixAuth_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh hDh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb A hq)

/-- Per-`o` costed hidden-salt bound matching the integrand of `hiddenSaltMixtureBound`. -/
@[expose] noncomputable def hiddenSaltBoundV1 (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (R : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  let qR := min (2 * q) (q + 2)
  let dfAdv := R.simDeliverForge.eval (fun _ => A) ()
  let challAdvDF := R.challSimDF.eval (fun _ => dfAdv) ()
  (∑ t ∈ Finset.Ico 2 ((qep + 1) + 2),
    let tL : Option ℕ := some (t - 2)
    (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        ((R.B_cka tL t).eval (fun _ => challAdvDF) ()) +
      PRFPRNG.advantage (rootPRNG Z.F encPt)
        ((R.B_prng tL t).eval (fun _ => challAdvDF) ()) +
      (∑ j ∈ Finset.range q,
        CryptoVerification.E2E.fsAeadAuthSlotSumBound Z qR R.fs
          (fun stage la => (R.B_fs stage la j tL t).eval (fun _ => challAdvDF) ())) +
      4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) +
    (∑ t ∈ Finset.Ico 3 ((qep + 1) + 2),
      let tL : Option ℕ := some (t - 3)
      (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          ((R.B_cka tL t).eval (fun _ => challAdvDF) ()) +
        PRFPRNG.advantage (rootPRNG Z.F encPt)
          ((R.B_prng tL t).eval (fun _ => challAdvDF) ()) +
        (∑ j ∈ Finset.range q,
          CryptoVerification.E2E.fsAeadAuthSlotSumBound Z qR R.fs
            (fun stage la => (R.B_fs stage la j tL t).eval (fun _ => challAdvDF) ())) +
        4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) +
    (∑ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∑ par ∈ ({false, true} : Finset Bool),
      (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          ((R.B_cka_u tL par).eval (fun _ => challAdvDF) ()) +
        (∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
          (PRFPRNG.advantage (rootPRNG Z.F encPt)
              ((R.B_prng_u tL par t).eval (fun _ => challAdvDF) ()) +
            (∑ j ∈ Finset.range q,
              CryptoVerification.E2E.fsAeadAuthSlotSumBound Z qR R.fs
                (fun stage la => (R.B_fs_u stage la j tL par t).eval (fun _ => challAdvDF) ())))) +
        4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) +
    spuriousStepTerm Z.F encPt Dh q qep +
    (qep + 1) * (qep + 2) * δ

theorem lintegral_mono_of_support {α : Type} (oa : ProbComp α) (f g : α → ℝ≥0∞)
    (h : ∀ o ∈ support oa, f o ≤ g o) :
    letI : MeasurableSpace α := ⊤
    ∫⁻ o, f o ∂𝒟[oa] ≤ ∫⁻ o, g o ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have hae : ∀ᵐ x ∂𝒟[oa], x ∈ support oa :=
    evalDist.ae_of_forall_mem_support oa (· ∈ support oa) MeasurableSet.of_discrete fun _ ho => ho
  exact lintegral_mono_ae (hae.mono h)

theorem lintegral_congr_of_support {α : Type} (oa : ProbComp α) (f g : α → ℝ≥0∞)
    (h : ∀ o ∈ support oa, f o = g o) :
    letI : MeasurableSpace α := ⊤
    ∫⁻ o, f o ∂𝒟[oa] = ∫⁻ o, g o ∂𝒟[oa] :=
  le_antisymm
    (lintegral_mono_of_support oa f g fun o ho => le_of_eq (h o ho))
    (lintegral_mono_of_support oa g f fun o ho => le_of_eq (h o ho).symm)

theorem evalDist_mixHiddenSalt_le_v1_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hHid : ∀ o ∈ support oa,
      let P := paramsV1 Z K (ida o) (idb o)
      LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) lam qep (A o) ≤
        hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o) (A o)) :
    𝒟[oa >>= fun o => LibsignalSimC.hiddenSaltGame (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT
        decT (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
      CryptoVerification.E2E.hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ
        oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral]
  refine (lintegral_mono_of_support oa _ _ hHid).trans_eq ?_
  unfold hiddenSaltBoundV1 CryptoVerification.E2E.hiddenSaltMixtureBound
  change (∫⁻ o, _ ∂𝒟[oa]) = _
  simp only [lintegral_add_left Measurable.of_discrete,
    lintegral_finsetSum _ fun _ _ => Measurable.of_discrete,
    lintegral_const, evalDist_apply_univ_eq_one, mul_one]

@[simp]
private lemma stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

private def toRefuseState {C : Type} (r : RefuseB0.RefuseState C) :
    RefuseCorrB0.RefuseState C :=
  ⟨r.epoch, r.idx, r.trans⟩

@[simp]
private lemma toRefuseState_epoch {C : Type} (r : RefuseB0.RefuseState C) :
    (toRefuseState r).epoch = r.epoch := rfl

private lemma toRefuseState_onSend {C : Type} (r : RefuseB0.RefuseState C) (P : Party) (c : C) :
    toRefuseState (r.onSend P c) = (toRefuseState r).onSend P c := rfl

private lemma toRefuseState_onAccept {C : Type} (r : RefuseB0.RefuseState C) (P : Party)
    (pos : SM.Pos) :
    toRefuseState (r.onAccept P pos) = (toRefuseState r).onAccept P pos := rfl

private lemma toRefuseState_onDeliver {C : Type} [DecidableEq C] (r : RefuseB0.RefuseState C)
    (P : Party) (c : C) :
    toRefuseState (r.onDeliver P c) = (toRefuseState r).onDeliver P c := by
  unfold RefuseB0.RefuseState.onDeliver RefuseCorrB0.RefuseState.onDeliver toRefuseState
  dsimp only
  cases List.find? (fun pc => pc.1.sender == P.other && decide (pc.2 = c)) r.trans <;> rfl

private lemma refuseCorrB0Impl_run_toRefuseState {St Msg Coins C : Type} [DecidableEq C]
    (q : (unifSpec + SM.spec St Msg Coins C).Domain) (r : RefuseB0.RefuseState C) :
    (RefuseCorrB0.refuseCorrB0Impl (St := St) (Msg := Msg) (Coins := Coins) (C := C) q).run
        (toRefuseState r) =
      Prod.map id toRefuseState <$>
        (RefuseB0.refuseCorrB0Impl (St := St) (Msg := Msg) (Coins := Coins) (C := C) q).run r := by
  rcases q with n | ((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change (StateT.lift (query (spec := unifSpec + SM.spec St Msg Coins C) (.inl n)) :
        RefuseCorrB0.RefuseM St Msg Coins C _).run (toRefuseState r) =
      Prod.map id toRefuseState <$>
        (StateT.lift (query (spec := unifSpec + SM.spec St Msg Coins C) (.inl n)) :
          RefuseB0.RefuseM St Msg Coins C _).run r
    simp [map_eq_bind_pure_comp]
  · change (RefuseCorrB0.refuseTransmit (P, m, rc)).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseTransmit (P, m, rc)).run r
    unfold RefuseCorrB0.refuseTransmit RefuseB0.refuseTransmit
    simp only [StateT.run_bind, stateT_run_lift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    cases res <;> simp [toRefuseState_onSend]
  · change (RefuseCorrB0.refuseChall (P, m₀, m₁, rc)).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseChall (P, m₀, m₁, rc)).run r
    unfold RefuseCorrB0.refuseChall RefuseB0.refuseChall
    simp only [StateT.run_bind, stateT_run_lift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    cases res <;> simp [toRefuseState_onSend]
  · change (RefuseCorrB0.refuseDeliver (P, c)).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseDeliver (P, c)).run r
    unfold RefuseCorrB0.refuseDeliver RefuseB0.refuseDeliver
    simp only [StateT.run_bind, stateT_run_lift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    cases res with
    | none => simp
    | some rr => cases rr <;> simp [toRefuseState_onDeliver]
  · change (RefuseCorrB0.refuseInject (P, c)).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseInject (P, c)).run r
    unfold RefuseCorrB0.refuseInject RefuseB0.refuseInject
    simp only [StateT.run_bind, stateT_run_lift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    cases res with
    | none => simp
    | some rr => cases rr <;> simp [toRefuseState_onAccept]
  · change (RefuseCorrB0.refuseCorr P).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseCorr P).run r
    unfold RefuseCorrB0.refuseCorr RefuseB0.refuseCorr
    rw [StateT.run_bind, StateT.run_bind, StateT.run_get, StateT.run_get,
      pure_bind, pure_bind, toRefuseState_epoch]
    split_ifs <;> simp [map_eq_bind_pure_comp]

theorem refuseCorrB0_eq {St Msg Coins C : Type} [DecidableEq C]
    (A : SM.Adversary St Msg Coins C) :
    RefuseB0.refuseCorrB0 A = A.refuseCorrB0 := by
  unfold RefuseB0.refuseCorrB0 SM.Adversary.refuseCorrB0
  exact run'_simulateQ_eq_of_inv_dis RefuseB0.refuseCorrB0Impl RefuseCorrB0.refuseCorrB0Impl
    (fun _ => True) toRefuseState (fun _ => False)
    (fun _ _ _ _ _ _ => trivial)
    (fun t r _ _ => (refuseCorrB0Impl_run_toRefuseState t r).symm)
    A (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false A 0) {} trivial

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem prfAdvantage_prefixPrfAvg_congr_of_support {α Key Input Tag : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Tag]
    (mac : MACScheme Key Input Tag) (oa : ProbComp α)
    (D₁ D₂ : α → MACScheme.PRFAdversary Input Tag)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    mac.prfAdvantage (prefixPrfAvg oa D₁) = mac.prfAdvantage (prefixPrfAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => mac.branch b (D₁ o)] =
      𝒟[oa >>= fun o => mac.branch b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change mac.prfAdvantage (prfAvg oa D₁) = mac.prfAdvantage (prfAvg oa D₂)
  rw [MACScheme.prfAdvantage_eq_boolDist, MACScheme.prfAdvantage_eq_boolDist,
    prfBranch_avg, prfBranch_avg, prfBranch_avg, prfBranch_avg, hb true, hb false]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem prgAdvantage_prefixPrgAvg_congr_of_support {α S R : Type}
    [SampleableType S] [SampleableType R]
    (prg : PRGScheme S R) (oa : ProbComp α)
    (D₁ D₂ : α → PRGScheme.PRGAdversary R)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    prg.prgAdvantage (prefixPrgAvg oa D₁) = prg.prgAdvantage (prefixPrgAvg oa D₂) := by
  have hr : 𝒟[oa >>= fun o => prg.prgRealExperiment (D₁ o)] =
      𝒟[oa >>= fun o => prg.prgRealExperiment (D₂ o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  have hi : 𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D₁ o)] =
      𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D₂ o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change prg.prgAdvantage (prgAvg oa D₁) = prg.prgAdvantage (prgAvg oa D₂)
  unfold PRGScheme.prgAdvantage
  rw [prgReal_avg, prgReal_avg, prgIdeal_avg, prgIdeal_avg, hr, hi]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem ckaAdvantage_prefixAdvAvg_congr_of_support {α Key State Coins Msg CKey : Type}
    [SampleableType Key] [SampleableType Coins] [SampleableType CKey]
    (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ) (oa : ProbComp α)
    (D₁ D₂ : α → CKA.Adversary State Coins Msg CKey)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    CKA.advantage cka Δ tStar (prefixAdvAvg oa D₁) =
      CKA.advantage cka Δ tStar (prefixAdvAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => CKA.branch cka Δ tStar b (D₁ o)] =
      𝒟[oa >>= fun o => CKA.branch cka Δ tStar b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change CKA.advantage cka Δ tStar (advAvg oa D₁) = CKA.advantage cka Δ tStar (advAvg oa D₂)
  rw [CKA.advantage_eq_boolDist, CKA.advantage_eq_boolDist,
    ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, hb true, hb false]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem prngAdvantage_prefixAdvAvg_congr_of_support {α Key State Input Output : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Input] [SampleableType Output]
    (P : PRFPRNG Key State Input Output) (oa : ProbComp α)
    (D₁ D₂ : α → PRFPRNG.Adversary State Input Output)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    PRFPRNG.advantage P (prefixAdvAvg oa D₁) = PRFPRNG.advantage P (prefixAdvAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => PRFPRNG.branch P b (D₁ o)] =
      𝒟[oa >>= fun o => PRFPRNG.branch P b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change PRFPRNG.advantage P (advAvg oa D₁) = PRFPRNG.advantage P (advAvg oa D₂)
  rw [PRFPRNG.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist,
    prngBranch_avg, prngBranch_avg, prngBranch_avg, prngBranch_avg, hb true, hb false]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem wireOtccaAdvantage_prefixWireAvg_congr_of_support {α K AD H M M' C T : Type}
    [SampleableType K] [SampleableType C] [SampleableType T] [DecidableEq AD] [DecidableEq T]
    (ae : WireAEAD K AD H M M' C T) (oa : ProbComp α)
    (D₁ D₂ : α → WireAEAD.WireAdversary AD H M M' T)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    ae.wireOtccaAdvantage (prefixWireAvg oa D₁) = ae.wireOtccaAdvantage (prefixWireAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => FSMix.wBranch ae b (D₁ o)] =
      𝒟[oa >>= fun o => FSMix.wBranch ae b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change ae.wireOtccaAdvantage (FSMix.wireAvg oa D₁) = ae.wireOtccaAdvantage (FSMix.wireAvg oa D₂)
  rw [FSMix.wireOtccaAdvantage_eq_boolDist_wBranch, FSMix.wireOtccaAdvantage_eq_boolDist_wBranch,
    FSMix.wBranch_avg, FSMix.wBranch_avg, FSMix.wBranch_avg, FSMix.wBranch_avg, hb true, hb false]

omit [Zero Pt] [SampleableType Pt] in
theorem fsShortBoundMixWith_congr_of_support {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    {encT : Pt → PublicKey} (oa : ProbComp α) {idOf : α → Party → IdentityKey} (q qd : ℕ)
    (R : ∀ o, FsCostedReds C codec ℓ encT (idOf o))
    (A₁ A₂ : α → FsAdv Pt ℓ) (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    fsAeadMixtureBound C codec ℓ oa q qd R A₁ = fsAeadMixtureBound C codec ℓ oa q qd R A₂ := by
  unfold fsAeadMixtureBound fsChainPrgMixtureTerm fsSaltWireMixtureTerm
  refine congrArg (· + 4 * ((qd : ℝ≥0∞) * macForgeryProb C.F)) (congrArg (2 * ·) ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  have h1 := prgAdvantage_prefixPrgAvg_congr_of_support (lChainPRG C.F (Thm5.slotToHybridHopIndex q j / 2)) oa
    (fun o mt => evalTwoStage1 ((R o).prgRedZero (Thm5.slotToHybridHopIndex q j)) q false
      (fun _ => pubToADCosted (R o) (A₁ o)) mt)
    (fun o mt => evalTwoStage1 ((R o).prgRedZero (Thm5.slotToHybridHopIndex q j)) q false
      (fun _ => pubToADCosted (R o) (A₂ o)) mt)
    (fun o ho => by rw [hA o ho])
  have h2 := prfAdvantage_prefixPrfAvg_congr_of_support (lSaltPRF32 C.F) oa
    (fun o => (R o).lSaltRed.eval (fun _ => ((R o).slotSaltRed (Thm5.slotToHybridHopIndex q j)).eval
      (fun _ => multiSlotAdvCosted q (R o) (Thm5.isLookaheadHop (Thm5.slotToHybridHopIndex q j)) (A₁ o)) ()) ())
    (fun o => (R o).lSaltRed.eval (fun _ => ((R o).slotSaltRed (Thm5.slotToHybridHopIndex q j)).eval
      (fun _ => multiSlotAdvCosted q (R o) (Thm5.isLookaheadHop (Thm5.slotToHybridHopIndex q j)) (A₂ o)) ()) ())
    (fun o ho => by rw [hA o ho])
  have h3 := wireOtccaAdvantage_prefixWireAvg_congr_of_support (lWire C codec ℓ) oa
    (fun o => (R o).lWireRed.eval (fun _ => ((R o).slotWireRed (Thm5.slotToHybridHopIndex q j)).eval
      (fun _ => multiSlotAdvCosted q (R o) (Thm5.isLookaheadHop (Thm5.slotToHybridHopIndex q j)) (A₁ o)) ()) ())
    (fun o => (R o).lWireRed.eval (fun _ => ((R o).slotWireRed (Thm5.slotToHybridHopIndex q j)).eval
      (fun _ => multiSlotAdvCosted q (R o) (Thm5.isLookaheadHop (Thm5.slotToHybridHopIndex q j)) (A₂ o)) ()) ())
    (fun o ho => by rw [hA o ho])
  rw [h1, h2, h3]

omit [Zero Pt] [SampleableType Pt] in
private theorem fsAuthMixComp_congr_of_support {α : Type} (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    {encT : Pt → PublicKey} (oa : ProbComp α) {idOf : α → Party → IdentityKey} (qR : ℕ)
    (R : ∀ o, FsCostedReds C codec ℓ encT (idOf o))
    (A₁ A₂ : Bool → Bool → α → FsAdv Pt ℓ)
    (hA : ∀ stage la, ∀ o ∈ support oa, A₁ stage la o = A₂ stage la o) :
    fsAeadAuthMixtureCompBound C codec ℓ oa qR R A₁ =
      fsAeadAuthMixtureCompBound C codec ℓ oa qR R A₂ := by
  unfold fsAeadAuthMixtureCompBound
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun j _ => ?_)
  dsimp only
  set m := Thm5.slotToHybridHopIndex qR j
  set la := Thm5.isLookaheadHop m
  have h1 := prgAdvantage_prefixPrgAvg_congr_of_support (lChainPRG C.F (m / 2)) oa
    (fun o mt => evalTwoStage1 ((R o).prgRedAuth m) qR false
      (fun _ => pubToADCosted (R o) (A₁ false la o)) mt)
    (fun o mt => evalTwoStage1 ((R o).prgRedAuth m) qR false
      (fun _ => pubToADCosted (R o) (A₂ false la o)) mt)
    (fun o ho => by rw [hA false la o ho])
  have h2 := prfAdvantage_prefixPrfAvg_congr_of_support (lSaltPRF32 C.F) oa
    (fun o => (R o).lSaltRed.eval (fun _ => ((R o).slotSaltRed m).eval
      (fun _ => multiSlotAdvAuthCosted qR (R o) la (A₁ false la o)) ()) ())
    (fun o => (R o).lSaltRed.eval (fun _ => ((R o).slotSaltRed m).eval
      (fun _ => multiSlotAdvAuthCosted qR (R o) la (A₂ false la o)) ()) ())
    (fun o ho => by rw [hA false la o ho])
  have h3 := wireOtccaAdvantage_prefixWireAvg_congr_of_support (lWire C codec ℓ) oa
    (fun o => (R o).lWireRed.eval (fun _ => ((R o).slotWireRed m).eval
      (fun _ => multiSlotAdvAuthCosted qR (R o) la (A₁ true la o)) ()) ())
    (fun o => (R o).lWireRed.eval (fun _ => ((R o).slotWireRed m).eval
      (fun _ => multiSlotAdvAuthCosted qR (R o) la (A₂ true la o)) ()) ())
    (fun o ho => by rw [hA true la o ho])
  rw [h1, h2, h3]

theorem fig8MixShortAuthV1_congr_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A₁ A₂ : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A₁ =
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A₂ := by
  unfold fig8MixShortAuthV1
  dsimp only
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun tL _ => ?_)
  refine congrArg (· + 8 * CryptoVerification.LibsignalSession.macForgeryTerm Z q) ?_
  have hc := ckaAdvantage_prefixAdvAvg_congr_of_support (dhScheme Dh) 1 (healEpoch tL) oa
    (fun o => ((R o).fig8.redCKAAuth tL).eval (fun _ => (R o).fig8.challSim.eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redCKAAuth tL).eval (fun _ => (R o).fig8.challSim.eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  refine congrArg₂ (· + ·) hc (Finset.sum_congr rfl fun t _ => ?_)
  have hp := prngAdvantage_prefixAdvAvg_congr_of_support (rootPRNG Z.F encPt) oa
    (fun o => ((R o).fig8.redPRNGAuth tL t).eval (fun _ => (R o).fig8.challSim.eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redPRNGAuth tL t).eval (fun _ => (R o).fig8.challSim.eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  refine congrArg₂ (· + ·) (congrArg (2 * ·) hp) (Finset.sum_congr rfl fun j _ => ?_)
  exact fsAuthMixComp_congr_of_support Z protoSignalCodec ℓ oa (min (2 * q) (q + 2))
    (fun o => (R o).fs) _ _ fun stage la o ho => by rw [hA o ho]

theorem fig8MixShortPrivV1_congr_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A₁ A₂ : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A₁ =
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A₂ := by
  unfold fig8MixShortPrivV1
  dsimp only
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun i _ => ?_)
  have hsum :
      (∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
        (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
            (prefixAdvAvg oa fun o => ((R o).fig8.redCKAPriv tL i).eval
              (fun _ => ((R o).fig8.privRedB i).eval
                (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ()) +
          2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
            (prefixAdvAvg oa fun o => ((R o).fig8.redCKAPrivU tL i).eval
              (fun _ => ((R o).fig8.privRedB i).eval
                (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ()) +
          2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
            (prefixAdvAvg oa fun o => ((R o).fig8.redPRNGPriv tL i).eval
              (fun _ => ((R o).fig8.privRedB i).eval
                (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ()))) =
      (∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
        (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
            (prefixAdvAvg oa fun o => ((R o).fig8.redCKAPriv tL i).eval
              (fun _ => ((R o).fig8.privRedB i).eval
                (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ()) +
          2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
            (prefixAdvAvg oa fun o => ((R o).fig8.redCKAPrivU tL i).eval
              (fun _ => ((R o).fig8.privRedB i).eval
                (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ()) +
          2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
            (prefixAdvAvg oa fun o => ((R o).fig8.redPRNGPriv tL i).eval
              (fun _ => ((R o).fig8.privRedB i).eval
                (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ()))) := by
    refine Finset.sum_congr rfl fun tL _ => ?_
    have hc := ckaAdvantage_prefixAdvAvg_congr_of_support (dhScheme Dh) 1 (healEpoch tL) oa
      (fun o => ((R o).fig8.redCKAPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
        (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
      (fun o => ((R o).fig8.redCKAPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
        (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
      (fun o ho => by rw [hA o ho])
    have hcu := ckaAdvantage_prefixAdvAvg_congr_of_support (dhScheme Dh) 1 (healEpoch tL) oa
      (fun o => ((R o).fig8.redCKAPrivU tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
        (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
      (fun o => ((R o).fig8.redCKAPrivU tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
        (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
      (fun o ho => by rw [hA o ho])
    have hp := prngAdvantage_prefixAdvAvg_congr_of_support (rootPRNG Z.F encPt) oa
      (fun o => ((R o).fig8.redPRNGPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
        (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
      (fun o => ((R o).fig8.redPRNGPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
        (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
      (fun o ho => by rw [hA o ho])
    rw [hc, hcu, hp]
  have hf1 := fsShortBoundMixWith_congr_of_support Z protoSignalCodec ℓ oa (min (2 * q) (q + 2)) q
    (fun o => (R o).fs)
    (fun o => ((R o).fig8.redFSPriv i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redFSPriv i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  have hf2 := fsShortBoundMixWith_congr_of_support Z protoSignalCodec ℓ oa (min (2 * q) (q + 2)) q
    (fun o => (R o).fs)
    (fun o => ((R o).fig8.redFSPrivCoin i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redFSPrivCoin i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  rw [hsum, hf1, hf2]

theorem hiddenSaltBoundMixV1_congr_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A₁ A₂ : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    CryptoVerification.E2E.hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R
        A₁ =
      CryptoVerification.E2E.hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R
        A₂ := by
  let _ : MeasurableSpace α := ⊤
  unfold CryptoVerification.E2E.hiddenSaltMixtureBound
  dsimp only
  refine congrArg (· + _) (congrArg (· + _)
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_))
  · refine Finset.sum_congr rfl fun t _ => ?_
    refine congrArg (· + 4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_)
    · exact lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]
    · exact lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]
    · exact Finset.sum_congr rfl fun j _ =>
        lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]
  · refine Finset.sum_congr rfl fun t _ => ?_
    refine congrArg (· + 4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_)
    · exact lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]
    · exact lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]
    · exact Finset.sum_congr rfl fun j _ =>
        lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]
  · refine Finset.sum_congr rfl fun tL _ => Finset.sum_congr rfl fun par _ => ?_
    refine congrArg (· + 4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)
      (congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun t _ => ?_))
    · exact lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]
    · refine congrArg₂ (· + ·) ?_ ?_
      · exact lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]
      · exact Finset.sum_congr rfl fun j _ =>
          lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]

theorem uTermShortMixV1_congr_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A₁ A₂ : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    CryptoVerification.E2E.uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A₁ =
      CryptoVerification.E2E.uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R
        A₂ := by
  have ha := fig8MixShortAuthV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
    (fun o => RefuseB0.refuseCorrB0 (A₁ o)) (fun o => RefuseB0.refuseCorrB0 (A₂ o))
    (fun o ho => by rw [hA o ho])
  have hp := fig8MixShortPrivV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
    (fun o => RefuseB0.refuseCorrB0 (A₁ o)) (fun o => RefuseB0.refuseCorrB0 (A₂ o))
    (fun o ho => by rw [hA o ho])
  have he := prgAdvantage_prefixPrgAvg_congr_of_support (rootKdfAsPrg Z.F (encPt lam)) oa
    (fun o rc => (R o).epoch0Red.eval (fun _ => RefuseB0.refuseCorrB0 (A₁ o)) rc)
    (fun o rc => (R o).epoch0Red.eval (fun _ => RefuseB0.refuseCorrB0 (A₂ o)) rc)
    (fun o ho => by rw [hA o ho])
  have hh := hiddenSaltBoundMixV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R
    (fun o => RefuseB0.refuseCorrB0 (A₁ o)) (fun o => RefuseB0.refuseCorrB0 (A₂ o))
    (fun o ho => by rw [hA o ho])
  have hu := prgAdvantage_prefixPrgAvg_congr_of_support (rootKdfAsPrg Z.F (encPt lam)) oa
    (fun o rc => (R o).uniformStartRed.eval (fun _ => RefuseB0.refuseCorrB0 (A₁ o)) rc)
    (fun o rc => (R o).uniformStartRed.eval (fun _ => RefuseB0.refuseCorrB0 (A₂ o)) rc)
    (fun o ho => by rw [hA o ho])
  unfold CryptoVerification.E2E.uniformStartMixtureBound
  rw [ha, hp, he, hh, hu]

omit [SampleableType Pt] in
theorem simDeliverForgeClamp_sendShort {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) {ℓ : ℕ} (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (CBC.Plain ℓ) PQC Bytes) :
    HeadlineV1.SendMsgsOkDF (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1.shortB)
      (LibsignalSim.simDeliverForgeClamp P Dh encPt encT decT lam qep B A) :=
  Computational.Proofs.SessionCostedDFStage2.simDeliverForgeClamp_sendShort
    P hL Dh encPt encT decT lam qep B A

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hooksCKAShifted_commit_vR {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (l tStar : ℕ)
    (ctx : SM.Engine.Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (old new : SM.Engine.VP (Option Γ) T RSt SS RS) (h : DeliverForge.CKAStateShifted Γ T I) :
    ∀ res ∈ support (((DeliverForge.hooksCKAShifted cka prng fs l tStar).commit
        ctx P old new).run h),
      ∀ new', res.1 = some new' → new'.vR = new.vR :=
  Computational.Proofs.SessionCostedDFStage2.hooksCKAShifted_commit_vR
    cka prng fs l tStar ctx P old new h

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hooksCKAShifted_vrInv_fromAEADPRG {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip l tStar : ℕ) :
    SM.Engine.HooksVRInv (SM.Engine.RSReach maxSkip)
      (DeliverForge.hooksCKAShifted cka prng (FSAEAD.fromAEADPRG ae G maxSkip) l tStar) :=
  Computational.Proofs.SessionCostedDFStage2.hooksCKAShifted_vrInv_fromAEADPRG
    cka prng ae G maxSkip l tStar

end EvalBridges

end

end CryptoVerification.E2E

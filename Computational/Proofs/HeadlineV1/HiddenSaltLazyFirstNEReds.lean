/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds2
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECell
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperSim
public import Computational.Proofs.SessionCostedDF -- proof-setup: allow-public-import
import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim
public import Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs
import Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds
import Computational.Proofs.SessionCostedFig8.DFProgBucketBounds
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA
import Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.HeadlineV1.DeliverForgePaperUnshiftedPotOK
import Computational.Proofs.HeadlineV1.DeliverForgePaperMultiBucketPotOK
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti
import Computational.Proofs.HeadlineV1.Stage2RouterHelpers
import Computational.Proofs.HeadlineV1.Stage2BucketPRNGSwap
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperBucketPRNG
import Computational.Proofs.SessionCostedFig8.BundlesMultiFs
import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS
import Computational.Proofs.HeadlineV1.Stage2BucketCKASwap
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3B1
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3B2
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3Bucket
import Computational.Proofs.ReductionDsl.SM.DeliverForgeBucketSimEval
import Computational.Proofs.E2E.SpkCostedEval
import Computational.Proofs.E2E.SpkHop2
import Computational.Proofs.E2E.SpkHop2A
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdSkip
import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
import Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc
import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepSend
import Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap
import Computational.Proofs.HeadlineV1.CouplingV1
import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.PubRed
import Computational.Proofs.ReductionDsl.SpkHop2Red
import Computational.Proofs.ReductionDsl.SpkLeakRed
import Computational.Proofs.ReductionDsl.SpkLeakRedU
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.SessionCostedFig8.BundlesEval
import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap

/-!
# Paper-Semantics Session Reductions and Cell-Sum Bridge

Defines the paper-semantics `DeliverForge` session reduction package `v1SessionRedsPaper` from
3-way case-split CKA, PRF-PRNG, and FS-AEAD reductions, proves `sessionCostedReductionsBounded`,
and bounds the per-cell and summed advantage terms by `hiddenSaltBoundV1`.-/

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators ENNReal
open ReductionDsl ReductionDsl.Comp OracleSpec OracleComp ENNReal
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Engine.RedPRNG CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge
namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.SM.Thm1 CryptoVerification.LibsignalSession
open CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst CryptoGames.LibsignalSession
open CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

/-- Paper-engine CKA reduction for cell `(tL, t)` on `challSimDF'Paper (2 + 1) (qep + 1) dfAdv`. -/
@[expose] def redCKAHiddenSaltPaperDF {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    DeliverForge.redCKAAuthDFShiftedDir2Paper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam (qep + 1) (t - 1) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else if 3 ≤ t ∧ tL = some (t - 3) then
    DeliverForge.redCKAAuthDFShiftedPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) (t - 2) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else
    DeliverForge.redCKAAuthDFPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) tL t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)

/-- Paper-engine PRF-PRNG reduction for cell `(tL, t)` on
`challSimDF'Paper (2 + 1) (qep + 1) dfAdv`. -/
@[expose] def redPRNGHiddenSaltPaperDF {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    DeliverForge.redPRNGAuthDFShiftedDir2Paper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam (qep + 1) (t - 1) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else if 3 ≤ t ∧ tL = some (t - 3) then
    DeliverForge.redPRNGAuthDFShiftedPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) (t - 2) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else
    DeliverForge.redPRNGAuthDFPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) tL t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)

/-- Paper-engine FS-AEAD reduction for cell `(tL, t)` and session `j` on
`challSimDF'Paper (2 + 1) (qep + 1) dfAdv`. -/
@[expose] def redFSHiddenSaltPaperDF {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    DeliverForge.redFSAuthDFShiftedDir2Paper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam (qep + 1) j (t - 1) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else if 3 ≤ t ∧ tL = some (t - 3) then
    DeliverForge.redFSAuthDFShiftedPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) j (t - 2) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else
    DeliverForge.redFSAuthDFPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) j tL t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)

/-- Concrete per-cell advantage term for cell `(tL, t)` under the paper engine on `dfAdv`. -/
@[expose] noncomputable def hiddenSaltCellTermPaperDF {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    ℝ≥0∞ :=
  CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
    (redCKAHiddenSaltPaperDF P ℓ Dh encPt encT idOf lam qep tL t dfAdv) +
  PRFPRNG.advantage (Ratchet.rootPRNG P.C.F encPt)
    (redPRNGHiddenSaltPaperDF P ℓ Dh encPt encT idOf lam qep tL t dfAdv) +
  ∑ j ∈ Finset.range q,
    FSAEAD.advantage (lFS P.C P.codec ℓ encT idOf 25000)
      (redFSHiddenSaltPaperDF P ℓ Dh encPt encT idOf lam qep j tL t dfAdv)

end CryptoGames.LibsignalSM.Proofs.Refinement

namespace CryptoVerification.LibsignalSession

open _root_.ReductionDsl OracleSpec OracleComp _root_.CryptoGames _root_.CryptoGames.SM
  _root_.CryptoGames.SM.Construction _root_.CryptoGames.Ratchet _root_.CryptoGames.LibsignalSM
  _root_.CryptoGames.LibsignalSession _root_.CryptoVerification.LibsignalSession
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded bits_succ_le
  bits_le_bits_qep_add cInTransitE_cost_le cCompContainsE_cost_le vRecvC_cost_le
  cTrivialE_cost_le commitEC_cost_le modeCfgEC_injectFullE_cost_le esG_cost esH_cost esSetH_cost
  esSetG_cost esAbort_cost pGet_cost cGsSt_cost cGsSetWin_cost cRecPos_cost otherE_cost
  v0_cost v1_cost v2_cost v3_cost v4_cost implEC_cost_le authOutE_cost_le
  initPRNGEStateC_cost_le initFSEStateC_cost_le hooksPRNGC_costBounded hooksFSC_costBounded
  hooksFSC_costBounded_linear)

section ShiftedPaperDeliverForgeCost

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

local notation "OO_cka" =>
  CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "S_cka" => CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hkCKAShiftedC" =>
  SM.Construction.hooksCKAShiftedC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "hkPRNGC" =>
  SM.Construction.hooksPRNGC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "hkFSC" =>
  SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redCKADir2P" =>
  SM.Construction.redCKAAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redCKAShiftedP" =>
  SM.Construction.redCKAAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redCKAP" =>
  SM.Construction.redCKAAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redPRNGDir2P" =>
  SM.Construction.redPRNGAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redPRNGShiftedP" =>
  SM.Construction.redPRNGAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redPRNGP" =>
  SM.Construction.redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redFSDir2P" =>
  SM.Construction.redFSAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redFSShiftedP" =>
  SM.Construction.redFSAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redFSP" =>
  SM.Construction.redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)

/-- Case-split `B_cka` paper reduction program (3-way dispatch). -/
def redCKAAuthDFCasePaperProg (L B qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO_cka
      (CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (SM.specDF (SM.Construction.PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then redCKADir2P L B qep maxSkip (t - 1) t
  else if 3 ≤ t ∧ tL = some (t - 3) then redCKAShiftedP L B 1 qep maxSkip (t - 2) t
  else redCKAP L B 1 qep maxSkip tL t

/-- Case-split `B_prng` paper reduction program (3-way dispatch). -/
def redPRNGAuthDFCasePaperProg (L B qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (PRFPRNG.prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (SM.specDF (SM.Construction.PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (PRFPRNG.prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then redPRNGDir2P L B qep maxSkip (t - 1) t
  else if 3 ≤ t ∧ tL = some (t - 3) then redPRNGShiftedP L B 1 qep maxSkip (t - 2) t
  else redPRNGP L B 1 qep maxSkip tL t

/-- Case-split `B_fs` paper reduction program (3-way dispatch). -/
def redFSAuthDFCasePaperProg (L B qep maxSkip j : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (PRFPRNG.fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (SM.specDF (SM.Construction.PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (PRFPRNG.prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then redFSDir2P L B qep maxSkip j (t - 1) t
  else if 3 ≤ t ∧ tL = some (t - 3) then redFSShiftedP L B 1 qep maxSkip j (t - 2) t
  else redFSP L B 1 qep maxSkip j tL t

local notation "redCKACaseP" =>
  redCKAAuthDFCasePaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redPRNGCaseP" =>
  redPRNGAuthDFCasePaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redFSCaseP" =>
  redFSAuthDFCasePaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)

private lemma hdrEqE_cost_le {Γ'}
    (c₁ c₂ : Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.hdrEqE c₁ c₂).cost ≤ c₁.cost + c₂.cost + 40 := by
  have hmax11 : max 1 1 = 1 := rfl
  have hmax14 : max 1 4 = 4 := rfl
  simp only [SM.Engine.hdrEqE, SM.Engine.optTEqE, CKA.ckaOps, Expr.cost,
    v0_cost, v1_cost, hmax11, hmax14, Nat.reduceAdd]; omega

private lemma deliverForgeEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : SM.Construction.Mode) (hhk : HooksCostBounded hk H) {Γ'}
    (es : Expr OO_cka Γ' (SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
      (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    (SM.Engine.deliverForgeEC hk L 3 qep (SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L +
        ReductionDsl.bits qep + ReductionDsl.bits mo.tStar + 4210 := by
  have hqep1 := bits_succ_le qep
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 := .prod (SM.Engine.esTy vpT hsT) (.prod .bool (.prod hdrCtT hdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (SM.Engine.esG (O' := OO_cka) (.fst .v0)) (SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ1)
    (SM.Engine.esG (O' := OO_cka) (.fst .v1)) (SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hcc1 := cCompContainsE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (SM.Engine.esG (.fst .v1)) (SM.Engine.cRecPos .v0)
  have hhe1 := hdrEqE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1) (SM.Engine.esH (.fst .v1))
    (SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have htr := cTrivialE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ2) (SM.Engine.esG (.fst .v4))
    (.pair (SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ2) (SM.Engine.esSetH (.fst .v4) (.snd .v2))
    (SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    Expr.cost, v0_cost, v1_cost, v2_cost, v4_cost, Nat.reduceAdd]
    at hit0 hit1 hcc1 hhe1 hvr htr hcm hij
  simp only [SM.Engine.deliverForgeEC, SM.orE, SM.isSomeE, SM.Engine.cGsWin, SM.Engine.esMk,
    SM.posEpoch, cRecPos_cost, esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost,
    Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Nat.reduceAdd]; omega

private lemma implECDF_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep maxSkip : ℕ)
    (mo : SM.Construction.Mode) (hhk : HooksCostBounded hk H) {Γ'}
    (es : Expr OO_cka Γ' (SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.implECDF hk L 3 qep maxSkip (SM.Engine.modeCfgEC OO_cka mo) mo.policy es q).cost ≤
      es.cost + q.cost + 18650 * L +
        L * (ReductionDsl.bits (mo.tL.getD 0) + 2 * ReductionDsl.bits mo.tStar + 40) +
        3 * H + 6 * ReductionDsl.bits qep + (ReductionDsl.bits (mo.tL.getD 0) + 3) +
        6 * ReductionDsl.bits mo.tStar +
        (maxSkip + 1) + 22300 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := SM.Engine.esTy vpT hsT
  let smqT := CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let dfqT : Ty S_cka := .prod .bool (.prod hdrCtT hdrCtT)
  let smqDFT := CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod esT smqDFT :: Γ'
  have himpl := implEC_cost_le hk H L qep maxSkip mo hhk (Γ' := smqT :: Γ0) (.fst .v1) .v0
  have hdf := deliverForgeEC_cost_le hk H L qep mo hhk (Γ' := dfqT :: Γ0) (.fst .v1) .v0
  simp only [v0_cost, v1_cost, Expr.cost, Nat.reduceAdd] at himpl hdf
  simp only [SM.Engine.implECDF, Comp.cost, Expr.cost, v0_cost, Nat.reduceAdd]; omega

private lemma cAfterCorrShiftedE_cost_le_cAfterCorrE {O' : Ops S_cka} {vpT : Ty S_cka}
    (L l : ℕ) {Γ'} (s : Expr O' Γ' (SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (SM.Engine.cAfterCorrShiftedE L l s p).cost ≤
      (SM.Engine.cAfterCorrE L s p).cost + 36 * ReductionDsl.bits l + 650 := by
  have hl1 := ReductionDsl.bits_mono (Nat.sub_le l 1)
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  simp only [SM.Engine.cAfterCorrShiftedE, SM.Engine.cAfterCorrE, SM.Engine.cGsMk, SM.Engine.cLeakE,
    SM.maxOptE, SM.maxN, SM.leN, SM.boolEq, SM.otherE, SM.pGet, SM.Engine.cRecPos, SM.posSender,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    Expr.cost, v0_cost, v1_cost, v2_cost, hb1, Nat.reduceAdd]; omega

private lemma leakDoomE_cost_le_add {O' : Ops S_cka} {vpT : Ty S_cka}
    (L : ℕ) (π : SM.Engine.Policy) {Γ'} (g g₁ g₂ : Expr O' Γ' (SM.Engine.cGsTy vpT)) {d : ℕ}
    (h : g₁.cost ≤ g₂.cost + d) :
    (SM.Engine.leakDoomE L π g g₁).cost ≤ (SM.Engine.leakDoomE L π g g₂).cost + d := by
  simp only [SM.Engine.leakDoomE, Expr.cost]; omega

private lemma corrECShifted_cost_le_corrEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (L l : ℕ) (π : SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    (SM.Engine.corrECShifted hk L l π es p).cost ≤
      (SM.Engine.corrEC hk L π es p).cost + 72 * ReductionDsl.bits l + 1300 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let psT := CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod (SM.Engine.esTy vpT hsT) .bool :: Γ'
  let Γ1 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ0
  have hac0 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hld := leakDoomE_cost_le_add (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0))
    (SM.Engine.cAfterCorrShiftedE L l (SM.Engine.esG (.fst .v0)) (.snd .v0))
    (SM.Engine.cAfterCorrE L (SM.Engine.esG (.fst .v0)) (.snd .v0)) (Nat.add_assoc _ _ _ ▸ hac0)
  have hac1 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ1)
    (SM.Engine.esG (.fst .v2)) (.snd .v2)
  simp only [SM.Engine.corrECShifted, SM.Engine.corrEC, SM.orE, SM.Engine.esMk,
    Comp.cost, Expr.cost]; omega

private lemma implECDFShifted_cost_le_implECDF {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip : ℕ) (cfg : SM.Engine.ConfigEC OO_cka) (π : SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.implECDFShifted hk L l Δ qep maxSkip cfg π es q).cost ≤
      (SM.Engine.implECDF hk L Δ qep maxSkip cfg π es q).cost + 72 * ReductionDsl.bits l + 1300 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := SM.Engine.esTy vpT hsT
  let smqT := CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smqDFT := CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ_cr : List (Ty S_cka) := .bool :: .prod esT smqT :: smqT :: .prod esT smqDFT :: Γ'
  have hcr := corrECShifted_cost_le_corrEC hk L l π (Γ' := Γ_cr) (.fst .v1) .v0
  simp only [SM.Engine.implECDFShifted, SM.Engine.implECDF, SM.Engine.implECShifted,
    SM.Engine.implEC, Comp.cost, Expr.cost]; omega

private lemma hooksCKAShiftedC_costBounded (B l tStar : ℕ) :
    HooksCostBounded (hkCKAShiftedC B l tStar)
      (5 * ReductionDsl.bits l + ReductionDsl.bits tStar + (B + 1) + 530) := by
  refine
    { startSend_le := fun h ctx p t γv σ r => by
        have hl1 := bits_succ_le l
        have hl2 : ReductionDsl.bits (l + 2) ≤ ReductionDsl.bits (l + 1) + 1 := bits_succ_le (l + 1)
        have hb1 : ReductionDsl.bits 1 = 1 := rfl
        simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedStartSendC,
          SM.Construction.ckaShiftedSetCache, SM.Construction.ckaShiftedSetΓPre, SM.pSet, SM.leN,
          CKA.ckaIface, CKA.ckaSamplers, CKA.ckaOps, Comp.cost, Expr.cost,
          v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, hb1, Nat.reduceAdd]; omega
      startRecv_le := fun h ctx p t γv σ tn => by
        simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedStartRecvC,
          SM.Construction.ckaStartRecvAnsE, CKA.ckaOps, Comp.cost, Expr.cost,
          v0_cost, v1_cost, v2_cost, Nat.reduceAdd]; omega
      fsSend_le := fun h ctx p t ss hdr m pair => by
        simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedFsSendC, CKA.ckaOps,
          Comp.cost, Expr.cost]; omega
      fsRecv_le := fun h ctx p t rs hdr e rec_ => by
        have hB := ReductionDsl.bits_le_succ B
        simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedFsRecvC, CKA.ckaOps,
          Comp.cost, Expr.cost]; omega
      commit_le := fun h ctx p old new => by
        have hl1 := bits_succ_le l
        have hl2 : ReductionDsl.bits (l + 2) ≤ ReductionDsl.bits (l + 1) + 1 := bits_succ_le (l + 1)
        have hb1 : ReductionDsl.bits 1 = 1 := rfl
        simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedCommitC,
          SM.Construction.ckaShiftedSetΓPre, SM.pSet, SM.isSomeE, SM.leN, SM.Engine.vpTcurNat,
          SM.Engine.vpΓ, SM.Engine.vpSetΓ, SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpRoot,
          SM.Engine.vpVS, SM.Engine.vpVR, SM.Engine.vpTcur, CKA.ckaIface, Comp.cost, Expr.cost,
          v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, hb1, Nat.reduceAdd]; omega
      reveal_le := fun h ctx p vp => by
        have hb1 : ReductionDsl.bits 1 = 1 := rfl
        simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedRevealC,
          SM.Engine.realPartyE, SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS,
          SM.Engine.vpVR, SM.Engine.vpΓ, SM.Engine.vpTcur, SM.Engine.vpTcurNat, SM.leN, SM.pGet,
          CKA.ckaIface, Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, hb1, Nat.reduceAdd]; omega }

private lemma initCKAShiftedEStateC_cost_le (l : ℕ) {Γ'} (bE : Expr OO_cka Γ' .bool) :
    (SM.Construction.initCKAShiftedEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) l bE).cost ≤ bE.cost + 800 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  simp only [SM.Construction.initCKAShiftedEStateC, SM.Engine.mkPartiesE, SM.Engine.cGsInitE,
    SM.Engine.cGsMk, SM.Engine.vpMk, SM.Engine.esMk, CKA.ckaIface, CKA.ckaSamplers, CKA.ckaOps,
    Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, hb0, Nat.reduceAdd]; omega

private abbrev dfStepBound (q qep : ℕ) : ℕ :=
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  24000 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
    200 * ReductionDsl.bits qep + 350000

private lemma df_poly_le_ratchetCostBudget (q qep : ℕ) :
    (q + 1) * dfStepBound q qep ≤ ratchetCostBudget q qep := by
  unfold ratchetCostBudget dfStepBound; dsimp only
  set M := maxForwardJumps + ReductionDsl.bits qep
  set L := q + 1
  set B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbq : 1 ≤ ReductionDsl.bits qep := ReductionDsl.one_le_bits qep
  have hL_pos : 1 ≤ L := by omega
  have hM_lb : 25001 ≤ M := by omega
  have hm_le : maxForwardJumps + 1 ≤ M := by omega
  have hB_le : B ≤ L * M := Nat.mul_le_mul_left L hm_le
  have h24000L : 24000 * L ≤ L * M := by
    calc 24000 * L = L * 24000 := Nat.mul_comm _ _
      _ ≤ L * M := Nat.mul_le_mul_left L (by omega)
  have h3b : 3 * ReductionDsl.bits qep + 60 ≤ 4 * M := by omega
  have hL3b : L * (3 * ReductionDsl.bits qep + 60) ≤ 4 * (L * M) :=
    (Nat.mul_le_mul_left L h3b).trans_eq (by ring)
  have hb_LM : ReductionDsl.bits qep ≤ L * M := by
    calc ReductionDsl.bits qep ≤ M := by omega
      _ = 1 * M := (Nat.one_mul M).symm
      _ ≤ L * M := Nat.mul_le_mul_right M hL_pos
  have h1_LM : 25001 ≤ L * M := by
    calc 25001 = 1 * 25001 := (Nat.one_mul _).symm
      _ ≤ L * M := Nat.mul_le_mul hL_pos hM_lb
  have hsum :
      24000 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
        200 * ReductionDsl.bits qep + 350000 ≤
        2 ^ 12 * (L * M) := by
    omega
  calc (q + 1) * (24000 * L + L * (3 * ReductionDsl.bits qep + 60) +
          3 * B + 200 * ReductionDsl.bits qep + 350000)
      ≤ (q + 1) * (2 ^ 12 * (L * M)) := Nat.mul_le_mul_left (q + 1) hsum
    _ = 2 ^ 12 * (q + 1) ^ 2 * M := by
      change (q + 1) * (2 ^ 12 * ((q + 1) * M)) = 2 ^ 12 * (q + 1) ^ 2 * M
      ring

private lemma add_mul_add_le_ratchetCostBudget_df {q qep a b c : ℕ}
    (ha : a ≤ dfStepBound q qep) (hb : b + c ≤ dfStepBound q qep) :
    a + q * b + q * c ≤ ratchetCostBudget q qep := by
  have hmul : q * (b + c) ≤ q * dfStepBound q qep := Nat.mul_le_mul_left q hb
  have hring : (q + 1) * dfStepBound q qep = q * dfStepBound q qep + dfStepBound q qep := by
    rw [Nat.add_mul, Nat.one_mul]
  have h1 : a + q * b + q * c ≤ (q + 1) * dfStepBound q qep := by
    have : q * b + q * c = q * (b + c) := by ring
    omega
  exact h1.trans (df_poly_le_ratchetCostBudget q qep)

private lemma implECDFShifted_step_add_le_dfStepBound {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep l : ℕ)
    (mo : SM.Construction.Mode) (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hl : l ≤ mo.tStar)
    (hhk : HooksCostBounded hk
      (let L := q + 1
       let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * ReductionDsl.bits qep + B + 2500)) :
    (SM.Engine.implECDFShifted
      (Γ' := [SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
        CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
      hk (q + 1) l 3 qep maxForwardJumps
      (SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1).cost + 13 +
        (ReductionDsl.bits mo.tStar + 81) ≤
      dfStepBound q qep := by
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have htStar_bits := bits_le_bits_qep_add (x := mo.tStar) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := mo.tL.getD 0) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hsh := implECDFShifted_cost_le_implECDF hk L l 3 qep maxForwardJumps
    (SM.Engine.modeCfgEC OO_cka mo) mo.policy
    (Γ' := [SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  have himpl := implECDF_cost_le hk
    (320 * L + 10 * ReductionDsl.bits qep + B + 2500) L qep maxForwardJumps
    mo hhk (Γ' := [SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [v0_cost, v1_cost] at himpl
  have hmul :
      L * (ReductionDsl.bits (mo.tL.getD 0) + 2 * ReductionDsl.bits mo.tStar + 40) ≤
        L * (3 * ReductionDsl.bits qep + 60) :=
    Nat.mul_le_mul_left L (by omega)
  dsimp only [L, B, dfStepBound] at hsh himpl hmul ⊢; omega

theorem redCKAAuthDFShiftedProg_add_totalCost_le
    (q qep l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) :
    (SM.Construction.redCKAAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) qep maxForwardJumps l t).totalCost q +
      q * (ReductionDsl.bits t + 81) ≤ ratchetCostBudget q qep := by
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hmo_tL : mo.tL.getD 0 ≤ mo.tStar := by dsimp [mo]; omega
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add (x := l - 1) (qep := qep) (by omega)
  have hhk := (hooksCKAShiftedC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B l t).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B]; omega)
  have hstep := implECDFShifted_step_add_le_dfStepBound _ q qep l mo ht hmo_tL hl hhk
  have hinit := initCKAShiftedEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) l (Γ' := [.unit]) (.bool false)
  have hout := authOutE_cost_le (O' := OO_cka)
    (vpT := @SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (hsT := @SM.Construction.ckaShiftedHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    L mo.policy (Γ' := [SM.Construction.ckaShiftedEsTy, .bool]) .v0
  simp only [v0_cost, Expr.cost] at hinit hout
  rw [SM.Construction.redCKAAuthDFShiftedProg_totalCost, add_right_comm _ (q * _)]
  refine add_mul_add_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, SM.Construction.Mode.policy, dfStepBound]
    at hinit hout ⊢
  simp only [Option.getD_some, Nat.reduceAdd] at hinit hout ⊢; omega

theorem redPRNGAuthDFShiftedProg_add_totalCost_le
    (q qep l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) :
    (SM.Construction.redPRNGAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps l t).totalCost q +
      q * (ReductionDsl.bits t + 81) ≤ ratchetCostBudget q qep := by
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hmo_tL : mo.tL.getD 0 ≤ mo.tStar := by dsimp [mo]; omega
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add (x := l - 1) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch (some (l - 1))) (qep := qep)
    (by dsimp [healEpoch]; omega)
  have hhk := (hooksPRNGC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B, mo, SM.Construction.Mode.tH]; omega)
  have hstep := implECDFShifted_step_add_le_dfStepBound _ q qep l mo ht hmo_tL hl hhk
  have hinit := initPRNGEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
  have hout := authOutE_cost_le (O' := OO_cka)
    (vpT := @SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (hsT := @SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    L mo.policy (Γ' := [SM.Construction.prngEsTy, .bool]) .v0
  simp only [v0_cost, Expr.cost] at hinit hout
  rw [SM.Construction.redPRNGAuthDFShiftedProg_totalCost, add_right_comm _ (q * _)]
  refine add_mul_add_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, SM.Construction.Mode.policy, dfStepBound]
    at hinit hout ⊢
  simp only [Option.getD_some, Nat.reduceAdd] at hinit hout ⊢; omega

theorem redFSAuthDFShiftedProg_add_totalCost_le
    (q qep j l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) (hj : j < q) :
    (SM.Construction.redFSAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps j l t).totalCost q +
      q * (ReductionDsl.bits t + 81) ≤ ratchetCostBudget q qep := by
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hmo_tL : mo.tL.getD 0 ≤ mo.tStar := by dsimp [mo]; omega
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add (x := l - 1) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch (some (l - 1))) (qep := qep)
    (by dsimp [healEpoch]; omega)
  have hhk := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B mo j).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B, mo, SM.Construction.Mode.tH]; omega)
  have hstep := implECDFShifted_step_add_le_dfStepBound _ q qep l mo ht hmo_tL hl hhk
  have hinit := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L mo j (Γ' := [.unit]) (.bool false)
  simp only [Expr.cost] at hinit
  rw [SM.Construction.redFSAuthDFShiftedProg_totalCost]
  refine add_mul_add_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, dfStepBound] at hinit ⊢; omega

theorem redCKAAuthDFCasePaperProg_totalCost_le
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) :
    (redCKACaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
      qep maxForwardJumps tL t).totalCost q ≤ ratchetCostBudget q qep := by
  unfold redCKAAuthDFCasePaperProg; split_ifs with h2 h3
  · exact (SM.Construction.redCKAAuthDFShiftedDir2PaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) (t - 1) t qep maxForwardJumps q).trans
      (redCKAAuthDFShiftedProg_add_totalCost_le q qep (t - 1) t ht (by omega))
  · exact (SM.Construction.redCKAAuthDFShiftedPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) (t - 2) t qep maxForwardJumps q).trans
      (redCKAAuthDFShiftedProg_totalCost_le q qep (t - 2) t ht (by omega))
  · exact (SM.Construction.redCKAAuthDFPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL t q).trans
      (redCKAAuthDFProg_totalCost_le q qep t tL ht htL)

theorem redPRNGAuthDFCasePaperProg_totalCost_le
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) :
    (redPRNGCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
      qep maxForwardJumps tL t).totalCost q ≤ ratchetCostBudget q qep := by
  unfold redPRNGAuthDFCasePaperProg; split_ifs with h2 h3
  · exact (SM.Construction.redPRNGAuthDFShiftedDir2PaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) (t - 1) t qep maxForwardJumps q).trans
      (redPRNGAuthDFShiftedProg_add_totalCost_le q qep (t - 1) t ht (by omega))
  · exact (SM.Construction.redPRNGAuthDFShiftedPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) (t - 2) t qep maxForwardJumps q).trans
      (redPRNGAuthDFShiftedProg_totalCost_le q qep (t - 2) t ht (by omega))
  · exact (SM.Construction.redPRNGAuthDFPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL t q).trans
      (redPRNGAuthDFProg_totalCost_le q qep t tL ht htL)

theorem redFSAuthDFCasePaperProg_totalCost_le
    (q qep j t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) (hj : j < q) :
    (redFSCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
      qep maxForwardJumps j tL t).totalCost q ≤ ratchetCostBudget q qep := by
  unfold redFSAuthDFCasePaperProg; split_ifs with h2 h3
  · exact (SM.Construction.redFSAuthDFShiftedDir2PaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) j (t - 1) t qep maxForwardJumps q).trans
      (redFSAuthDFShiftedProg_add_totalCost_le q qep j (t - 1) t ht (by omega) hj)
  · exact (SM.Construction.redFSAuthDFShiftedPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) j (t - 2) t qep maxForwardJumps q).trans
      (redFSAuthDFShiftedProg_totalCost_le q qep j (t - 2) t ht (by omega) hj)
  · exact (SM.Construction.redFSAuthDFPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps j tL t q).trans
      (redFSAuthDFProg_totalCost_le q qep j t tL ht htL hj)

theorem redCKAAuthDFCasePaperProg_totalQueries_le
    (L B qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redCKACaseP L B qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 + 2 * q := by
  unfold redCKAAuthDFCasePaperProg; split_ifs
  · have h : (redCKADir2P L B qep maxSkip (t - 1) t).totalQueries (fun _ => 1) (fun _ => 0) q =
        2 + q * 2 := by
      simp [CostedReduction.totalQueries, SM.Construction.redCKAAuthDFShiftedDir2PaperProg,
        SM.Construction.redCKAAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    omega
  · have h : (redCKAShiftedP L B 1 qep maxSkip (t - 2) t).totalQueries (fun _ => 1) (fun _ => 0) q =
        2 + q * 2 := by
      simp [CostedReduction.totalQueries, SM.Construction.redCKAAuthDFShiftedPaperProg,
        SM.Construction.redCKAAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    omega
  · rw [SM.Construction.redCKAAuthDFPaperProg_totalQueries]; omega

theorem redPRNGAuthDFCasePaperProg_totalQueries
    (L B qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redPRNGCaseP L B qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  unfold redPRNGAuthDFCasePaperProg; split_ifs
  · dsimp only [CostedReduction.totalQueries, SM.Construction.redPRNGAuthDFShiftedDir2PaperProg,
      SM.Construction.redPRNGAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    rw [SM.Construction.initPRNGEStateC_queries,
      SM.Construction.implECDFShiftedPaper_hooksPRNGC_queries]; omega
  · dsimp only [CostedReduction.totalQueries, SM.Construction.redPRNGAuthDFShiftedPaperProg,
      SM.Construction.redPRNGAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    rw [SM.Construction.initPRNGEStateC_queries,
      SM.Construction.implECDFShiftedPaper_hooksPRNGC_queries]; omega
  · exact SM.Construction.redPRNGAuthDFPaperProg_totalQueries _ _ _ _ _ _ _ _

theorem redFSAuthDFCasePaperProg_totalQueries
    (L B qep maxSkip j : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redFSCaseP L B qep maxSkip j tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  unfold redFSAuthDFCasePaperProg; split_ifs
  · dsimp only [CostedReduction.totalQueries, SM.Construction.redFSAuthDFShiftedDir2PaperProg,
      SM.Construction.redFSAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    rw [SM.Construction.initFSEStateC_queries,
      SM.Construction.implECDFShiftedPaper_hooksFSC_queries]; omega
  · dsimp only [CostedReduction.totalQueries, SM.Construction.redFSAuthDFShiftedPaperProg,
      SM.Construction.redFSAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    rw [SM.Construction.initFSEStateC_queries,
      SM.Construction.implECDFShiftedPaper_hooksFSC_queries]; omega
  · exact SM.Construction.redFSAuthDFPaperProg_totalQueries _ _ _ _ _ _ _ _ _

theorem redCKAAuthDFCasePaperProg_gredBounded
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hsize : (redCKACaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps tL t).size ≤ ReductionDsl.reductionSizeBudget) :
    GRedBounded (redCKACaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) :=
  _root_.CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ q (2 + 2 * q) (ratchetCostBudget q qep)
    (redCKAAuthDFCasePaperProg_totalCost_le q qep t tL ht htL)
    hsize
    (redCKAAuthDFCasePaperProg_totalQueries_le _ _ _ _ _ _ _)
    (CKA.ckaOps_sizeHonest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (CKA.ckaSamplers_sizeHonest _ _ _ _ _)

theorem redPRNGAuthDFCasePaperProg_gredBounded
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hsize : (redPRNGCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps tL t).size ≤ ReductionDsl.reductionSizeBudget) :
    GRedBounded (redPRNGCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) :=
  _root_.CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ q (2 + 2 * q) (ratchetCostBudget q qep)
    (redPRNGAuthDFCasePaperProg_totalCost_le q qep t tL ht htL)
    hsize
    (by rw [redPRNGAuthDFCasePaperProg_totalQueries]; omega)
    (PRFPRNG.prngOps_sizeHonest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (PRFPRNG.prngSamplers_sizeHonest _ _ _ _ _)

theorem redFSAuthDFCasePaperProg_gredBounded
    (q qep j t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) (hj : j < q)
    (hsize : (redFSCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps j tL t).size ≤ ReductionDsl.reductionSizeBudget) :
    GRedBounded (redFSCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps j tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) :=
  _root_.CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ q (2 * q) (ratchetCostBudget q qep)
    (redFSAuthDFCasePaperProg_totalCost_le q qep j t tL ht htL hj)
    hsize
    (by rw [redFSAuthDFCasePaperProg_totalQueries]; omega)
    (PRFPRNG.prngOps_sizeHonest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (PRFPRNG.prngSamplers_sizeHonest _ _ _ _ _)

end ShiftedPaperDeliverForgeCost
end CryptoVerification.LibsignalSession

namespace CryptoVerification.E2E

open _root_.ReductionDsl OracleSpec OracleComp ENNReal MeasureTheory
open _root_.CryptoGames _root_.CryptoGames.LibsignalSM _root_.CryptoGames.LibsignalSM.Inst
open _root_.CryptoGames.Ratchet _root_.CryptoGames.CKA _root_.CryptoGames.SM _root_.CryptoGames.SM.Construction
open _root_.CryptoGames.SM.Engine _root_.CryptoGames.SM.Thm1 _root_.CryptoGames.SM.ThmB
open _root_.CryptoGames.LibsignalSession _root_.CryptoGames.Ratchet.LibsignalInst
open _root_.CryptoGames.Ratchet.LibsignalSim _root_.CryptoGames.LibsignalSM.Proofs
open _root_.CryptoVerification.LibsignalSession _root_.CryptoVerification.LibsignalProtoCodec
open _root_.CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open _root_.CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1
open _root_.CryptoVerification.E2E _root_.CryptoVerification.E2E.Signed
open _root_.CryptoGames.SM.Construction.AuthL11
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

/-- Paper-engine `SessionCostedReductions` instance sharing the first 7 projections with
`v1SessionReds` and replacing the 4 `DeliverForge` reductions with compiled atomic paper programs. -/
@[expose] def v1SessionRedsPaper {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam :=
  { v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q with
    challSimDF :=
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.challSimDF'PaperAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
    B_cka := fun tL t =>
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redCKAAuthDFCasePaperAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t
    B_prng := fun tL t =>
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redPRNGAuthDFCasePaperAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t
    B_fs := fun stage la j tL t =>
      Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFCasePaperMultiAtomicProg
        ℓ Pt C Dh encPt encT (idsOf idA idB) lam stage la j (min (2 * q) (q + 2)) q (qep + 1) tL t
    B_cka_u := fun tL par =>
      Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redCKAAuthDFPaperBucketAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL par
    B_prng_u := fun tL par t =>
      Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFPaperBucketHybridAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL par t
    B_fs_u := fun stage la j tL par t =>
      if healEpoch tL ≤ t ∧ t ≤ min (qep + 1) (q + 11) + 3 ∧ j < q then
        Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFPaperMultiBucketAtomicProg
          ℓ Pt C Dh encPt encT (idsOf idA idB) lam stage la (q * (t - healEpoch tL) + j) (min (2 * q) (q + 2)) q (qep + 1) tL par
      else
        Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsStage2AtomicProg
          Dh encPt C ℓ encT (idsOf idA idB) lam }

private lemma targetsL_getD_le {Δ t : ℕ} {tL : Option ℕ} (htL : tL ∈ admissibleLastLeakGuesses Δ t) :
    tL.getD 0 ≤ t := by
  simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at htL
  rcases htL with rfl | ⟨l, hl, rfl⟩
  · simp
  · simp; omega

/-- `v1SessionRedsPaper` satisfies `sessionCostedReductionsBounded` when `qep ≤ q + 10`. -/
theorem v1SessionRedsPaper_bounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ q + 10) :
    sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
      (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  have hb := v1SessionReds_bounded ℓ C K idA idB Dh encPt encT decT lam qep q hqep
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.1,
    Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.challSimDF'PaperAtomicProg_gRedBounded
      Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q,
    fun t ht => by
      rw [Finset.mem_Ico] at ht
      exact ⟨
        Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redCKAAuthDFCasePaperAtomicProg_gRedBounded
          Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t (some (t - 2)) ht.2 (by simp),
        Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redPRNGAuthDFCasePaperAtomicProg_gRedBounded
          Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t (some (t - 2)) ht.2 (by simp),
        fun j _hj stage la =>
          Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds.redFSAuthDFCasePaperMultiAtomicProg_gRedBounded
            ℓ Pt C Dh encPt encT (idsOf idA idB) lam stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 2)) t⟩,
    fun t ht => by
      rw [Finset.mem_Ico] at ht
      exact ⟨
        Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redCKAAuthDFCasePaperAtomicProg_gRedBounded
          Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t (some (t - 3)) ht.2 (by simp),
        Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redPRNGAuthDFCasePaperAtomicProg_gRedBounded
          Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t (some (t - 3)) ht.2 (by simp),
        fun j _hj stage la =>
          Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds.redFSAuthDFCasePaperMultiAtomicProg_gRedBounded
            ℓ Pt C Dh encPt encT (idsOf idA idB) lam stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 3)) t⟩,
    fun tL htL par => by
      have htL_le : tL.getD 0 ≤ (qep + 1) + 2 := by
        simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at htL
        rcases htL with rfl | ⟨l, hl, rfl⟩
        · simp
        · simp; omega
      exact ⟨
        Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redCKAAuthDFPaperBucketAtomicProg_gRedBounded
          Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL par htL_le (by omega),
        fun t ht => by
          rw [Finset.mem_Ico] at ht
          exact ⟨
            Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFPaperBucketHybridAtomicProg_gRedBounded
              Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL par t ht.2 htL_le (by omega),
            fun j _hj stage la => by
              dsimp only [v1SessionRedsPaper]
              split_ifs
              · exact Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds.redFSAuthDFPaperMultiBucketAtomicProg_gRedBounded
                  ℓ Pt C Dh encPt encT (idsOf idA idB) lam stage la (q * (t - healEpoch tL) + j) (min (2 * q) (q + 2)) q (qep + 1) tL par
              · exact Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsStage2AtomicProg_gRedBounded
                  Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q (2 * q)⟩⟩,
    fun t _ht A hA =>
      ⟨Computational.Proofs.HeadlineV1.DeliverForgePaperUnshiftedPotOK.redPRNGAuthDFCasePaperAtomicProg_makesAtMostQueries
        ℓ C Dh encPt encT (idsOf idA idB) lam (qep + 1) q (some (t - 2)) t A hA,
       fun j _hj stage la =>
         Computational.Proofs.HeadlineV1.DeliverForgePaperMultiBucketPotOK.redFSAuthDFCasePaperMultiAtomicProg_makesAtMostQueries_min
           ℓ C Dh encPt encT (idsOf idA idB) lam stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 2)) t A hA⟩,
    fun t _ht A hA =>
      ⟨Computational.Proofs.HeadlineV1.DeliverForgePaperUnshiftedPotOK.redPRNGAuthDFCasePaperAtomicProg_makesAtMostQueries
        ℓ C Dh encPt encT (idsOf idA idB) lam (qep + 1) q (some (t - 3)) t A hA,
       fun j _hj stage la =>
         Computational.Proofs.HeadlineV1.DeliverForgePaperMultiBucketPotOK.redFSAuthDFCasePaperMultiAtomicProg_makesAtMostQueries_min
           ℓ C Dh encPt encT (idsOf idA idB) lam stage la j (min (2 * q) (q + 2)) q (qep + 1) (some (t - 3)) t A hA⟩,
    fun tL _htL par t _ht A hA =>
      ⟨Computational.Proofs.HeadlineV1.DeliverForgePaperMultiBucketPotOK.redPRNGAuthDFPaperBucketHybridAtomicProg_makesAtMostQueries
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL par t A hA,
       fun j _hj stage la => by
         dsimp only [v1SessionRedsPaper]
         split_ifs
         · exact Computational.Proofs.HeadlineV1.DeliverForgePaperMultiBucketPotOK.redFSAuthDFPaperMultiBucketAtomicProg_makesAtMostQueries_min
             ℓ C Dh encPt encT (idsOf idA idB) lam stage la (q * (t - healEpoch tL) + j) (min (2 * q) (q + 2)) q (qep + 1) tL par A hA
         · exact Computational.Proofs.HeadlineV1.DeliverForgePaperMultiBucketPotOK.dummyFsStage2AtomicProg_makesAtMostQueries
             Dh encPt C ℓ encT (idsOf idA idB) lam q (min (2 * q) (q + 2)) A hA⟩⟩

section PaperEvalBridges

open _root_.CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 _root_.CryptoVerification.E2E.Signed
open _root_.CryptoGames.SM.Construction.AuthL11
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

@[simp] theorem v1SessionRedsPaper_spk (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).spk =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).spk := rfl

@[simp] theorem v1SessionRedsPaper_fig8 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 =
      fig8RedsInst Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam (qep + 1) q := rfl

@[simp] theorem v1SessionRedsPaper_fs (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).fs =
      fsCostedRedsInst C protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)) := rfl

@[simp] theorem v1SessionRedsPaper_simFig8 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 := rfl

@[simp] theorem v1SessionRedsPaper_simDeliverForge (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).simDeliverForge =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simDeliverForge := rfl

@[simp] theorem v1SessionRedsPaper_epoch0Red (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red := rfl

@[simp] theorem v1SessionRedsPaper_uniformStartRed (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed := rfl

theorem v1SessionRedsPaper_challSimDF_eval (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (B_adv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hqB : DeliverForge.MakesAtMostQueriesDF B_adv q) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).challSimDF.eval
      (fun _ => B_adv) () =
    DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) B_adv :=
  Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper.compileSmDFAtomic_challSimDF'PaperProg_eval
    Dh encPt C ℓ hℓ encT (idsOf idA idB) lam (qep + 1) q B_adv hqB

theorem v1SessionRedsPaper_B_cka_advantage_df (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (Z : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tStar : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q)
    (hsh_df : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv) :
    let P := paramsV1 Z K idA idB
    let challAdvDF := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    CKA.advantage (dhScheme Dh) 1 tStar
      (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_cka
        tL t).eval (fun _ => challAdvDF) ()) =
    CKA.advantage (dhScheme Dh) 1 tStar
      (Proofs.Refinement.redCKAHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
        tL t dfAdv) :=
  Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper.compileCkaDFAtomic_casePaper_advantage
    Dh encPt Z ℓ hℓ encT (idsOf idA idB) lam 1 tStar (qep + 1) q tL t
    (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
    (challSimDF'Paper_queries (2 + 1) (qep + 1) dfAdv hq_df)
    (challSimDF'Paper_sendOk (2 + 1) (qep + 1) _ dfAdv hsh_df)

theorem v1SessionRedsPaper_B_prng_advantage_df (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (Z : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q)
    (hsh_df : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv) :
    let P := paramsV1 Z K idA idB
    let challAdvDF := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    PRFPRNG.advantage (rootPRNG Z.F encPt)
      (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT
        lam qep q).B_prng tL t).eval (fun _ => challAdvDF) ()) =
    PRFPRNG.advantage (rootPRNG Z.F encPt)
      (Proofs.Refinement.redPRNGHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
        tL t dfAdv) :=
  Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper.compilePrngDFAtomic_casePaper_advantage
    Dh encPt Z ℓ hℓ encT (idsOf idA idB) lam (qep + 1) q tL t
    (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
    (challSimDF'Paper_queries (2 + 1) (qep + 1) dfAdv hq_df)
    (challSimDF'Paper_sendOk (2 + 1) (qep + 1) _ dfAdv hsh_df)

section SimDeliverForgeGuarded

set_option linter.unusedSectionVars false

open _root_.CryptoGames.GuardedSafe
open _root_.CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (SimShortInv simShortInv_initSim smRespShort smRecvLong SimSafeS guardedSafeS_simSend
   inTransit_mem_and_ct mem_accept_trans)

private theorem guardedSafePost_fig8ToDFImpl_step {ℓ : ℕ}
    (t : (QueryBounds.FSpec Pt ℓ).Domain)
    (ht : ¬ smRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt) t)
    (sent : List (LibsignalSim.Fig8C Pt)) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun r => smRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt) t r.1)
      ((Proofs.Refinement.fig8ToDFImpl Pt ℓ t).run sent) := by
  have hQt : ¬ smDFRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt)
      (toDFDom t) := by
    rcases t with _ | _
    · exact not_false
    · exact ht
  have hq := GuardedSafePost.query
    (RespOk := smDFRespShort (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    hQt
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, c⟩) | ⟨R, c⟩) | R))
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ) (toDFDom (.inl n)) >>=
      fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial
  · unfold Proofs.Refinement.fig8ToDFImpl DeliverForge.transmitQueryDF
    rw [StateT.run_bind]
    have hlift : GuardedSafePost
        (smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (fun p : Option (LibsignalSim.Fig8C Pt) × List (LibsignalSim.Fig8C Pt) =>
          smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt)
            (.inr (.inl (.inl (.inl (.inl (R, m, r)))))) p.1)
        ((StateT.lift (query (spec := DFSpec Pt ℓ)
            (toDFDom (.inr (.inl (.inl (.inl (.inl (R, m, r)))))))) :
          Proofs.Refinement.DeliverForgeM Pt ℓ _).run sent) := by
      dsimp only [StateT.lift, StateT.run]
      exact hq.bind fun _ ha => GuardedSafePost.pure ha
    refine hlift.bind fun ⟨res, sent'⟩ hres => ?_
    cases res <;>
      (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind];
       exact GuardedSafePost.pure hres)
  · unfold Proofs.Refinement.fig8ToDFImpl DeliverForge.challQueryDF
    rw [StateT.run_bind]
    have hlift : GuardedSafePost
        (smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (fun p : Option (LibsignalSim.Fig8C Pt) × List (LibsignalSim.Fig8C Pt) =>
          smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt)
            (.inr (.inl (.inl (.inl (.inr (R, m₀, m₁, r)))))) p.1)
        ((StateT.lift (query (spec := DFSpec Pt ℓ)
            (toDFDom (.inr (.inl (.inl (.inl (.inr (R, m₀, m₁, r)))))))) :
          Proofs.Refinement.DeliverForgeM Pt ℓ _).run sent) := by
      dsimp only [StateT.lift, StateT.run]
      exact hq.bind fun _ ha => GuardedSafePost.pure ha
    refine hlift.bind fun ⟨res, sent'⟩ hres => ?_
    cases res <;>
      (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind];
       exact GuardedSafePost.pure hres)
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inl (.inl (.inr (R, c)))))) >>= fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inl (.inr (R, c))))) >>= fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inr R))) >>= fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial

private theorem guardedSafePost_deliverForgeHook_lift {ℓ : ℕ} {α : Type} {P : α → Prop}
    {x : LibsignalSim.Fig8Comp Pt ℓ α}
    (hx : GuardedSafePost
      (smRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      P x)
    (sent : List (LibsignalSim.Fig8C Pt)) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun r => P r.1)
      (((Proofs.Refinement.deliverForgeHook Pt ℓ).lift x).run sent) := by
  dsimp only [Proofs.Refinement.deliverForgeHook]
  induction hx generalizing sent with
  | pure h =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact GuardedSafePost.pure (P := fun r : α × List (LibsignalSim.Fig8C Pt) => P r.1) h
  | @query_bind t mx hQt _ ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    have hlift : GuardedSafePost
        (smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (fun r : (QueryBounds.FSpec Pt ℓ).Range t × List (LibsignalSim.Fig8C Pt) =>
          smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt) t r.1)
        ((liftM (Proofs.Refinement.fig8ToDFImpl Pt ℓ t) :
          Proofs.Refinement.DeliverForgeM Pt ℓ _).run sent) := by
      simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using
        guardedSafePost_fig8ToDFImpl_step t hQt sent
    exact hlift.bind fun pu hpu => ih pu.1 hpu pu.2

private abbrev DFSafePost (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (oa : DeliverForge.AdversaryCompDF (LibsignalSim.Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt)
      (α × (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ × List (LibsignalSim.Fig8C Pt)))) :
    Prop :=
  GuardedSafePost
    (smDFRespShort (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (fun r => True ∧ SimShortInv r.2.1.base) oa

private def dfSafeC (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (sent : List (LibsignalSim.Fig8C Pt)),
    SimShortInv sC.base →
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun p => SimShortInv p.1.2.base) ((x.run sC).run sent)

private theorem dfSafePost_runDFM {PQ : Type} {ℓ : ℕ} {α : Type}
    {x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    (hx : dfSafeC PQ Pt ℓ x)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base) :
    DFSafePost PQ Pt ℓ (LibsignalSim.runDFM x sC ex) := by
  unfold LibsignalSim.runDFM
  exact (hx sC ex hs).bind fun _ hp => GuardedSafePost.pure ⟨trivial, hp⟩

private theorem dfSafeC_pure {PQ : Type} {ℓ : ℕ} {α : Type} (a : α) :
    dfSafeC PQ Pt ℓ (pure a) := fun sC sent hs => by
  simp only [StateT.run_pure]
  exact GuardedSafePost.pure
    (P := fun p : (α × LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
        List (LibsignalSim.Fig8C Pt) => SimShortInv p.1.2.base)
    hs

private theorem dfSafeC_bind {PQ : Type} {ℓ : ℕ} {α β : Type}
    {x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    {f : α → StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) β}
    (hx : dfSafeC PQ Pt ℓ x) (hf : ∀ a, dfSafeC PQ Pt ℓ (f a)) :
    dfSafeC PQ Pt ℓ (x >>= f) := fun sC sent hs => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (hx sC sent hs).bind fun p hp => hf p.1.1 p.1.2 p.2 hp

private theorem dfSafeC_get_bind {PQ : Type} {ℓ : ℕ} {α : Type}
    {f : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ →
      StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
        (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    (hf : ∀ sC, SimShortInv sC.base → dfSafeC PQ Pt ℓ (f sC)) :
    dfSafeC PQ Pt ℓ (get >>= f) := fun sC sent hs => by
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  exact hf sC hs sC sent hs

private theorem dfSafeC_set {PQ : Type} {ℓ : ℕ}
    (sC' : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (h : SimShortInv sC'.base) :
    dfSafeC PQ Pt ℓ (set sC') := fun _ _ _ => by
  simp only [StateT.run_set, StateT.run_pure]
  exact GuardedSafePost.pure
    (P := fun p : (PUnit × LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
        List (LibsignalSim.Fig8C Pt) => SimShortInv p.1.2.base)
    h

private theorem dfSafeC_guardC {PQ : Type} {ℓ : ℕ} {α : Type}
    {x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) (Option α)}
    (hx : dfSafeC PQ Pt ℓ x) :
    dfSafeC PQ Pt ℓ (LibsignalSimC.guardC x) := by
  unfold LibsignalSimC.guardC
  refine dfSafeC_get_bind fun _ _ => ?_
  split
  · exact dfSafeC_pure none
  · exact hx

private theorem dfSafeC_zoomB {PQ : Type} {ℓ : ℕ} {α : Type}
    {x : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α}
    (hx : SimSafeS PQ Pt ℓ x) :
    dfSafeC PQ Pt ℓ
      (LibsignalSimC.runOnBaseState (Proofs.Refinement.deliverForgeHook Pt ℓ) x) :=
  fun sC sent hs => by
    show GuardedSafePost _ _ _
      (((Proofs.Refinement.deliverForgeHook Pt ℓ).lift (x.run sC.base) >>=
        fun p => pure (p.1, { sC with base := p.2 })).run sent)
    rw [StateT.run_bind]
    exact (guardedSafePost_deliverForgeHook_lift (hx sC.base hs) sent).bind fun p hp => by
      simp only [StateT.run_pure]
      exact GuardedSafePost.pure
        (P := fun r : (α × LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
            List (LibsignalSim.Fig8C Pt) => SimShortInv r.1.2.base)
        hp

private theorem dfSafeC_simSendC {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    dfSafeC PQ Pt ℓ
      (LibsignalSimC.simSendC P qep fig (Proofs.Refinement.deliverForgeHook Pt ℓ) Q m₀ chal r) := by
  unfold LibsignalSimC.simSendC
  refine dfSafeC_bind (dfSafeC_zoomB (guardedSafeS_simSend P qep Q m₀ chal r)) fun res => ?_
  cases res with
  | none => exact dfSafeC_pure none
  | some w =>
    refine dfSafeC_get_bind fun _ hsC => ?_
    exact dfSafeC_bind (dfSafeC_set _ hsC) fun _ => dfSafeC_pure (some w)

private theorem dfSafeC_simCorrC {PQ PQC : Type} (P : Params PQ PQC) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Q : Party) :
    dfSafeC PQ Pt ℓ
      (LibsignalSimC.simCorrC P encT (Proofs.Refinement.deliverForgeHook Pt ℓ) Dh Q) := by
  unfold LibsignalSimC.simCorrC
  refine dfSafeC_get_bind fun sC hsC => ?_
  dsimp only
  split
  · exact dfSafeC_pure none
  · have hcorr : dfSafeC PQ Pt ℓ
        (LibsignalSimC.liftC (Proofs.Refinement.deliverForgeHook Pt ℓ)
          (SM.corrQuery (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
            (C := LibsignalSim.Fig8C Pt) Q)) := fun sC₁ sent hs₁ => by
      show GuardedSafePost _ _ _
        (((Proofs.Refinement.deliverForgeHook Pt ℓ).lift (SM.corrQuery Q) >>=
          fun a => pure (a, sC₁)).run sent)
      rw [StateT.run_bind]
      have hq : GuardedSafePost
          (smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
          (smRecvLong (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
          (fun _ => True) (SM.corrQuery Q) := by
        unfold SM.corrQuery
        exact GuardedSafePost.query
          (spec := QueryBounds.FSpec Pt ℓ)
          (RespOk := smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
          (Q := smRecvLong (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
          (t := Sum.inr (Sum.inr Q))
          not_false
      exact (guardedSafePost_deliverForgeHook_lift hq sent).bind fun _ _ => by
        simp only [StateT.run_pure]
        exact GuardedSafePost.pure
          (P := fun r : (Option (LibsignalSim.Fig8St Pt) ×
                LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
              List (LibsignalSim.Fig8C Pt) => SimShortInv r.1.2.base)
          hs₁
    refine dfSafeC_bind hcorr fun res => ?_
    cases res with
    | none => exact dfSafeC_pure none
    | some _ => exact dfSafeC_bind (dfSafeC_set _ ⟨hsC.1, hsC.2⟩) fun _ => dfSafeC_pure _

private theorem simShortInv_onAcceptPure {PQ : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (s : LibsignalSim.SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (LibsignalSim.onAcceptPure qep Q w isDel t i m ci? T pq' s).2 := by
  unfold LibsignalSim.onAcceptPure
  dsimp only
  split_ifs
  · rcases s.mir.inTransit Q.other w with _ | r
    · exact hs
    · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact hs
  · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact ⟨hs.1, hs.2⟩

private theorem simShortInv_onAnswerPure {PQ : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : LibsignalSim.SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (LibsignalSim.onAnswerPure qep Q w isDel ci? T pq' res s).2 := by
  unfold LibsignalSim.onAnswerPure
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact simShortInv_onAcceptPure qep Q w isDel t i _ ci? T pq' s hs

private theorem guardedSafePost_deliverQueryDF {ℓ : ℕ} (Q : Party)
    (c : LibsignalSim.Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun _ => True)
      (DeliverForge.deliverQueryDF
        (St := LibsignalSim.Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := LibsignalSim.Fig8C Pt) Q c) := by
  unfold DeliverForge.deliverQueryDF
  exact GuardedSafePost.query
    (spec := DFSpec Pt ℓ)
    (RespOk := smDFRespShort (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (Q := smDFRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (t := Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Q, c))))))
    (fun h => h hc)

private theorem guardedSafePost_injectQueryDF {ℓ : ℕ} (Q : Party)
    (c : LibsignalSim.Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun _ => True)
      (DeliverForge.injectQueryDF
        (St := LibsignalSim.Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := LibsignalSim.Fig8C Pt) Q c) := by
  unfold DeliverForge.injectQueryDF
  exact GuardedSafePost.query
    (spec := DFSpec Pt ℓ)
    (RespOk := smDFRespShort (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (Q := smDFRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (t := Sum.inr (Sum.inl (Sum.inl (Sum.inr (Q, c)))))
    (fun h => h hc)

private theorem guardedSafePost_deliverForgeSemHook_onProbe {PQC : Type} [SampleableType PQC]
    {ℓ : ℕ} (Q : Party) (c' : LibsignalSim.Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32)
    (ex : List (LibsignalSim.Fig8C Pt)) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun _ => True)
      ((LibsignalSim.deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex) := by
  unfold LibsignalSim.deliverForgeSemHook
  dsimp only
  rcases ex.find? (fun c => Proofs.Refinement.sameWireFig8 c c') with _ | c
  · exact GuardedSafePost.pure trivial
  · have hq : GuardedSafePost
        (smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (fun _ => True)
        (DeliverForge.deliverForgeQuery
          (St := LibsignalSim.Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
          (Coins := BitVec 256) (C := LibsignalSim.Fig8C Pt) Q c c') := by
      unfold DeliverForge.deliverForgeQuery
      exact GuardedSafePost.query
        (spec := DFSpec Pt ℓ)
        (RespOk := smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (Q := smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (t := Sum.inr (Sum.inr (Q, c, c')))
        (fun h => h hc')
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial

private theorem dfSafePost_semFwdAnswerHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : LibsignalSim.Fig8C Pt)
    (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semFwdAnswerHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w isDel ci? Tpk pq' c') := by
  unfold LibsignalSim.semFwdAnswerHook LibsignalSim.deliverForgeSemHook
  dsimp only
  refine GuardedSafePost.bind (P := fun _ => True) ?_ fun ⟨res, ex₁⟩ _ =>
    GuardedSafePost.pure ⟨trivial, simShortInv_onAnswerPure qep Q w isDel ci? Tpk pq' res sC.base hs⟩
  split_ifs
  · exact (guardedSafePost_deliverQueryDF Q c' hc').bind fun _ _ => GuardedSafePost.pure trivial
  · exact (guardedSafePost_injectQueryDF Q c' hc').bind fun _ _ => GuardedSafePost.pure trivial

private theorem dfSafePost_semResyncHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : LibsignalSim.Fig8C Pt)
    (hc : c.2.2.1.1.length < 2 ^ 32)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semResyncHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w ci? Tpk pq' c r) := by
  unfold LibsignalSim.semResyncHook LibsignalSim.deliverForgeSemHook
  rcases r with _ | ⟨t, i, _, m'⟩
  · exact GuardedSafePost.pure ⟨trivial, hs⟩
  · dsimp only
    refine GuardedSafePost.bind (P := fun _ => True)
      ((guardedSafePost_deliverQueryDF Q c hc).bind fun _ _ => GuardedSafePost.pure trivial)
      fun ⟨res, ex₁⟩ _ => ?_
    rcases res with _ | (_ | _)
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure
        ⟨trivial, simShortInv_onAcceptPure qep Q w true t i m' ci? Tpk pq' sC.base hs⟩

private theorem dfSafePost_semFwdEvictHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : LibsignalSim.Fig8C Pt)
    (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semFwdEvictHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w isDel Tpk pq' c') := by
  unfold LibsignalSim.semFwdEvictHook
  split_ifs
  · exact (guardedSafePost_deliverForgeSemHook_onProbe (PQC := PQC) Q c' hc' ex).bind
      fun _ _ => GuardedSafePost.pure ⟨trivial, hs⟩
  · exact dfSafePost_semFwdAnswerHook P Dh encPt encT lam qep sC ex hs Q w isDel none Tpk pq' c' hc'

private theorem dfSafePost_semFwdHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep B : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (LibsignalSim.Fig8C Pt))
    (hhon : ∀ c, honestC = some c → c.2.2.1.1.length < 2 ^ 32)
    (c' : LibsignalSim.Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semFwdHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep B sC ex Q w isDel ci? Tpk pq' honestC c') := by
  unfold LibsignalSim.semFwdHook
  rcases honestC with _ | c
  · exact dfSafePost_semFwdAnswerHook P Dh encPt encT lam qep sC ex hs Q w isDel ci? Tpk pq' c' hc'
  · dsimp only
    split_ifs
    · rcases LibsignalSim.evalCKClamp P Dh encPt encT lam B sC Q w c c' with _ | r
      · exact (guardedSafePost_deliverForgeSemHook_onProbe (PQC := PQC) Q c' hc' ex).bind
          fun _ _ => GuardedSafePost.pure ⟨trivial, hs⟩
      · exact dfSafePost_semResyncHook P Dh encPt encT lam qep sC ex hs Q w ci? Tpk pq' c
          (hhon c rfl) r
    · exact dfSafePost_semFwdAnswerHook P Dh encPt encT lam qep sC ex hs Q w isDel ci? Tpk pq' c' hc'

private theorem simParseRecvC_ser_eq {PQ PQC : Type} (P : Params PQ PQC)
    (decT : PublicKey → Option Pt) (B : ℕ) (qB : Bool) (pq : PQ) (w : Bytes)
    {pq' : PQ} {i : ℕ} {pk : PublicKey} {T? : Option Pt} {lct : ℕ × LibsignalCiphertextWithSalt32}
    (hp : LibsignalSim.simParseRecvC P decT B qB pq w = some (pq', (i, (pk, (T?, lct))))) :
    lct.2.1.1 = w.take (w.length - 8) := by
  unfold LibsignalSim.simParseRecvC at hp
  split_ifs at hp
  dsimp only [] at hp
  rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
  · rw [hparse] at hp; cases hp
  · rw [hparse] at hp; dsimp only [] at hp
    split_ifs at hp
    rcases hspqr : P.spqr.recv pq h.pqRatchet with _ | ⟨pq1, salt⟩
    · rw [hspqr] at hp; cases hp
    · rw [hspqr] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      exact congrArg (fun x : ℕ × LibsignalCiphertextWithSalt32 => x.2.1.1) hp.2.2.2.2.symm

private theorem dfSafePost_semRecvHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semRecvHook P Dh encPt encT decT lam LibsignalSim.deliverForgeSemHook
        qep B sC ex Q w isDel) := by
  unfold LibsignalSim.semRecvHook
  dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hp : LibsignalSim.simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w
      with _ | ⟨pq', i, pk, T?, lct⟩
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · have hwlen : w.length < 2 ^ 32 := by
        cases isDel with
        | true =>
          rcases htr : sC.base.mir.inTransit Q.other w with _ | rec'
          · simp [htr] at href
          · obtain ⟨hmem, rfl⟩ := inTransit_mem_and_ct htr
            exact hs.1 rec' hmem
        | false =>
          by_cases hw9 : w.length < 9
          · omega
          · have hadm : ratchetKeyAdmissible P.codec decT encT w = true := by
              revert href
              cases ratchetKeyAdmissible P.codec decT encT w <;> simp
            unfold ratchetKeyAdmissible at hadm
            simp only [hw9, ↓reduceIte] at hadm
            have hp0 := hp
            unfold LibsignalSim.simParseRecvC at hp0
            split_ifs at hp0
            dsimp only [] at hp0
            rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
            · rw [hparse] at hp0; cases hp0
            · simp only [hparse, Bool.and_eq_true, decide_eq_true_eq] at hadm
              exact hadm.1
      have hlct : lct.2.1.1.length < 2 ^ 32 := by
        rw [simParseRecvC_ser_eq P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w hp,
          List.length_take]
        omega
      have hhon : ∀ c : LibsignalSim.Fig8C Pt,
          (sC.base.honest.find? fun (wc : Bytes × LibsignalSim.Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
              (fun (wc : Bytes × LibsignalSim.Fig8C Pt) => wc.2) = some c →
          c.2.2.1.1.length < 2 ^ 32 := by
        intro c hc_eq
        rcases Option.mem_map.mp hc_eq with ⟨wc, hfind, rfl⟩
        exact hs.2 wc (List.mem_of_find?_eq_some hfind)
      have hmkC : ∀ (t : ℕ) (To : Option Pt),
          (match (sC.base.honest.find? fun (wc : Bytes × LibsignalSim.Fig8C Pt) =>
               wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
                 (fun (wc : Bytes × LibsignalSim.Fig8C Pt) => wc.2) with
           | some (c : LibsignalSim.Fig8C Pt) =>
             if c.2.2.2 = lct.2.2 then c else ((t, To), lct)
           | none => ((t, To), lct)).2.2.1.1.length < 2 ^ 32 := by
        intro t To
        rcases hfind : sC.base.honest.find? (fun (wc : Bytes × LibsignalSim.Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with _ | wc
        · exact hlct
        · simp only [Option.map]
          split
          · exact hs.2 wc (List.mem_of_find?_eq_some hfind)
          · exact hlct
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · have hsAmb : SimShortInv
            ({ sC with base :=
                if inReceiveOnlyEpoch sC.base.mir Q ||
                    (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
                  { sC.base with amb := sC.base.amb + 1 }
                else sC.base }).base := by
          dsimp only
          split_ifs <;> exact ⟨hs.1, hs.2⟩
        cases h1 :
          (((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
            some true &&
          ((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) ==
            some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T
              · exact GuardedSafePost.pure ⟨trivial, hsAmb⟩
              · cases h4 :
                  (((Option.map (fun x => x.2)
                      (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                        sC.base.honest)).map fun c =>
                    decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact dfSafePost_semFwdHook P Dh encPt encT lam qep B _ ex hsAmb
                    Q w isDel none pk pq' _ hhon _ (hmkC _ _)
                · simp only [↓reduceIte]
                  exact dfSafePost_semFwdEvictHook P Dh encPt encT lam qep _ ex hsAmb
                    Q w isDel pk pq' _ hlct
            · simp only [↓reduceIte]
              exact GuardedSafePost.pure ⟨trivial, hsAmb⟩
          · simp only [↓reduceIte]
            exact GuardedSafePost.pure ⟨trivial, hs⟩
        · simp only [↓reduceIte]
          exact GuardedSafePost.pure ⟨trivial, hs⟩
      · cases h5 :
          ((sC.base.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects
            i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact dfSafePost_semFwdHook P Dh encPt encT lam qep B sC ex hs
            Q w isDel (some ci) pk pq' _ hhon _ (hmkC _ _)
        · simp only [↓reduceIte]
          exact GuardedSafePost.pure ⟨trivial, hs⟩
  · simp only [↓reduceIte]
    exact GuardedSafePost.pure ⟨trivial, hs⟩

theorem simDeliverForgeClamp_guardedSMDFShort {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] (P : Params PQ PQC) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (CBC.Plain ℓ) PQC Bytes) :
    GuardedSMDFShort (LibsignalSim.simDeliverForgeClamp P Dh encPt encT decT lam qep B A) := by
  unfold GuardedSMDFShort LibsignalSim.simDeliverForgeClamp
  refine (GuardedSafePost.liftComp_unif hQu_smDFRecvLong ($ᵗ BitVec 256)).bind fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  have hsim : GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun r => SimShortInv r.2.1.base)
      ((simulateQ (LibsignalSim.simDeliverForgeOracle P Dh encPt encT decT lam qep B) A).run
        (LibsignalSimC.initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), [])) := by
    refine GuardedSafePost.simulateQ_run
      (I := fun p : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ ×
          List (LibsignalSim.Fig8C Pt) => SimShortInv p.1.base)
      (GuardedSafePost.true_of_false A) ?_ (simShortInv_initSim _ _)
    rintro (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) _ ⟨sC, ex⟩ hs
    · show DFSafePost PQ Pt ℓ
        (query (spec := DFSpec Pt ℓ) (.inl n) >>= fun a => pure (a, (sC, ex)))
      exact (GuardedSafePost.query (hQu_smDFRecvLong n)).bind fun _ _ =>
        GuardedSafePost.pure ⟨trivial, hs⟩
    · change DFSafePost PQ Pt ℓ
        (LibsignalSim.semSendHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
          qep sC ex Q m none r)
      rw [LibsignalSim.semSendHook_deliverForge_eq]
      exact dfSafePost_runDFM (dfSafeC_guardC (dfSafeC_simSendC P qep _ Q m none r)) sC ex hs
    · change DFSafePost PQ Pt ℓ
        (LibsignalSim.semSendHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
          qep sC ex Q m₀ (some m₁) r)
      rw [LibsignalSim.semSendHook_deliverForge_eq]
      exact dfSafePost_runDFM (dfSafeC_guardC (dfSafeC_simSendC P qep _ Q m₀ (some m₁) r)) sC ex hs
    · change DFSafePost PQ Pt ℓ
        (LibsignalSim.semRecvHook P Dh encPt encT decT lam LibsignalSim.deliverForgeSemHook
          qep B sC ex Q w true >>= fun ⟨rr, sC₁, ex₁⟩ =>
            (LibsignalSim.deliverForgeSemHook (PQC := PQC)).onDeliverPost Q none rr ex₁ >>=
              fun ex₂ => pure (rr, (sC₁, ex₂)))
      exact (dfSafePost_semRecvHook P Dh encPt encT decT lam qep B sC ex hs Q w true).bind
        fun ⟨rr, sC₁, ex₁⟩ ⟨_, hs₁⟩ => by
          dsimp only [LibsignalSim.deliverForgeSemHook]
          rw [pure_bind]
          exact GuardedSafePost.pure ⟨trivial, hs₁⟩
    · exact dfSafePost_semRecvHook P Dh encPt encT decT lam qep B sC ex hs Q w false
    · change DFSafePost PQ Pt ℓ
        (LibsignalSim.semCorrHook P Dh encT LibsignalSim.deliverForgeSemHook sC ex Q)
      rw [LibsignalSim.semCorrHook_deliverForge_eq]
      exact dfSafePost_runDFM (dfSafeC_guardC (dfSafeC_simCorrC P Dh encT Q)) sC ex hs
  exact hsim.map (R := fun _ => True) Prod.fst fun _ _ => trivial

end SimDeliverForgeGuarded

/-- Single-win 3-family Stage-2 `DeliverForge` advantage sum (`B1` + `B2` + `(tL, par)` buckets),
which replaces the pre-`[B7]` per-cell `forgeGuessedAdvantageCellPaper` cut point between
`firstNESimImpl'` / `firstNEHalted'` and `HiddenSaltLazyFirstNEReds`. -/
@[expose] noncomputable def forgeStage2CellBucketSumPaper
    {Key St Msg Coins : Type} {T E : Type}
    [DecidableEq Msg] [DecidableEq T] [DecidableEq E]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) (qep : ℕ)
    (sameHdr : (Header T × E) → (Header T × E) → Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins (Header T × E)) : ℝ≥0∞ :=
  (∑ t ∈ Finset.Ico 2 ((qep + 1) + 2),
    DeliverForge.forgeGuessedAdvantageShiftedDir2Paper sm (qep + 1) sameHdr (t - 1) t B) +
  (∑ t ∈ Finset.Ico 3 ((qep + 1) + 2),
    DeliverForge.forgeGuessedAdvantageShiftedPaper sm (2 + 1) (qep + 1) sameHdr (t - 2) t B) +
  (∑ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∑ par ∈ ({false, true} : Finset Bool),
    DeliverForge.forgeBucketAdvantagePaper sm 1 (qep + 1) sameHdr tL par B)

/-- Stage-2 reduction bridge from `forgeStage2CellBucketSumPaper` to any `SessionCostedReductions`
bundle `R` (instantiating `DeliverForge.forgeBucketAdvantagePaper_le_cka_add_branch_true` on each
`(tL, par)` bucket). -/
theorem forgeStage2CellBucketSumPaper_le_of_stage2_bounds
    {ℓ : ℕ}
    (Z : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ)
    (R : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam)
    (challAdvDF : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hB1 : ∀ t ∈ Finset.Ico 2 ((qep + 1) + 2),
      let tL : Option ℕ := some (t - 2)
      DeliverForge.forgeGuessedAdvantageShiftedDir2Paper
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        (qep + 1) DeliverForge.sameHdrScheme (t - 1) t challAdvDF ≤
      CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        ((R.B_cka tL t).eval (fun _ => challAdvDF) ()) +
      PRFPRNG.advantage (rootPRNG Z.F encPt)
        ((R.B_prng tL t).eval (fun _ => challAdvDF) ()) +
      (∑ j ∈ Finset.range q,
        CryptoVerification.E2E.fsAeadAuthSlotSumBound Z (min (2 * q) (q + 2)) R.fs
          (fun stage la => (R.B_fs stage la j tL t).eval (fun _ => challAdvDF) ())) +
      4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)
    (hB2 : ∀ t ∈ Finset.Ico 3 ((qep + 1) + 2),
      let tL : Option ℕ := some (t - 3)
      DeliverForge.forgeGuessedAdvantageShiftedPaper
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        (2 + 1) (qep + 1) DeliverForge.sameHdrScheme (t - 2) t challAdvDF ≤
      CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        ((R.B_cka tL t).eval (fun _ => challAdvDF) ()) +
      PRFPRNG.advantage (rootPRNG Z.F encPt)
        ((R.B_prng tL t).eval (fun _ => challAdvDF) ()) +
      (∑ j ∈ Finset.range q,
        CryptoVerification.E2E.fsAeadAuthSlotSumBound Z (min (2 * q) (q + 2)) R.fs
          (fun stage la => (R.B_fs stage la j tL t).eval (fun _ => challAdvDF) ())) +
      4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)
    (hU_cka : ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∀ par : Bool,
      CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (DeliverForge.redCKAAuthDFPaperBucket (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) tL par challAdvDF) ≤
      CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        ((R.B_cka_u tL par).eval (fun _ => challAdvDF) ()))
    (hU_ideal : ∀ tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1),
      ∀ par ∈ ({false, true} : Finset Bool),
      𝒟[CKA.branch (dhScheme Dh) 1 (healEpoch tL) true
          (DeliverForge.redCKAAuthDFPaperBucket (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) tL par
            challAdvDF)] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
        (PRFPRNG.advantage (rootPRNG Z.F encPt)
            ((R.B_prng_u tL par t).eval (fun _ => challAdvDF) ()) +
          (∑ j ∈ Finset.range q,
            CryptoVerification.E2E.fsAeadAuthSlotSumBound Z (min (2 * q) (q + 2)) R.fs
              (fun stage la => (R.B_fs_u stage la j tL par t).eval (fun _ => challAdvDF) ())))) +
      4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q) :
    let qR := min (2 * q) (q + 2)
    forgeStage2CellBucketSumPaper
      (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
      qep DeliverForge.sameHdrScheme challAdvDF ≤
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
          4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) := by
  intro qR
  unfold forgeStage2CellBucketSumPaper
  refine add_le_add (add_le_add (Finset.sum_le_sum hB1) (Finset.sum_le_sum hB2)) ?_
  refine Finset.sum_le_sum fun tL htL => Finset.sum_le_sum fun par hpar => ?_
  have hcka := DeliverForge.forgeBucketAdvantagePaper_le_cka_add_branch_true
    (dhScheme Dh) (rootPRNG Z.F encPt)
    (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1)
    (dhScheme_correct Dh hDh) Nat.one_pos tL par challAdvDF
  change DeliverForge.forgeBucketAdvantagePaper
      (scheme (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam)
      1 (qep + 1) DeliverForge.sameHdrScheme tL par challAdvDF ≤ _
  refine hcka.trans ?_
  rw [add_assoc]
  exact add_le_add (hU_cka tL htL par) (hU_ideal tL htL par hpar)

end PaperEvalBridges
end CryptoVerification.E2E

namespace CryptoVerification.E2E.Stage2BucketPRNGPackedBridge

open scoped BigOperators ENNReal MeasureTheory
open OracleSpec OracleComp
open ReductionDsl (CostedReduction)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic atomicShortPubB
  fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (prngAdvantage_congr)
open Computational.Proofs.SessionCostedFig8.Bundles (fig8CkaOpsShallow compilePrngDFAtomic)
open Computational.Proofs.SessionCostedFig8.BundlesEval (compilePrngDFAtomic_coinSimEquiv fsAtomicB_receive_rsReach)
open Computational.Proofs.SessionCostedFig8.FsAtomicBSwap (HooksLocalFsAgree vRecv_localFs_eq vSend_localFs_eq)
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.PRFPRNG (prngIface)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lAead lChainPRG lFS lPubOf)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open CryptoGames.SM (Config lastLeakGuessAdmissible)
open CryptoGames.SM.Construction (Header PartyState healEpoch mkParties redPRNGAuthDFPaperBucketSplitProg)
open CryptoGames.SM.Engine (Ctx EState Hooks HooksVRInv RSReach SMEngineInv SMVRInv VP abortE coinsE commitE deliverE implEDFPaperBucketRaw_inv implEDFPaperBucketRaw_vrInv injectE noDoomPolicy run_liftH_bind transmitEBucket_eq_transmitE)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge (DdhRoleOk badSendMsg_transmit_false commitE_localCKA_eq dhSchemeFb_receive_of_roleOk dhSchemeFb_send_of_roleOk implE_localCKA_eq localPartyInv_mkParties vRecv_localCKA_eq)
open CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF badSendMsgDF)

private lemma hooksPRNGBucketMain_fs_fields_congr {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs₁ fs₂ : FSAEADScheme K SS RS (Header T) M E)
    (hS : fs₁.initSender = fs₂.initSender) (hR : fs₁.initReceiver = fs₂.initReceiver)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng fs₁ Δcka qep tL par t).startSend =
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng fs₂ Δcka qep tL par t).startSend ∧
    (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng fs₁ Δcka qep tL par t).startRecv =
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng fs₂ Δcka qep tL par t).startRecv ∧
    (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng fs₁ Δcka qep tL par t).commit =
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng fs₂ Δcka qep tL par t).commit ∧
    (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng fs₁ Δcka qep tL par t).reveal =
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng fs₂ Δcka qep tL par t).reveal := by
  cases fs₁; cases fs₂; cases hS; cases hR; exact ⟨rfl, rfl, rfl, rfl⟩

private lemma hooksPRNGBucketForgedHdr_fs_fields_congr {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs₁ fs₂ : FSAEADScheme K SS RS (Header T) M E)
    (hS : fs₁.initSender = fs₂.initSender) (hR : fs₁.initReceiver = fs₂.initReceiver)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng fs₁ Δcka qep tL par t).startSend =
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng fs₂ Δcka qep tL par t).startSend ∧
    (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng fs₁ Δcka qep tL par t).startRecv =
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng fs₂ Δcka qep tL par t).startRecv ∧
    (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng fs₁ Δcka qep tL par t).commit =
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng fs₂ Δcka qep tL par t).commit ∧
    (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng fs₁ Δcka qep tL par t).reveal =
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng fs₂ Δcka qep tL par t).reveal := by
  cases fs₁; cases fs₂; cases hS; cases hR; exact ⟨rfl, rfl, rfl, rfl⟩


local instance {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

private lemma hooksPRNGBucketHybridGen_startRecv_rs_nereds {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    {VROk : RS → Prop}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (tn0 : T)
    (h : CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T Sig K I) (res : _)
    (hmem : res ∈ support (((CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).startRecv
      ctx P t0 γ0 σv0 tn0).run h))
    (γ' : Γ) (σ' : Option Sig) (rs : RS) (hEq : res.1 = some (some (γ', σ', rs))) :
    VROk rs := by
  dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hmem
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have hTail :
      res ∈ support ((do
        if !(qep + 1 < t0) && (lastLeakGuessAdmissible Δbucket tL t0 &&
            (CryptoGames.SM.Construction.DeliverForge.partyPar (CryptoGames.Party.senderOf t0) == par)) then
          if tL.isSome && t0 = healEpoch tL then
            return none
          else if CryptoGames.SM.Construction.DeliverForge.postLeak tL ctx || h.corrRoot.isSome || t < t0 then
            match CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with
            | none => return none
            | some σ =>
              let kk := cka.receive γ0 tn0
              let p := prng.up σ kk.2
              return some (some (kk.1, some p.1, fs.initReceiver p.2))
          else if t0 = t then
            let kk := cka.receive γ0 tn0
            match ← CryptoGames.SM.Construction.DeliverForge.liftPBucket (CryptoGames.PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) kk.2) with
            | none => return none
            | some (σOut, kOut) =>
              return some (some (kk.1, some σOut, fs.initReceiver kOut))
          else if !(t0 < healEpoch tL) then
            let kk := cka.receive γ0 tn0
            let kOut ← CryptoGames.SM.Construction.DeliverForge.lookupPRNGBucketF t0 kk.2
            return some (some (kk.1, none, fs.initReceiver kOut))
          else
            return some none
        else
          return some none).run h) → VROk rs := by
    intro hmem'
    split_ifs at hmem'
    · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
      subst hmem'; simp at hEq
    · rcases hres : CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with _ | σ
      · rw [hres, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
        subst hmem'; simp at hEq
      · rw [hres, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
        subst hmem'; rcases Option.some.inj (Option.some.inj hEq) with ⟨_, _, rfl⟩
        exact hInitR _
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem'
      obtain ⟨⟨o, _⟩, _, hmem'⟩ := hmem'
      rcases o with _ | ⟨σOut, kOut⟩
      · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
        subst hmem'; simp at hEq
      · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
        subst hmem'; rcases Option.some.inj (Option.some.inj hEq) with ⟨_, _, rfl⟩
        exact hInitR _
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem'
      obtain ⟨⟨kOut, _⟩, _, hmem'⟩ := hmem'
      rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
      subst hmem'; rcases Option.some.inj (Option.some.inj hEq) with ⟨_, _, rfl⟩
      exact hInitR _
    · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
      subst hmem'; simp at hEq
    · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
      subst hmem'; simp at hEq
  rcases hc : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
  · simp only [hc] at hmem; exact hTail hmem
  · by_cases hEqT : tCached = tn0
    · simp only [hc, hEqT, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; rcases Option.some.inj (Option.some.inj hEq) with ⟨_, _, rfl⟩
      exact hInitR _
    · simp only [hc, hEqT, ↓reduceIte] at hmem; exact hTail hmem

private lemma hooksPRNGBucketMainGen_startRecv_rs_nereds {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    {VROk : RS → Prop}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (tn0 : T)
    (h : CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T Sig K I) (res : _)
    (hmem : res ∈ support (((CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen cka prng fs Δbucket qep tL par t).startRecv
      ctx P t0 γ0 σv0 tn0).run h))
    (γ' : Γ) (σ' : Option Sig) (rs : RS) (hEq : res.1 = some (some (γ', σ', rs))) :
    VROk rs := by
  dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen] at hmem
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hc : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
  · simp only [hc] at hmem
    split_ifs at hmem <;>
      (rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; simp at hEq)
  · by_cases hEqT : tCached = tn0
    · simp only [hc, hEqT, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; rcases Option.some.inj (Option.some.inj hEq) with ⟨_, _, rfl⟩
      exact hInitR _
    · simp only [hc, hEqT, ↓reduceIte] at hmem
      split_ifs at hmem <;>
        (rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; simp at hEq)

private theorem hooksPRNGBucketHybrid_df_vrInv_fsAtomicB_nereds {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    HooksVRInv (RSReach maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) Δcka qep tL par t) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq :=
    hooksPRNGBucketHybridGen_startRecv_rs_nereds (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) (3 + Δcka) qep tL par t
      (fun k => (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD
        (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps k).mono (Nat.zero_le _))
      ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hmem
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact (fsAtomicB_receive_rsReach C ℓ encT idOf B0 _ hVR (Option.some.inj hEq)).2
  commit_vR _ _ _ new _ res hmem new' hEq := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hmem
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; cases Option.some.inj hEq; rfl

private theorem hooksPRNGBucketMain_df_vrInv_lFS_nereds {Pt KC Γ CCoins I KR RSt : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    HooksVRInv (RSReachB maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep tL par t) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq :=
    hooksPRNGBucketMainGen_startRecv_rs_nereds cka prng
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) (3 + Δcka) qep tL par t
      (fun k => (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps k).mono (Nat.zero_le _))
      ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hmem
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps _ hVR (Option.some.inj hEq)).2
  commit_vR _ _ _ new _ res hmem new' hEq := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hmem
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; cases Option.some.inj hEq; rfl

private theorem hooksPRNGBucketForgedHdr_df_vrInv_lFS_nereds {Pt KC Γ CCoins I KR RSt : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    HooksVRInv (RSReachB maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep tL par t) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq :=
    hooksPRNGBucketHybridGen_startRecv_rs_nereds cka prng
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) (3 + Δcka) qep tL par t
      (fun k => (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps k).mono (Nat.zero_le _))
      ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hmem
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps _ hVR (Option.some.inj hEq)).2
  commit_vR _ _ _ new _ res hmem new' hEq := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hmem
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; cases Option.some.inj hEq; rfl

private theorem hooksPRNGBucketMain_df_localFsAgree_nereds {Pt KC Γ CCoins I KR RSt : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    HooksLocalFsAgree ℓ B0
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng (fsAtomicB C ℓ encT idOf B0) Δcka qep tL par t)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep tL par t) where
  startSend_eq :=
    (hooksPRNGBucketMain_fs_fields_congr cka prng (fsAtomicB C ℓ encT idOf B0)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) rfl rfl Δcka qep tL par t).1
  startRecv_eq :=
    (hooksPRNGBucketMain_fs_fields_congr cka prng (fsAtomicB C ℓ encT idOf B0)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) rfl rfl Δcka qep tL par t).2.1
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen]
    rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen]
    rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq :=
    (hooksPRNGBucketMain_fs_fields_congr cka prng (fsAtomicB C ℓ encT idOf B0)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) rfl rfl Δcka qep tL par t).2.2.1
  reveal_eq :=
    (hooksPRNGBucketMain_fs_fields_congr cka prng (fsAtomicB C ℓ encT idOf B0)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) rfl rfl Δcka qep tL par t).2.2.2

private theorem hooksPRNGBucketForgedHdr_df_localFsAgree_nereds {Pt KC Γ CCoins I KR RSt : Type}
    [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    HooksLocalFsAgree ℓ B0
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng (fsAtomicB C ℓ encT idOf B0) Δcka qep tL par t)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep tL par t) where
  startSend_eq :=
    (hooksPRNGBucketForgedHdr_fs_fields_congr cka prng (fsAtomicB C ℓ encT idOf B0)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) rfl rfl Δcka qep tL par t).1
  startRecv_eq :=
    (hooksPRNGBucketForgedHdr_fs_fields_congr cka prng (fsAtomicB C ℓ encT idOf B0)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) rfl rfl Δcka qep tL par t).2.1
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen]
    rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen]
    rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq :=
    (hooksPRNGBucketForgedHdr_fs_fields_congr cka prng (fsAtomicB C ℓ encT idOf B0)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) rfl rfl Δcka qep tL par t).2.2.1
  reveal_eq :=
    (hooksPRNGBucketForgedHdr_fs_fields_congr cka prng (fsAtomicB C ℓ encT idOf B0)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) rfl rfl Δcka qep tL par t).2.2.2

private theorem hooksPRNGBucketHybrid_df_localCKAAgree_nereds {Pt KR RSt K SS RS M E : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    CryptoVerification.LibsignalSession.Fig8SchemeBridge.HooksLocalCKAAgree
      (fun P γ t0 => DdhRoleOk P t0 γ)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid (dhSchemeFb Dh) prng fs Δcka qep tL par t)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid (dhScheme Dh) prng fs Δcka qep tL par t) where
  startSend_eq ctx P t0 γ σ r h ht hSend hOk := by
    have ht1 : (t0 - 1) + 1 = t0 := Nat.sub_add_cancel ht
    have hSend' : P.sendsIn ((t0 - 1) + 1) = true := ht1.symm ▸ hSend
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid,
      CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen]
    have hCoin : ∀ (coins : BitVec 256) (h₁ : CryptoGames.SM.Construction.DeliverForge.PRNGBucketState Pt RSt K Pt) (res : _),
        res ∈ support ((do
          let c := (dhScheme Dh).send γ coins
          match ← CryptoGames.SM.Construction.DeliverForge.rootPRNGBucketHybrid prng (3 + Δcka) tL par t t0
              (CryptoGames.SM.Construction.DeliverForge.postLeak tL ctx) c.2.2 σ with
          | none => return none
          | some (σ', kVal) =>
            modify fun (s : CryptoGames.SM.Construction.DeliverForge.PRNGBucketState Pt RSt K Pt) =>
              { s with cache := Function.update s.cache t0 (some (c.2.1, σ', kVal)) }
            return some (c.1, c.2.1, σ', fs.initSender kVal)).run h₁) →
        ∀ γ' T σ' ss, res.1 = some (γ', T, σ', ss) → DdhRoleOk P t0 γ' := by
      intro coins h₁ res hmem γ' T σ' ss hSome
      have hsnd := dhSchemeFb_send_of_roleOk Dh hOk hSend' coins
      simp only [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨rtRes, _⟩, _, hmem⟩ := hmem
      rcases rtRes with _ | ⟨σ₁, kVal⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; cases hSome
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; cases hSome
        exact ht1 ▸ hsnd.2
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    refine ⟨?_, fun res hmem γ' T σ' ss hSome => ?_⟩
    · split_ifs
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        cases r with
        | none =>
          simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
          refine bind_congr fun coins => ?_
          rw [(dhSchemeFb_send_of_roleOk Dh hOk hSend' coins).1]
        | some coins =>
          dsimp only
          rw [(dhSchemeFb_send_of_roleOk Dh hOk hSend' coins).1]
      · cases r with
        | none =>
          simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
          refine bind_congr fun coins => ?_
          rw [(dhSchemeFb_send_of_roleOk Dh hOk hSend' coins).1]
        | some coins =>
          dsimp only
          rw [(dhSchemeFb_send_of_roleOk Dh hOk hSend' coins).1]
    · split_ifs at hmem
      · rw [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
        cases r with
        | none =>
          rw [StateT.run_bind, StateT.run_lift, bind_assoc, mem_support_bind_iff] at hmem
          obtain ⟨coins, _, hmem⟩ := hmem
          rw [pure_bind] at hmem
          exact hCoin coins _ res hmem γ' T σ' ss hSome
        | some coins =>
          exact hCoin coins _ res hmem γ' T σ' ss hSome
      · cases r with
        | none =>
          rw [StateT.run_bind, StateT.run_lift, bind_assoc, mem_support_bind_iff] at hmem
          obtain ⟨coins, _, hmem⟩ := hmem
          rw [pure_bind] at hmem
          exact hCoin coins _ res hmem γ' T σ' ss hSome
        | some coins =>
          exact hCoin coins _ res hmem γ' T σ' ss hSome
  startRecv_eq ctx P t0 γ σ Tn h ht hRecv hOk := by
    have ht1 : (t0 - 1) + 1 = t0 := Nat.sub_add_cancel ht
    have hRecv' : P.sendsIn ((t0 - 1) + 1) = false := ht1.symm ▸ hRecv
    have hrcv := dhSchemeFb_receive_of_roleOk Dh hOk hRecv' Tn
    have hRecvEq := hrcv.1
    have hRecvOk : DdhRoleOk P t0 ((dhScheme Dh).receive γ Tn).1 := ht1 ▸ hrcv.2
    refine ⟨?_, fun res hmem γ' σ' rs hSome => ?_⟩
    · dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid,
        CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen]
      simp only [hRecvEq]
    · dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid,
        CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hmem
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      have hTail :
          res ∈ support ((do
            if !(qep + 1 < t0) && (lastLeakGuessAdmissible (3 + Δcka) tL t0 &&
                (CryptoGames.SM.Construction.DeliverForge.partyPar (CryptoGames.Party.senderOf t0) == par)) then
              if tL.isSome && t0 = healEpoch tL then
                return none
              else if CryptoGames.SM.Construction.DeliverForge.postLeak tL ctx || h.corrRoot.isSome || t < t0 then
                match CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot h (t0 - 1) σ with
                | none => return none
                | some σ1 =>
                  let kk := (dhScheme Dh).receive γ Tn
                  let p := prng.up σ1 kk.2
                  return some (some (kk.1, some p.1, fs.initReceiver p.2))
              else if t0 = t then
                let kk := (dhScheme Dh).receive γ Tn
                match ← CryptoGames.SM.Construction.DeliverForge.liftPBucket (CryptoGames.PRFPRNG.challPrfQuery (State := RSt) (Input := Pt) (Output := K) kk.2) with
                | none => return none
                | some (σOut, kOut) =>
                  return some (some (kk.1, some σOut, fs.initReceiver kOut))
              else if !(t0 < healEpoch tL) then
                let kk := (dhScheme Dh).receive γ Tn
                let kOut ← CryptoGames.SM.Construction.DeliverForge.lookupPRNGBucketF t0 kk.2
                return some (some (kk.1, none, fs.initReceiver kOut))
              else
                return some none
            else
              return some none).run h) → DdhRoleOk P t0 γ' := by
        intro hmem'
        split_ifs at hmem'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
          subst hmem'; simp at hSome
        · rcases hR : CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot h (t0 - 1) σ with _ | σ1
          · simp only [hR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
            subst hmem'; simp at hSome
          · simp only [hR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
            subst hmem'; cases hSome; exact hRecvOk
        · simp only [StateT.run_bind, CryptoGames.SM.Construction.DeliverForge.liftPBucket,
            StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem'
          obtain ⟨ans, _, hmem'⟩ := hmem'
          rcases ans with _ | ⟨σOut, kOut⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
            subst hmem'; simp at hSome
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
            subst hmem'; cases hSome; exact hRecvOk
        · simp only [StateT.run_bind, mem_support_bind_iff] at hmem'
          obtain ⟨⟨kOut, _⟩, _, hmem'⟩ := hmem'
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
          subst hmem'; cases hSome; exact hRecvOk
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
          subst hmem'; simp at hSome
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem'
          subst hmem'; simp at hSome
      rcases hc : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
      · simp only [hc] at hmem; exact hTail hmem
      · by_cases hEq : tCached = Tn
        · simp only [hc, hEq, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; cases hSome; exact hRecvOk
        · simp only [hc, hEq, ↓reduceIte] at hmem; exact hTail hmem
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := rfl

private theorem hooksPRNGBucketMain_df_localCKAAgree_nereds {Pt KR RSt K SS RS M E : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    CryptoVerification.LibsignalSession.Fig8SchemeBridge.HooksLocalCKAAgree
      (fun P γ t0 => DdhRoleOk P t0 γ)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain (dhSchemeFb Dh) prng fs Δcka qep tL par t)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain (dhScheme Dh) prng fs Δcka qep tL par t) where
  startSend_eq := (hooksPRNGBucketHybrid_df_localCKAAgree_nereds Dh prng fs Δcka qep tL par t).startSend_eq
  startRecv_eq ctx P t0 γ σ Tn h ht hRecv hOk := by
    have ht1 : (t0 - 1) + 1 = t0 := Nat.sub_add_cancel ht
    have hRecv' : P.sendsIn ((t0 - 1) + 1) = false := ht1.symm ▸ hRecv
    have hrcv := dhSchemeFb_receive_of_roleOk Dh hOk hRecv' Tn
    have hRecvEq := hrcv.1
    have hRecvOk : DdhRoleOk P t0 ((dhScheme Dh).receive γ Tn).1 := ht1 ▸ hrcv.2
    refine ⟨?_, fun res hmem γ' σ' rs hSome => ?_⟩
    · dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain,
        CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen]
      simp only [hRecvEq]
    · dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMain,
        CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen] at hmem
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      rcases hc : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
      · simp only [hc] at hmem
        split_ifs at hmem <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
           subst hmem; simp at hSome)
      · by_cases hEq : tCached = Tn
        · simp only [hc, hEq, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; cases hSome; exact hRecvOk
        · simp only [hc, hEq, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
             subst hmem; simp at hSome)
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := rfl

private theorem hooksPRNGBucketForgedHdr_df_localCKAAgree_nereds {Pt KR RSt K SS RS M E : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    CryptoVerification.LibsignalSession.Fig8SchemeBridge.HooksLocalCKAAgree
      (fun P γ t0 => DdhRoleOk P t0 γ)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr (dhSchemeFb Dh) prng fs Δcka qep tL par t)
      (CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdr (dhScheme Dh) prng fs Δcka qep tL par t) where
  startSend_eq := (hooksPRNGBucketHybrid_df_localCKAAgree_nereds Dh prng fs Δcka qep tL par t).startSend_eq
  startRecv_eq := (hooksPRNGBucketHybrid_df_localCKAAgree_nereds Dh prng fs Δcka qep tL par t).startRecv_eq
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := rfl

private lemma badSendMsgDF_query_bind_step_nereds {St Msg Coins C α : Type} (Pmsg : Msg → Bool)
    (qy : (unifSpec + CryptoGames.SM.specDF St Msg Coins C).Domain)
    (mx : (unifSpec + CryptoGames.SM.specDF St Msg Coins C).Range qy →
      CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF St Msg Coins C α)
    (h : IsQueryBoundP
      ((liftM (OracleSpec.query qy) : OracleComp (unifSpec + CryptoGames.SM.specDF St Msg Coins C) _) >>= mx)
      (fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg t = true) 0) :
    badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg qy = false ∧
      ∀ u, IsQueryBoundP (mx u)
        (fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg t = true) 0 := by
  rw [isQueryBoundP_query_bind_iff] at h
  rcases h with ⟨hq0, hmx⟩
  have hbf : badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg qy = false :=
    Bool.eq_false_iff.mpr (hq0.resolve_right (by omega))
  refine ⟨hbf, fun u => ?_⟩
  have hu := hmx u; simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hu; exact hu

private lemma badSendMsgDF_inl_to_badSendMsg_nereds {St Msg Coins C : Type} (Pmsg : Msg → Bool)
    (t5 : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (h : badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg (.inr (.inl t5)) = false) :
    CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) Pmsg (.inr t5) = false := by
  rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P <;> exact h

private theorem implEDFPaperBucketRaw_localFs_eq_nereds {Pt ι : Type} [DecidableEq Pt] {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV : Type} {ℓ B0 B_q q' Δ qep : ℕ} {cfg : Config (LibsignalMsgPublicPart × Plain ℓ)}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) CCoins γV σV
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂) (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP γV Pt σV (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (t_sm : (CryptoGames.SM.Construction.DeliverForge.specDF (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (hBad : badSendMsgDF
      (St := PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) (.inr t_sm) = false)
    (hVR : SMVRInv (RSReachB maxForwardJumps) B_q (q' + 1) es.g) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ Δ qep maxForwardJumps cfg (.inr t_sm)).run es =
      (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ Δ qep maxForwardJumps cfg (.inr t_sm)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  rcases t_sm with t5 | ⟨P, c, c'⟩
  · have hBad5 := badSendMsgDF_inl_to_badSendMsg_nereds (fun m => atomicShortPubB m.1) t5 hBad
    rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · change (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₁ Δ qep (P, m, r)).run es =
        (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₂ Δ qep (P, m, r)).run es
      unfold CryptoGames.SM.Construction.DeliverForge.transmitEBucket
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win) = true
      · simp [hab]
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases es.g.epMgmt Δ qep P r.isSome with _ | s₁
        · rfl
        · have hm : atomicShortPubB m.1 = true :=
            badSendMsg_transmit_false
              (ok := fun (x : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB x.1) hBad5
          simp only [run_liftH_bind]
          exact congrArg (· >>= _) (vSend_localFs_eq hAg s₁ P (s₁.st P) m none r hm es.h)
    · rfl
    · change (deliverE hk₁ maxForwardJumps cfg (P, c)).run es =
        (deliverE hk₂ maxForwardJumps cfg (P, c)).run es
      have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
      unfold deliverE
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win) = true
      · simp [hab]
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases es.g.inTransit P.other c with _ | r
        · rfl
        · simp only [run_liftH_bind,
            vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c (some r) es.h (hVR P), hCommit]
    · change (injectE hk₁ Δ qep cfg (P, c)).run es =
        (injectE hk₂ Δ qep cfg (P, c)).run es
      have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
      unfold injectE
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases href :
          (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ)) = true
      · simp [href]
      · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c none es.h (hVR P), hCommit]
    · change (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₁ P).run es =
        (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₂ P).run es
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket; rw [hAg.reveal_eq]
  · change (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₁ Δ qep cfg (P, c, c')).run es =
      (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es
    have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · dsimp only; split_ifs
        · rfl
        · simp only [run_liftH_bind,
            vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c' none es.h (hVR P), hCommit]

private theorem simulateQ_implEDFPaperBucketMode_localFs_eq_nereds {Pt ι : Type} [DecidableEq Pt] {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV α : Type} {ℓ L B0 B_q q Δ qep : ℕ}
    {cfg : Config (LibsignalMsgPublicPart × Plain ℓ)}
    (gMain : Bool) (isHonest : HS → Header Pt → Bool)
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) CCoins γV σV
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂) (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) α}
    (hoa : oa.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) q)
    (hSendOk : IsQueryBoundP oa (fun t => badSendMsgDF
      (St := PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP γV Pt σV (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (winEp : Option ℕ)
    (hInv : SMEngineInv L B_q q es.g) (hVR : SMVRInv (RSReachB maxForwardJumps) B_q q es.g) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode hk₁ Δ qep maxForwardJumps cfg gMain isHonest) oa).run (es, winEp) =
      (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode hk₂ Δ qep maxForwardJumps cfg gMain isHonest) oa).run (es, winEp) := by
  have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
      (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
  induction oa using OracleComp.inductionOn generalizing q es winEp with
  | pure _ => simp only [simulateQ_pure]
  | query_bind qy mx ih =>
    obtain ⟨hBadQ, hBadMx⟩ := badSendMsgDF_query_bind_step_nereds (fun m => atomicShortPubB m.1) qy mx hSendOk
    rw [isQueryBoundP_query_bind_iff] at hoa
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind, hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · have hq0 : ¬ ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
          (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256)))
          (LibsignalMsgPublicPart × Plain ℓ) CCoins
          (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) (Sum.inl n) := by
        simp [ReductionDsl.isGameQuery]
      have hmx : ∀ u, (mx u).IsQueryBoundP _ q := fun u => by
        have hu := hoa.2 u; simp only [hq0, ↓reduceIte] at hu; exact hu
      have hInl₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ Δ qep maxForwardJumps cfg (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ Δ qep maxForwardJumps cfg (.inl n)).run es =
          (coinsE n).run es := rfl
      cases gMain <;>
        (unfold CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode
           CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
           CryptoGames.SM.Construction.DeliverForge.withWinEpDF;
         simp only [↓reduceIte, Bool.false_eq_true, StateT.run_mk];
         rw [hInl₁, hInl₂];
         simp only [coinsE, StateT.run_lift, bind_assoc, pure_bind];
         exact bind_congr fun u => ih u (hmx u) (hBadMx u) es _ hInv hVR)
    · have hq1 : ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
          (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256)))
          (LibsignalMsgPublicPart × Plain ℓ) CCoins
          (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) (Sum.inr t_sm) := by
        simp [ReductionDsl.isGameQuery]
      rcases q with _ | q'
      · exact absurd (hoa.1.resolve_left (not_not.mpr hq1)) (by omega)
      have hmx : ∀ u, (mx u).IsQueryBoundP _ q' := fun u => by
        have hu := hoa.2 u; simp only [hq1, ↓reduceIte] at hu; exact hu
      have hRaw := implEDFPaperBucketRaw_localFs_eq_nereds (Δ := Δ) (qep := qep) (cfg := cfg) hAg hVRHk hB0 es t_sm hBadQ hVR
      cases gMain <;>
        (unfold CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode
           CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
           CryptoGames.SM.Construction.DeliverForge.withWinEpDF;
         simp only [↓reduceIte, Bool.false_eq_true, StateT.run_mk];
         simp only [bind_assoc, hRaw];
         refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hr => ?_;
         simp only [pure_bind];
         exact ih u (hmx u) (hBadMx u) es' _
           (implEDFPaperBucketRaw_inv hk₂ cfg es t_sm hInv (u, es') hr)
           (implEDFPaperBucketRaw_vrInv hk₂ hVRHk cfg es t_sm hInv hVR (u, es') hr))

private theorem implEDFPaperBucketRaw_localCKA_eq_nereds {Pt ι : Type} [DecidableEq Pt]
    {TSpec : OracleSpec.{0, 0} ι} {HS RSt SS RS M E σV ssV rsV : Type}
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E
      (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) σV ssV rsV}
    (hAg : CryptoVerification.LibsignalSession.Fig8SchemeBridge.HooksLocalCKAAgree
      (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (Δ qep maxSkip : ℕ) (cfg : Config M)
    (es : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) M (Header Pt × E) HS)
    (t_sm : (CryptoGames.SM.Construction.DeliverForge.specDF (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E)).Domain)
    (hEs : CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv es) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ Δ qep maxSkip cfg (.inr t_sm)).run es =
      (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ Δ qep maxSkip cfg (.inr t_sm)).run es ∧
    ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ Δ qep maxSkip cfg (.inr t_sm)).run es),
      CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv res.2 := by
  rcases t_sm with t5 | ⟨P, c, c'⟩
  · rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · change (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₁ Δ qep (P, m, r)).run es =
          (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₂ Δ qep (P, m, r)).run es ∧
        ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₂ Δ qep (P, m, r)).run es),
          CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv res.2
      rw [transmitEBucket_eq_transmitE, transmitEBucket_eq_transmitE]
      exact implE_localCKA_eq hAg Δ qep maxSkip cfg noDoomPolicy es (.inl (.inl (.inl (.inl (P, m, r))))) hEs
    · refine ⟨rfl, fun res hmem => ?_⟩
      change res ∈ support ((CryptoGames.SM.Construction.DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
      dsimp only [CryptoGames.SM.Construction.DeliverForge.challEBucket] at hmem
      rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hEs
    · exact implE_localCKA_eq hAg Δ qep maxSkip cfg noDoomPolicy es (.inl (.inl (.inr (P, c)))) hEs
    · exact implE_localCKA_eq hAg Δ qep maxSkip cfg noDoomPolicy es (.inl (.inr (P, c))) hEs
    · change (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₁ P).run es =
          (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₂ P).run es ∧
        ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₂ P).run es),
          CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv res.2
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket abortE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hAg.reveal_eq]
      refine ⟨trivial, fun res hmem => ?_⟩
      by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true
      · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hEs
      · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨revRes, _⟩, _, hmem⟩ := hmem
        rcases revRes with _ | stP <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro Q; exact hEs Q)
  · change (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₁ Δ qep cfg (P, c, c')).run es =
        (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es ∧
      ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es),
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv res.2
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
      · by_cases hchk : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [hchk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
        · have hvr := vRecv_localCKA_eq hAg es.g P (es.g.st P) c' none es.h (hEs P)
          simp only [hchk, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvr.1]
          refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvrMem => ?_,
            fun res hmem => ?_⟩
          · rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
            · rfl
            · rfl
            · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
              · simp [hqep]
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
                by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
                · simp only [htriv, ↓reduceIte, StateT.run_bind]
                  rw [(commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                    { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).1]
                · simp [htriv]
          · rw [mem_support_bind_iff] at hmem; obtain ⟨⟨vrRes, h'⟩, hvrMem, hmem⟩ := hmem
            rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact hEs
            · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
              · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact hEs
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
                by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
                · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
                  obtain ⟨⟨cmRes, _⟩, hcmMem, hmem⟩ := hmem
                  have hcm := (commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                    { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).2 _ hcmMem
                  rcases cmRes with _ | s₁
                  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                    subst hmem; intro Q; dsimp [CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv] at *
                    rw [hcm.1]; exact hEs Q
                  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                      support_pure, Set.mem_singleton_iff] at hmem
                    subst hmem; exact hcm.2 s₁ rfl
                · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                  split_ifs at hmem <;>
                    (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                       support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs)

private theorem simulateQ_implEDFPaperBucketMode_localCKA_eq_nereds {Pt ι : Type} [DecidableEq Pt]
    {TSpec : OracleSpec.{0, 0} ι} {HS RSt SS RS M E σV ssV rsV α : Type}
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    (gMain : Bool) (isHonest : HS → Header Pt → Bool)
    {hk₁ hk₂ : Hooks TSpec HS (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E
      (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) σV ssV rsV}
    (hAg : CryptoVerification.LibsignalSession.Fig8SchemeBridge.HooksLocalCKAAgree
      (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (Δ qep maxSkip : ℕ) (cfg : Config M)
    (oa : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF
      (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E) α)
    (es : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) M (Header Pt × E) HS)
    (winEp : Option ℕ) (hEs : CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv es) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode hk₁ Δ qep maxSkip cfg gMain isHonest) oa).run (es, winEp) =
      (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode hk₂ Δ qep maxSkip cfg gMain isHonest) oa).run (es, winEp) := by
  have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
      (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
  induction oa using OracleComp.inductionOn generalizing es winEp with
  | pure _ => simp only [simulateQ_pure]
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind, hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · have hInl₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ Δ qep maxSkip cfg (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ Δ qep maxSkip cfg (.inl n)).run es =
          (coinsE n).run es := rfl
      cases gMain <;>
        (unfold CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode
           CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
           CryptoGames.SM.Construction.DeliverForge.withWinEpDF;
         simp only [↓reduceIte, Bool.false_eq_true, StateT.run_mk];
         rw [hInl₁, hInl₂];
         simp only [coinsE, StateT.run_lift, bind_assoc, pure_bind];
         exact bind_congr fun u => ih u es _ hEs)
    · have hStep := implEDFPaperBucketRaw_localCKA_eq_nereds hAg Δ qep maxSkip cfg es t_sm hEs
      cases gMain <;>
        (unfold CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode
           CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
           CryptoGames.SM.Construction.DeliverForge.withWinEpDF;
         simp only [↓reduceIte, Bool.false_eq_true, StateT.run_mk];
         simp only [bind_assoc, hStep.1];
         refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hr => ?_;
         simp only [pure_bind];
         exact ih u es' _ (hStep.2 (u, es') hr))

private theorem redPRNGAuthDFPaperBucketSplit_dhSchemeFb_eq_nereds {Pt KR RSt K SS RS M E : Type}
    [DecidableEq Pt] [Zero Pt] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (lam : Pt) (Δcka qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      Pt RSt SS RS M (BitVec 256) E) :
    CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit (dhSchemeFb Dh) prng fs lam Δcka qep tL par gMain t0 A =
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit (dhScheme Dh) prng fs lam Δcka qep tL par gMain t0 A := by
  have hInitA : (dhSchemeFb Dh).initA = (dhScheme Dh).initA := rfl
  have hInitB : (dhSchemeFb Dh).initB = (dhScheme Dh).initB := rfl
  cases gMain
  · unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketForgedHdr
      CryptoGames.SM.Construction.DeliverForge.engRunDFPaperBucketMode
      CryptoGames.SM.Construction.DeliverForge.initPRNGBucketHybrid
    simp only [Bool.false_eq_true, ↓reduceIte, hInitA, hInitB, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine bind_congr fun kc => ?_
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨rtRes, h₀⟩ _ => ?_
    rcases rtRes with _ | ⟨σv, kVal⟩
    · simp [StateT.run_pure]
    · simp only [StateT.run_pure, pure_bind, bind_assoc]
      let st₀ : Party → VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (Option RSt) SS RS :=
        fun
          | .A => (mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σv
              (fs.initSender kVal) (fs.initReceiver kVal)).1
          | .B => (mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σv
              (fs.initSender kVal) (fs.initReceiver kVal)).2
      have hEs₀ : CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv
          ({ g := { st := st₀, b := false }, h := h₀ } : EState _ M (Header Pt × E) _) :=
        localPartyInv_mkParties Dh kc σv (fs.initSender kVal) (fs.initReceiver kVal)
      exact congrArg (· >>= _) (simulateQ_implEDFPaperBucketMode_localCKA_eq_nereds
        false CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket
        (hooksPRNGBucketForgedHdr_df_localCKAAgree_nereds Dh prng fs Δcka qep tL par t0)
        (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) A _ none hEs₀)
  · unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketMain
      CryptoGames.SM.Construction.DeliverForge.engRunDFPaperBucket
      CryptoGames.SM.Construction.DeliverForge.initPRNGBucketHybrid
    simp only [↓reduceIte, hInitA, hInitB, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine bind_congr fun kc => ?_
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨rtRes, h₀⟩ _ => ?_
    rcases rtRes with _ | ⟨σv, kVal⟩
    · simp [StateT.run_pure]
    · simp only [StateT.run_pure, pure_bind, bind_assoc]
      let st₀ : Party → VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (Option RSt) SS RS :=
        fun
          | .A => (mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σv
              (fs.initSender kVal) (fs.initReceiver kVal)).1
          | .B => (mkParties ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σv
              (fs.initSender kVal) (fs.initReceiver kVal)).2
      have hEs₀ : CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv
          ({ g := { st := st₀, b := false }, h := h₀ } : EState _ M (Header Pt × E) _) :=
        localPartyInv_mkParties Dh kc σv (fs.initSender kVal) (fs.initReceiver kVal)
      exact congrArg (· >>= _) (simulateQ_implEDFPaperBucketMode_localCKA_eq_nereds
        true (fun _ _ => false)
        (hooksPRNGBucketMain_df_localCKAAgree_nereds Dh prng fs Δcka qep tL par t0)
        (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) A _ none hEs₀)

private theorem redPRNGAuthDFPaperBucketSplit_fsAtomicB_eq_lFS_nereds
    {Pt KC Γ CCoins I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit cka prng (fsAtomicB C ℓ encT idOf B0)
        lam Δcka qep tL par gMain t0 A =
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL par gMain t0 A := by
  have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) qAdv := by
    refine hA.of_imp fun x hx => ?_; rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  have hS : (fsAtomicB C ℓ encT idOf B0).initSender =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender := rfl
  have hR : (fsAtomicB C ℓ encT idOf B0).initReceiver =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver := rfl
  have hms1 : (fsAtomicB C ℓ encT idOf B0).maxSkip = maxForwardJumps := rfl
  have hms2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  cases gMain
  · unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketForgedHdr
      CryptoGames.SM.Construction.DeliverForge.engRunDFPaperBucketMode
      CryptoGames.SM.Construction.DeliverForge.initPRNGBucketHybrid
    simp only [Bool.false_eq_true, ↓reduceIte, hS, hR, hms1, hms2, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine bind_congr fun kc => ?_
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨rtRes, h₀⟩ _ => ?_
    rcases rtRes with _ | ⟨σv, kVal⟩
    · simp [StateT.run_pure]
    · simp only [StateT.run_pure, pure_bind, bind_assoc]
      let st₀ : Party → VP Γ Pt (Option RSt) (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)) :=
        fun
          | .A => (mkParties (cka.initA kc) (cka.initB kc) σv
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender kVal)
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver kVal)).1
          | .B => (mkParties (cka.initA kc) (cka.initB kc) σv
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender kVal)
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver kVal)).2
      have hInv₀ : SMEngineInv (B_q + 1) B_q qAdv
          ({ st := st₀, b := false } : Ctx Γ Pt (Option RSt)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) :=
        (CryptoGames.SM.Engine.SMEngineInv.init _ false (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))).mono hqB
      have hVRHk := hooksPRNGBucketForgedHdr_df_vrInv_lFS_nereds cka prng C ℓ encT idOf Δcka qep tL par t0
      have hVR₀ : SMVRInv (RSReachB maxForwardJumps) B_q qAdv
          ({ st := st₀, b := false } : Ctx Γ Pt (Option RSt)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) := by
        intro P t₁ v hv
        cases P <;> simp only [st₀, mkParties] at hv
        · by_cases ht0 : t₁ = 0
          · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv; subst hv
            exact hVRHk.mono (Nat.zero_le _) (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
              ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
              (lChainPRG C.F) maxForwardJumps kVal)
          · simp [ht0] at hv
        · cases hv
      exact congrArg (· >>= _) (simulateQ_implEDFPaperBucketMode_localFs_eq_nereds
        (Δ := 2 + Δcka) (qep := qep)
        (cfg := CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par)
        false CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket
        (hooksPRNGBucketForgedHdr_df_localFsAgree_nereds cka prng C ℓ encT idOf B0 Δcka qep tL par t0)
        hVRHk hB0 hA' hSendOk { g := { st := st₀, b := false }, h := h₀ } none hInv₀ hVR₀)
  · unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketMain
      CryptoGames.SM.Construction.DeliverForge.engRunDFPaperBucket
      CryptoGames.SM.Construction.DeliverForge.initPRNGBucketHybrid
    simp only [↓reduceIte, hS, hR, hms1, hms2, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine bind_congr fun kc => ?_
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨rtRes, h₀⟩ _ => ?_
    rcases rtRes with _ | ⟨σv, kVal⟩
    · simp [StateT.run_pure]
    · simp only [StateT.run_pure, pure_bind, bind_assoc]
      let st₀ : Party → VP Γ Pt (Option RSt) (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)) :=
        fun
          | .A => (mkParties (cka.initA kc) (cka.initB kc) σv
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender kVal)
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver kVal)).1
          | .B => (mkParties (cka.initA kc) (cka.initB kc) σv
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender kVal)
              ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver kVal)).2
      have hInv₀ : SMEngineInv (B_q + 1) B_q qAdv
          ({ st := st₀, b := false } : Ctx Γ Pt (Option RSt)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) :=
        (CryptoGames.SM.Engine.SMEngineInv.init _ false (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))).mono hqB
      have hVRHk := hooksPRNGBucketMain_df_vrInv_lFS_nereds cka prng C ℓ encT idOf Δcka qep tL par t0
      have hVR₀ : SMVRInv (RSReachB maxForwardJumps) B_q qAdv
          ({ st := st₀, b := false } : Ctx Γ Pt (Option RSt)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) := by
        intro P t₁ v hv
        cases P <;> simp only [st₀, mkParties] at hv
        · by_cases ht0 : t₁ = 0
          · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv; subst hv
            exact hVRHk.mono (Nat.zero_le _) (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
              ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
              (lChainPRG C.F) maxForwardJumps kVal)
          · simp [ht0] at hv
        · cases hv
      exact congrArg (· >>= _) (simulateQ_implEDFPaperBucketMode_localFs_eq_nereds
        (Δ := 2 + Δcka) (qep := qep)
        (cfg := CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par)
        true (fun _ _ => false)
        (hooksPRNGBucketMain_df_localFsAgree_nereds cka prng C ℓ encT idOf B0 Δcka qep tL par t0)
        hVRHk hB0 hA' hSendOk { g := { st := st₀, b := false }, h := h₀ } none hInv₀ hVR₀)


private theorem redPRNGAuthDFPaperBucketSplitProg_advantage_atomic_nereds {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    PRFPRNG.advantage (rootPRNG C.F encPt)
      ((CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg (q + 1) B0 Δcka qep maxForwardJumps tL par gMain t0 :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL par gMain t0 A) := by
  intro B0
  exact CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg_advantage_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q Δcka qep tL par gMain t0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksPRNGBucketHybrid_df_vrInv_fsAtomicB_nereds Dh encPt C ℓ encT idOf B0 Δcka qep tL par t0)
    (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD
      (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec => (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

private theorem compilePrngDFAtomic_paperBucketSplit_advantage_nereds {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    PRFPRNG.advantage (rootPRNG C.F encPt)
      ((compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg (q + 1) B0 1 qep maxForwardJumps tL par gMain t0)).eval
        (fun _ => A) ()) =
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par gMain t0 A) := by
  intro B0
  rw [prngAdvantage_congr (rootPRNG C.F encPt)
      (compilePrngDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0
        (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg (q + 1) B0 1 qep maxForwardJumps tL par gMain t0) A),
    redPRNGAuthDFPaperBucketSplitProg_advantage_atomic_nereds Dh encPt C ℓ encT idOf lam 1 qep q tL par gMain t0 A hqA,
    redPRNGAuthDFPaperBucketSplit_dhSchemeFb_eq_nereds Dh (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
      lam 1 qep tL par gMain t0 A,
    redPRNGAuthDFPaperBucketSplit_fsAtomicB_eq_lFS_nereds (dhScheme Dh) (rootPRNG C.F encPt) C ℓ encT idOf lam
      B0 q 1 qep tL par gMain t0 (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA]

private theorem compilePrngDFAtomic_paperBucketPacked_le_advantage_nereds {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketPacked (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par t A) ≤
    PRFPRNG.advantage (rootPRNG C.F encPt)
      ((Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFPaperBucketHybridAtomicProg
          Dh encPt C ℓ encT idOf lam qep q tL par t).eval (fun _ => A) ()) := by
  by_cases hAct : CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch (3 + 1) tL par t = true
  · have hProg :
        Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFPaperBucketHybridAtomicProg
          Dh encPt C ℓ encT idOf lam qep q tL par t =
        compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1))
          (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg
            (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL par false t) := by
      unfold Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFPaperBucketHybridAtomicProg
      rw [hAct]; rfl
    have hSlotM : CryptoGames.SM.Construction.DeliverForge.bucketSlotIsMain (3 + 1) tL par t = false := by
      simp [CryptoGames.SM.Construction.DeliverForge.bucketSlotIsMain, hAct]
    have hSlotE : CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch (3 + 1) tL par t = t := by
      simp [CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch, hSlotM]
    unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketPacked
    rw [hProg, hSlotM, hSlotE]
    exact le_of_eq (compilePrngDFAtomic_paperBucketSplit_advantage_nereds
      Dh encPt C ℓ hℓ encT idOf lam qep q tL par false t A hqA hshA).symm
  · have hActF : CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch (3 + 1) tL par t = false :=
      Bool.eq_false_iff.mpr hAct
    by_cases hPrev : (decide (healEpoch tL < t) &&
        CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch (3 + 1) tL par (t - 1)) = true
    · have hProg :
          Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFPaperBucketHybridAtomicProg
            Dh encPt C ℓ encT idOf lam qep q tL par t =
          compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1))
            (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg
              (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL par true (t - 1)) := by
        unfold Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFPaperBucketHybridAtomicProg
        change (if CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch (3 + 1) tL par t = true then _
          else if (decide (healEpoch tL < t) &&
            CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch (3 + 1) tL par (t - 1)) = true then _
          else _) = _
        rw [hActF, hPrev]; rfl
      have hSlotM : CryptoGames.SM.Construction.DeliverForge.bucketSlotIsMain (3 + 1) tL par t = true := by
        unfold CryptoGames.SM.Construction.DeliverForge.bucketSlotIsMain
        rw [Bool.and_assoc, hActF, Bool.not_false, Bool.true_and]; exact hPrev
      have hSlotE : CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch (3 + 1) tL par t = t - 1 := by
        simp [CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch, hSlotM]
      unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketPacked
      rw [hProg, hSlotM, hSlotE]
      exact le_of_eq (compilePrngDFAtomic_paperBucketSplit_advantage_nereds
        Dh encPt C ℓ hℓ encT idOf lam qep q tL par true (t - 1) A hqA hshA).symm
    · have hPrevF : (decide (healEpoch tL < t) &&
          CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch (3 + 1) tL par (t - 1)) = false :=
        Bool.eq_false_iff.mpr hPrev
      have hSlotM : CryptoGames.SM.Construction.DeliverForge.bucketSlotIsMain (3 + 1) tL par t = false := by
        unfold CryptoGames.SM.Construction.DeliverForge.bucketSlotIsMain
        rw [Bool.and_assoc, hActF, Bool.not_false, Bool.true_and]; exact hPrevF
      have hSlotE : CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch (3 + 1) tL par t = t := by
        simp [CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch, hSlotM]
      unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketPacked
      rw [hSlotM, hSlotE]
      change PRFPRNG.advantage (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketForgedHdr
          (dhScheme Dh) (rootPRNG C.F encPt) (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          lam 1 qep tL par t A) ≤ _
      rw [CryptoGames.SM.Construction.DeliverForge.prng_advantage_redPRNGAuthDFPaperBucketForgedHdr_eq_zero_of_inactive
        (dhScheme Dh) (rootPRNG C.F encPt) (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam 1 qep tL par t hActF A]
      exact bot_le

end CryptoVerification.E2E.Stage2BucketPRNGPackedBridge

namespace CryptoVerification.E2E

open _root_.ReductionDsl OracleSpec OracleComp ENNReal MeasureTheory
open _root_.CryptoGames _root_.CryptoGames.LibsignalSM _root_.CryptoGames.LibsignalSM.Inst
open _root_.CryptoGames.Ratchet _root_.CryptoGames.CKA _root_.CryptoGames.SM _root_.CryptoGames.SM.Construction
open _root_.CryptoGames.SM.Engine _root_.CryptoGames.SM.Thm1 _root_.CryptoGames.SM.ThmB
open _root_.CryptoGames.LibsignalSession _root_.CryptoGames.Ratchet.LibsignalInst
open _root_.CryptoGames.Ratchet.LibsignalSim _root_.CryptoGames.LibsignalSM.Proofs
open _root_.CryptoVerification.LibsignalSession _root_.CryptoVerification.LibsignalProtoCodec
open _root_.CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1
open _root_.CryptoVerification.E2E _root_.CryptoVerification.E2E.Signed
open _root_.CryptoGames.SM.Construction.AuthL11
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

section PaperEvalBridges

open _root_.CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 _root_.CryptoVerification.E2E.Signed
open _root_.CryptoGames.SM.Construction.AuthL11
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Direct Stage-2 / hoisted-MAC bound for any `DeliverForge` adversary `dfAdv`
making at most `q` queries with `SendMsgsOkDF` and `GuardedSMDFShort`: bounds
`forgeStage2CellBucketSumPaper` on `challSimDF'Paper (2 + 1) (qep + 1) dfAdv` by
`v1SessionRedsPaper`'s `B1` + `B2` + `(tL, par)` Stage-2 terms. -/
theorem forgeStage2CellBucketSumPaper_le_v1SessionRedsPaper_dfAdv
    (Z : Crypto) (K : MlKem) (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
    (dfAdv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q)
    (hsh_df : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv)
    (hg_df : GuardedSMDFShort dfAdv) :
    let qR := min (2 * q) (q + 2)
    let R := v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q
    let challAdvDF := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    forgeStage2CellBucketSumPaper
      (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
      qep DeliverForge.sameHdrScheme challAdvDF ≤
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
          4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) := by
  intro qR R challAdvDF
  have hq32' : 2 * q + 25002 < 2 ^ 32 := by omega
  have hq_ch : DeliverForge.MakesAtMostQueriesDF challAdvDF q :=
    challSimDF'Paper_queries (2 + 1) (qep + 1) dfAdv hq_df
  have hsh_ch : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) challAdvDF :=
    challSimDF'Paper_sendOk (2 + 1) (qep + 1) _ dfAdv hsh_df
  have hg_ch : GuardedSMDFShort challAdvDF :=
    challSimDF'Paper_guardedSMDFShort (2 + 1) (qep + 1) dfAdv hg_df
  have hRfs : R.fs = fsCostedRedsInst Z protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)) := rfl
  refine forgeStage2CellBucketSumPaper_le_of_stage2_bounds
      Z K Dh hDh encPt encT decT idA idB lam qep q R challAdvDF
      (fun t ht => ?_) (fun t ht => ?_) (fun tL htL par => ?_) (fun tL htL par _hpar => ?_)
  · dsimp only []
    have ht2 : 2 ≤ t := (Finset.mem_Ico.mp ht).1
    have h12 := Computational.Proofs.HeadlineV1.Stage2BucketPRNGSwap.hB1_hops12
      Z Dh hDh encPt encT (idsOf idA idB) lam qep t ht2 dfAdv
    have hcka := v1SessionRedsPaper_B_cka_advantage_df ℓ hℓ Z K idA idB Dh encPt encT decT lam qep q
      (healEpoch (some (t - 2))) (some (t - 2)) t dfAdv hq_df hsh_df
    dsimp only [] at hcka
    have hcka_rhs :
        Proofs.Refinement.redCKAHiddenSaltPaperDF (paramsV1 Z K idA idB) ℓ Dh encPt encT (idsOf idA idB) lam qep
          (some (t - 2)) t dfAdv =
        DeliverForge.redCKAAuthDFShiftedDir2Paper (dhScheme Dh) (Ratchet.rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam (qep + 1) (t - 1) t challAdvDF := by
      unfold Proofs.Refinement.redCKAHiddenSaltPaperDF
      split_ifs with h1 h2
      · rfl
      · exact absurd ⟨ht2, rfl⟩ h1
      · exact absurd ⟨ht2, rfl⟩ h1
    rw [hcka_rhs] at hcka
    have hprng := v1SessionRedsPaper_B_prng_advantage_df ℓ hℓ Z K idA idB Dh encPt encT decT lam qep q
      (some (t - 2)) t dfAdv hq_df hsh_df
    dsimp only [] at hprng
    have hprng_rhs :
        Proofs.Refinement.redPRNGHiddenSaltPaperDF (paramsV1 Z K idA idB) ℓ Dh encPt encT (idsOf idA idB) lam qep
          (some (t - 2)) t dfAdv =
        DeliverForge.redPRNGAuthDFShiftedDir2Paper (dhScheme Dh) (Ratchet.rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam (qep + 1) (t - 1) t challAdvDF := by
      unfold Proofs.Refinement.redPRNGHiddenSaltPaperDF
      split_ifs with h1 h2
      · rfl
      · exact absurd ⟨ht2, rfl⟩ h1
      · exact absurd ⟨ht2, rfl⟩ h1
    rw [hprng_rhs] at hprng
    have hfs := Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3B1.localAuthDFShiftedDir2Paper_le_casePaperAtomic_sum_min
      ℓ Z Dh hD encPt encT hinj hdum idA idB lam hℓ q qep t hq32' ht challAdvDF hq_ch hsh_ch hg_ch
    dsimp only [] at h12
    change _ ≤ CKA.advantage (dhScheme Dh) 1 (healEpoch (some (t - 2)))
        (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_cka (some (t - 2)) t).eval
          (fun _ => challAdvDF) ()) +
      PRFPRNG.advantage (rootPRNG Z.F encPt)
        (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_prng (some (t - 2)) t).eval
          (fun _ => challAdvDF) ()) + _ + _
    rw [hcka, hprng, hRfs]
    exact h12.trans ((add_le_add le_rfl hfs).trans (le_of_eq (add_assoc _ _ _).symm))
  · dsimp only []
    have ht3 : 3 ≤ t := (Finset.mem_Ico.mp ht).1
    have h12 := Computational.Proofs.HeadlineV1.Stage2BucketPRNGSwap.hB2_hops12
      Z Dh hDh encPt encT (idsOf idA idB) lam qep t ht3 dfAdv
    have hcka := v1SessionRedsPaper_B_cka_advantage_df ℓ hℓ Z K idA idB Dh encPt encT decT lam qep q
      (healEpoch (some (t - 3))) (some (t - 3)) t dfAdv hq_df hsh_df
    dsimp only [] at hcka
    have hcka_rhs :
        Proofs.Refinement.redCKAHiddenSaltPaperDF (paramsV1 Z K idA idB) ℓ Dh encPt encT (idsOf idA idB) lam qep
          (some (t - 3)) t dfAdv =
        DeliverForge.redCKAAuthDFShiftedPaper (dhScheme Dh) (Ratchet.rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) (t - 2) t challAdvDF := by
      unfold Proofs.Refinement.redCKAHiddenSaltPaperDF
      split_ifs with h1 h2
      · exfalso; rcases h1 with ⟨_, hEq⟩; have := Option.some.inj hEq; omega
      · rfl
      · exact absurd ⟨ht3, rfl⟩ h2
    rw [hcka_rhs] at hcka
    have hprng := v1SessionRedsPaper_B_prng_advantage_df ℓ hℓ Z K idA idB Dh encPt encT decT lam qep q
      (some (t - 3)) t dfAdv hq_df hsh_df
    dsimp only [] at hprng
    have hprng_rhs :
        Proofs.Refinement.redPRNGHiddenSaltPaperDF (paramsV1 Z K idA idB) ℓ Dh encPt encT (idsOf idA idB) lam qep
          (some (t - 3)) t dfAdv =
        DeliverForge.redPRNGAuthDFShiftedPaper (dhScheme Dh) (Ratchet.rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) (t - 2) t challAdvDF := by
      unfold Proofs.Refinement.redPRNGHiddenSaltPaperDF
      split_ifs with h1 h2
      · exfalso; rcases h1 with ⟨_, hEq⟩; have := Option.some.inj hEq; omega
      · rfl
      · exact absurd ⟨ht3, rfl⟩ h2
    rw [hprng_rhs] at hprng
    have hfs := Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3B2.localAuthDFShiftedPaper_le_casePaperAtomic_sum_min
      ℓ Z Dh hD encPt encT hinj hdum idA idB lam hℓ q qep t hq32' ht challAdvDF hq_ch hsh_ch hg_ch
    dsimp only [] at h12
    change _ ≤ CKA.advantage (dhScheme Dh) 1 (healEpoch (some (t - 3)))
        (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_cka (some (t - 3)) t).eval
          (fun _ => challAdvDF) ()) +
      PRFPRNG.advantage (rootPRNG Z.F encPt)
        (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_prng (some (t - 3)) t).eval
          (fun _ => challAdvDF) ()) + _ + _
    rw [hcka, hprng, hRfs]
    exact h12.trans ((add_le_add le_rfl hfs).trans (le_of_eq (add_assoc _ _ _).symm))
  · exact le_of_eq (Computational.Proofs.HeadlineV1.Stage2BucketCKASwap.compileCkaDFAtomic_paperBucket_advantage
      Dh encPt Z ℓ hℓ encT (idsOf idA idB) lam (healEpoch tL) (qep + 1) q tL par
      challAdvDF hq_ch hsh_ch).symm
  · have htH : healEpoch tL ≤ (qep + 1) + 1 :=
      Computational.Proofs.HeadlineV1.Stage2BucketPRNGSwap.admissibleLastLeakGuesses_four_healEpoch_le htL
    have hprng := DeliverForge.cka_branch_true_redCKAAuthDFPaperBucket_le_sum_prng_add_local
      (dhScheme Dh) (rootPRNG Z.F encPt) (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000)
      lam 1 (qep + 1) (dhScheme_correct Dh hDh) Nat.one_pos tL par htH challAdvDF
    have hprng_sum :
        (∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
          PRFPRNG.advantage (rootPRNG Z.F encPt)
            (DeliverForge.redPRNGAuthDFPaperBucketPacked (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) tL par t challAdvDF)) ≤
        ∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
          PRFPRNG.advantage (rootPRNG Z.F encPt)
            ((R.B_prng_u tL par t).eval (fun _ => challAdvDF) ()) :=
      Finset.sum_le_sum fun t _ht =>
        Stage2BucketPRNGPackedBridge.compilePrngDFAtomic_paperBucketPacked_le_advantage_nereds
          Dh encPt Z ℓ hℓ encT (idsOf idA idB) lam (qep + 1) q tL par t challAdvDF hq_ch hsh_ch
    have hfs := Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3Bucket.localAuthDFPaperBucket_main_add_forgedHdr_le_B_fs_u_sum_min
      ℓ Z Dh hDh hD encPt encT hinj hdum idA idB lam hℓ q qep hq32' tL htL par challAdvDF hq_ch hsh_ch hg_ch
    rw [hRfs]
    refine hprng.trans ?_
    refine (add_le_add hprng_sum hfs).trans ?_
    rw [← add_assoc, ← Finset.sum_add_distrib]
    exact le_rfl

/-- Unconditional Stage-2 sum bound on `R.simDeliverForge.eval (fun _ => A) ()`:
`forgeStage2CellBucketSumPaper` plus `spuriousStepTerm` and the ratchet-key collision term is
bounded above by `hiddenSaltBoundV1` evaluated on `v1SessionRedsPaper` (C001: ML-KEM failures
are charged as `MlKem.KemFailBad` at top level, not here). -/
theorem sum_hiddenSaltCellTermPaperDF_le_hiddenSaltBoundV1_paper
    (Z : Crypto) (K : MlKem) (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
    (δ : ℝ≥0∞)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q) :
    let R := v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q
    let dfAdv := R.simDeliverForge.eval (fun _ => A) ()
    forgeStage2CellBucketSumPaper
      (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
      qep DeliverForge.sameHdrScheme
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv) +
      spuriousStepTerm Z.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ ≤
    hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT idA idB lam qep q δ R A := by
  intro R dfAdv
  have hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg_makesAtMostQueriesDF
      ℓ Z K idA idB Dh encPt encT decT lam qep q A hq
  have hsh_df : SendMsgsOkDF
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) dfAdv :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg_sendAtomicShortDF
      hℓ Z K idA idB Dh encPt encT decT lam qep q A hq
  have hg_df : GuardedSMDFShort dfAdv :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg_guardedSMDFShort
      hℓ Z K idA idB Dh encPt encT decT lam qep q A hq
  have hchall : R.challSimDF.eval (fun _ => dfAdv) () =
      DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv :=
    v1SessionRedsPaper_challSimDF_eval ℓ hℓ Z K idA idB Dh encPt encT decT
      lam qep q dfAdv hq_df
  unfold hiddenSaltBoundV1; dsimp only
  rw [show R.challSimDF.eval (fun _ => R.simDeliverForge.eval (fun _ => A) ()) () =
        DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv from hchall]
  have hmain := forgeStage2CellBucketSumPaper_le_v1SessionRedsPaper_dfAdv
    Z K hD hℓ Dh hDh encPt encT decT hinj hdum idA idB lam qep q hq32 dfAdv hq_df hsh_df hg_df
  exact add_le_add (add_le_add hmain le_rfl) le_rfl

end PaperEvalBridges
end CryptoVerification.E2E

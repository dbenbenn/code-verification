/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA -- proof-setup: allow-public-import

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECoupleT -- proof-setup: allow-public-import
import ProofLib.SepLogic.WP.StateNorm
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatementsShort
import Computational.Proofs.HeadlineV1.HiddenSaltV1Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Defs
import Mathlib.Data.List.Dedup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Disjoint
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Attr.Register
import PolyFun.Control.Monad.Support
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import ToMathlib.Control.StateT
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.SecExp.Measure
import VCVio.EvalDist.Defs.Measure.Core
import VCVio.EvalDist.EvalDistEq
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Monad.Bool
import VCVio.EvalDist.ProbabilityBounds
import VCVio.EvalDist.ProbabilityNotation
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.AnswerMeasure
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.OracleSpec
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.Prelude.Core
import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Cell-Family Runner Unification and Bit Independence

Rewrites `forgeGuessedAdvantageCellPaper` in terms of the unified runner `runBaseDFCellPaper`,
proves `GameState.b` independence under `simImplDF'Paper`, and defines `cellSimRun` with its
win-monotonicity bounds.-/

namespace CryptoVerification.LibsignalSession.HeadlineV1
public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory


open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

theorem pprimePaperRel_init_b {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (k : Key) (b : Bool) :
    PPrimePaperRel (SM.initState sm k b) (toMirror (SM.initState sm k b))
      (SM.initState sm k b) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by intro _ h; simp [SM.initState] at h, by intro _ h; simp [SM.initState] at h,
    fun _ h => h, by intro _ h; simp [SM.initState] at h, fun _ h => h⟩

/-! ## Runner unification at zero shift -/

theorem corrImplShiftedPaper_zero_eq_corrImplPaper {St Msg C : Type} :
    corrImplShiftedPaper (St := St) (Msg := Msg) (C := C) 0 =
      DeliverForge.corrImplPaper := by
  funext P s
  unfold corrImplShiftedPaper DeliverForge.corrImplPaper
  simp [afterCorrShifted_zero_eq_afterCorr]

theorem oracleImplShiftedPaper_zero_eq_oracleImplPaper
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg) :
    oracleImplShiftedPaper sm Δ 0 qep cfg = DeliverForge.oracleImplPaper sm Δ qep cfg := by
  unfold oracleImplShiftedPaper DeliverForge.oracleImplPaper
  rw [corrImplShiftedPaper_zero_eq_corrImplPaper]

theorem oracleImplBaseDFShiftedPaper_zero_eq_oracleImplBaseDFPaper
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    oracleImplBaseDFShiftedPaper sm Δ 0 qep sameHdr cfg =
      DeliverForge.oracleImplBaseDFPaper sm Δ qep sameHdr cfg := by
  unfold oracleImplBaseDFShiftedPaper DeliverForge.oracleImplBaseDFPaper
  rw [oracleImplShiftedPaper_zero_eq_oracleImplPaper]

theorem fullImplBaseDFShiftedPaper_zero_eq_fullImplBaseDFPaper
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    fullImplBaseDFShiftedPaper sm Δ 0 qep sameHdr cfg =
      DeliverForge.fullImplBaseDFPaper sm Δ qep sameHdr cfg := by
  unfold fullImplBaseDFShiftedPaper DeliverForge.fullImplBaseDFPaper
  rw [oracleImplBaseDFShiftedPaper_zero_eq_oracleImplBaseDFPaper]

theorem runBaseDFShiftedPaper_zero_eq_runBaseDFPaper
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) (b : Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) :
    runBaseDFShiftedPaper sm Δ 0 qep sameHdr cfg b B =
      DeliverForge.runBaseDFPaper sm Δ qep sameHdr cfg b B := by
  unfold runBaseDFShiftedPaper DeliverForge.runBaseDFPaper
  rw [fullImplBaseDFShiftedPaper_zero_eq_fullImplBaseDFPaper]

/-- Expresses `forgeGuessedAdvantageCellPaper` as the `cellWinPred` event probability of
`runBaseDFCellPaper`. -/
theorem forgeGuessedAdvantageCellPaper_eq_runBaseDFCellPaper
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) :
    forgeGuessedAdvantageCellPaper sm (qep + 1) sameHdr tL t B =
      𝒟[do
        let (_, s') ←
          runBaseDFCellPaper sm (qep + 1) sameHdr tL t (SM.Config.auth t) false B
        return cellWinPred tL t s'] {true} := by
  unfold forgeGuessedAdvantageCellPaper cellWinPred
  split_ifs with h1 h2
  · rcases h1 with ⟨ht2, rfl⟩
    unfold forgeGuessedAdvantageShiftedDir2Paper forgeGameGuessedShiftedDir2Paper
      runBaseDFShiftedDir2Paper runBaseDFCellPaper
    rw [fullImplBaseDFCellPaper_eq_shiftedDir2 sm (qep + 1) sameHdr ht2 (SM.Config.auth t)]
    have hsub : t - 1 - 1 = t - 2 := by omega
    simp only [hsub]
  · rcases h2 with ⟨ht3, rfl⟩
    have hnot1 : ¬(2 ≤ t ∧ some (t - 3) = some (t - 2)) := by
      rintro ⟨_, h⟩; injection h; omega
    unfold forgeGuessedAdvantageShiftedPaper forgeGameGuessedShiftedPaper
      runBaseDFShiftedPaper runBaseDFCellPaper
    rw [fullImplBaseDFCellPaper_eq_shifted sm (qep + 1) sameHdr hnot1 (SM.Config.auth t)]
    have hD : cellDelta (some (t - 3)) t = 2 + 1 := by
      unfold cellDelta; simp only [hnot1, ↓reduceIte]
    have hS : cellShift (some (t - 3)) t = t - 2 := by
      unfold cellShift; simp only [hnot1, ht3, and_self, ↓reduceIte]
    have hsub : t - 2 - 1 = t - 3 := by omega
    simp only [hD, hS, hsub]
  · unfold DeliverForge.forgeGuessedAdvantagePaper DeliverForge.forgeGameGuessedPaper
      runBaseDFCellPaper
    rw [fullImplBaseDFCellPaper_eq_shifted sm (qep + 1) sameHdr h1 (SM.Config.auth t)]
    have hD : cellDelta tL t = 2 + 1 := by unfold cellDelta; simp [h1]
    have hS : cellShift tL t = 0 := by unfold cellShift; simp [h1, h2]
    rw [hD, hS, fullImplBaseDFShiftedPaper_zero_eq_fullImplBaseDFPaper]
    rfl

theorem simulateQ_fullImplBaseDFCellPaper_liftM_probComp
    {α Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ)
    (sameHdr : C → C → Bool) (tL : Option ℕ) (t : ℕ) (cfg : SM.Config Msg)
    (p : ProbComp α) (s : SM.GameState St Msg C) :
    (simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
      (liftM p : DeliverForge.AdversaryCompDF St Msg Coins C α)).run s =
      (p >>= fun a => pure (a, s)) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q_u k ih =>
    change (simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
      ((liftM (OracleSpec.query (spec := unifSpec + DeliverForge.specDF St Msg Coins C)
          (.inl q_u)) : DeliverForge.AdversaryCompDF St Msg Coins C _) >>=
        fun u => (liftM (k u) : DeliverForge.AdversaryCompDF St Msg Coins C α))).run s = _
    rw [simulateQ_query_bind, StateT.run_bind]
    change ((liftM (OracleSpec.query (spec := unifSpec) q_u) :
        StateT (SM.GameState St Msg C) ProbComp _).run s >>=
      fun z => (simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
        (liftM (k z.1))).run z.2) = _
    simp only [StateT.run_monadLift, bind_assoc, pure_bind, ih]

theorem simulateQ_simImplDF'Paper_liftM_probComp
    {α St Msg Coins C : Type} [DecidableEq C] (Δ qep : ℕ)
    (p : ProbComp α) (m' : Mirror Msg C) :
    (simulateQ (DeliverForge.simImplDF'Paper (St := St) (Coins := Coins) Δ qep)
      (liftM p : DeliverForge.AdversaryCompDF St Msg Coins C α)).run m' =
      ((liftM p : DeliverForge.AdversaryCompDF St Msg Coins C α) >>=
        fun a => pure (a, m')) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n r ih =>
    change (simulateQ (DeliverForge.simImplDF'Paper (St := St) (Coins := Coins) Δ qep)
      ((liftM (OracleSpec.query (spec := unifSpec + DeliverForge.specDF St Msg Coins C)
          (.inl n)) : DeliverForge.AdversaryCompDF St Msg Coins C _) >>=
        fun u => (liftM (r u) : DeliverForge.AdversaryCompDF St Msg Coins C α))).run m' =
      (((liftM (OracleSpec.query (spec := unifSpec + DeliverForge.specDF St Msg Coins C)
          (.inl n)) : DeliverForge.AdversaryCompDF St Msg Coins C _) >>=
        fun u => (liftM (r u) : DeliverForge.AdversaryCompDF St Msg Coins C α)) >>=
        fun a => pure (a, m'))
    rw [simulateQ_query_bind, StateT.run_bind]
    change (((DeliverForge.simCoinsDF (St := St) (Msg := Msg) (Coins := Coins) (C := C) n).run
        m') >>=
      fun z => (simulateQ (DeliverForge.simImplDF'Paper (St := St) (Coins := Coins) Δ qep)
        (liftM (r z.1) : DeliverForge.AdversaryCompDF St Msg Coins C α)).run z.2) = _
    unfold DeliverForge.simCoinsDF
    simp only [StateT_run_lift, bind_assoc, pure_bind, ih]
    rfl

theorem runBaseDFCellPaper_challSimDF'Paper_simDeliverForge_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (tL : Option ℕ) (t : ℕ)
    (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (f : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) → ProbComp Bool)
    (A : LibsignalSM.LibAdv PQ (BitVec 512) ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    𝒟[runBaseDFCellPaper fig (qep + 1) sameHdr tL t cfg false
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForge P ℓ Dh encPt encT decT idOf lam qep A)) >>=
      fun z => f z.2] =
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let m'₀ : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := { st := fun _ => (), b }
      let z ←
        (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) sameHdr tL t cfg)
          ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
            (((simulateQ (LibsignalSimC.simImplC P encT decT qep fig fs
                (deliverForgeHook Pt ℓ) Dh) A).run sC₀).run [])).run m'₀)).run
          (SM.initState fig k false)
      f z.2] := by
  intro fig fs
  unfold runBaseDFCellPaper DeliverForge.challSimDF'Paper simDeliverForge
    LibsignalSimC.simRunCWith
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_bind_swap (γ := Bool)
    ($ᵗ Bool : ProbComp Bool) ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _)]
  refine congrArg evalDist (congrArg (($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= ·)
    (funext fun k => ?_))
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
    simulateQ_bind, StateT.run_bind]
  rw [simulateQ_fullImplBaseDFCellPaper_liftM_probComp]
  simp only [bind_assoc, pure_bind]
  refine congrArg (($ᵗ Bool : ProbComp Bool) >>= ·) (funext fun b => ?_)
  rw [deliverForgeHook_lift_liftM_run]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_simImplDF'Paper_liftM_probComp,
    simulateQ_fullImplBaseDFCellPaper_liftM_probComp]
  refine congrArg (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= ·) (funext fun pqrKey => ?_)
  simp only [StateT.run_pure, simulateQ_pure, pure_bind]
  rfl

/-! ## Challenge-bit independence -/

@[expose] def withB {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    SM.GameState St Msg C :=
  { s with b := b }

@[simp] theorem withB_st {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).st = s.st := rfl

@[simp] theorem withB_epoch {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).epoch = s.epoch := rfl

@[simp] theorem withB_idx {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).idx = s.idx := rfl

@[simp] theorem withB_tL {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).tL = s.tL := rfl

@[simp] theorem withB_trans {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).trans = s.trans := rfl

@[simp] theorem withB_chall {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).chall = s.chall := rfl

@[simp] theorem withB_comp {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).comp = s.comp := rfl

@[simp] theorem withB_maxAcc {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).maxAcc = s.maxAcc := rfl

@[simp] theorem withB_win {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).win = s.win := rfl

@[simp] theorem withB_leaks {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).leaks = s.leaks := rfl

@[simp] theorem withB_corrs {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).corrs = s.corrs := rfl

@[simp] theorem withB_b {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).b = b := rfl

@[simp] theorem withB_set_win {St Msg C : Type} (b : Bool) (s : SM.GameState St Msg C) (w : Bool) :
    { withB b s with win := w } = withB b { s with win := w } := rfl

@[simp] theorem mustBeCorrect_withB {St Msg C : Type} (maxSkip : ℕ) (Q : Party)
    (r : SM.Record Msg C) (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).mustBeCorrect maxSkip Q r = s.mustBeCorrect maxSkip Q r := rfl

@[simp] theorem inTransit_withB {St Msg C : Type} [DecidableEq C]
    (P : Party) (c : C) (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).inTransit P c = s.inTransit P c := rfl

@[simp] theorem safeInj_withB {St Msg C : Type}
    (Δ : ℕ) (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).safeInj Δ = s.safeInj Δ := rfl

@[simp] theorem trivial_withB {St Msg C : Type}
    (Δ : ℕ) (pos : SM.Pos) (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).trivial Δ pos = s.trivial Δ pos := rfl

@[simp] theorem corrAllowedPaper_withB {St Msg C : Type}
    (P : Party) (b : Bool) (s : SM.GameState St Msg C) :
    (withB b s).corrAllowedPaper P = s.corrAllowedPaper P := rfl

theorem epMgmt_with_b {St Msg C : Type} (s : SM.GameState St Msg C)
    (Δ qep : ℕ) (P : Party) (bad b : Bool) :
    (withB b s).epMgmt Δ qep P bad =
      (s.epMgmt Δ qep P bad).map (withB b) := by
  unfold withB SM.GameState.epMgmt SM.GameState.leak SM.GameState.safeCh
  dsimp only
  split_ifs <;> rfl

@[simp] theorem record_with_b {St Msg C : Type} (s₁ : SM.GameState St Msg C)
    (Δ : ℕ) (P : Party) (st' : St) (rec_r : SM.Record Msg C) (isChall b : Bool) :
    (withB b s₁).record Δ P st' rec_r isChall =
      withB b (s₁.record Δ P st' rec_r isChall) :=
  rfl

@[simp] theorem accept_with_b {St Msg C : Type} [DecidableEq C] (s : SM.GameState St Msg C)
    (Q : Party) (st' : St) (pos : SM.Pos) (b : Bool) :
    (withB b s).accept Q st' pos = withB b (s.accept Q st' pos) :=
  rfl

@[simp] theorem afterCorrShifted_with_b {St Msg C : Type} (l : ℕ) (s : SM.GameState St Msg C)
    (P : Party) (b : Bool) :
    DeliverForge.afterCorrShifted l (withB b s) P =
      withB b (DeliverForge.afterCorrShifted l s P) :=
  rfl

theorem cellWinPred_with_b {St Msg C : Type} (tL : Option ℕ) (t : ℕ)
    (s : SM.GameState St Msg C) (b : Bool) :
    cellWinPred tL t (withB b s) = cellWinPred tL t s := by
  unfold withB cellWinPred authOKDir2 SM.authLosingConditionsAvoided SM.canon
  rfl

theorem transmitImpl_with_b {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    (P : Party) (m_msg : Msg) (r : Option Coins) (s : SM.GameState St Msg C) (b : Bool) :
    (SM.transmitImpl sm Δ qep (P, m_msg, r)).run (withB b s) =
      ((SM.transmitImpl sm Δ qep (P, m_msg, r)).run s >>=
        fun z => pure (z.1, withB b z.2)) := by
  unfold SM.transmitImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, withB_win]
  by_cases hwin : s.win = true
  · simp [hwin]
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      bind_assoc, pure_bind, epMgmt_with_b]
    refine congrArg (SM.samIfNec r >>= ·) (funext fun cb => ?_)
    cases s.epMgmt Δ qep P cb.2 <;> simp

theorem deliverImpl_with_b {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (cfg : SM.Config Msg)
    (Q : Party) (c : C) (s : SM.GameState St Msg C) (b : Bool) :
    (SM.deliverImpl sm cfg (Q, c)).run (withB b s) =
      ((SM.deliverImpl sm cfg (Q, c)).run s >>=
        fun z => pure (z.1, withB b z.2)) := by
  unfold SM.deliverImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, withB_win, inTransit_withB, withB_st,
    withB_chall, mustBeCorrect_withB]
  by_cases hwin : s.win = true
  · simp [hwin]
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    cases s.inTransit Q.other c with
    | none => simp
    | some r =>
      dsimp only
      cases sm.receive (s.st Q) c with
      | none =>
        rcases Bool.eq_false_or_eq_true
            (cfg.deliverWin && s.mustBeCorrect sm.maxSkip Q r) with h | h
        · simp only [h, ↓reduceIte]; simp; rfl
        · simp only [h, Bool.false_eq_true, ↓reduceIte]; simp
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        dsimp only
        rcases Bool.eq_false_or_eq_true (cfg.deliverWin && s.mustBeCorrect sm.maxSkip Q r &&
            !decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg))) with h | h
        · simp only [h, ↓reduceIte]; simp; rfl
        · simp only [h, Bool.false_eq_true, ↓reduceIte]; simp

@[simp] theorem cellTrivialT_withB {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (tL : Option ℕ) (t : ℕ) (pos : SM.Pos) (b : Bool) (s : SM.GameState St Msg C) :
    cellTrivialT tL t (withB b s) pos = cellTrivialT tL t s pos := rfl

theorem injectImplCell_with_b {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (t : ℕ) (cfg : SM.Config Msg)
    (Q : Party) (c : C) (s : SM.GameState St Msg C) (b : Bool) :
    (injectImplCell sm qep tL t cfg (Q, c)).run (withB b s) =
      ((injectImplCell sm qep tL t cfg (Q, c)).run s >>=
        fun z => pure (z.1, withB b z.2)) := by
  unfold injectImplCell
  simp only [StateT.run_bind, StateT.run_get, pure_bind, withB_win, inTransit_withB,
    safeInj_withB, cellTrivialT_withB, withB_st]
  rcases Bool.eq_false_or_eq_true
      (s.win || (s.inTransit Q.other c).isSome || !s.safeInj (cellDelta tL t)) with h1 | h1
  · simp only [h1, ↓reduceIte]; simp
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases sm.receive (s.st Q) c with
    | none => simp
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      by_cases h2 : qep + 1 < t'
      · simp [h2]
      · by_cases h3 : cellTrivialT tL t s { sender := Q.other, epoch := t', idx := i' } = true
        · simp [h2, h3]
        · by_cases h4 : cfg.injectFull t' = true
          · simp [h2, h3, h4]; rfl
          · simp [h2, h3, h4]

theorem corrImplShiftedPaper_with_b {St Msg C : Type} (l : ℕ)
    (P : Party) (s : SM.GameState St Msg C) (b : Bool) :
    (corrImplShiftedPaper l P).run (withB b s) =
      ((corrImplShiftedPaper l P).run s >>=
        fun z => pure (z.1, withB b z.2)) := by
  unfold corrImplShiftedPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind, withB_win, corrAllowedPaper_withB,
    withB_st]
  by_cases h : (s.win || !s.corrAllowedPaper P) = true <;> simp [h]

theorem deliverForgeBaseImplCell_with_b {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg)
    (Q : Party) (c c' : C) (s : SM.GameState St Msg C) (b : Bool) :
    (deliverForgeBaseImplCell sm qep tL t sameHdr cfg (Q, c, c')).run (withB b s) =
      ((deliverForgeBaseImplCell sm qep tL t sameHdr cfg (Q, c, c')).run s >>=
        fun z => pure (z.1, withB b z.2)) := by
  unfold deliverForgeBaseImplCell
  simp only [StateT.run_bind, StateT.run_get, pure_bind, withB_win, inTransit_withB,
    cellTrivialT_withB, withB_st, withB_comp]
  by_cases hwin : s.win = true
  · simp [hwin]
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    cases s.inTransit Q.other c with
    | none => simp
    | some r =>
      dsimp only
      rcases Bool.eq_false_or_eq_true ((s.inTransit Q.other c').isSome ||
          s.comp.contains r.pos || !sameHdr c c') with hbad | hbad
      · simp only [hbad, ↓reduceIte]; simp
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
        cases sm.receive (s.st Q) c' with
        | none => simp
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          by_cases h2 : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
          · simp [h2]
          · by_cases h3 : cellTrivialT tL t s { sender := Q.other, epoch := t', idx := i' } = true
            · simp [h2, h3]
            · by_cases h4 : cfg.injectFull t' = true
              · simp [h2, h3, h4]; rfl
              · simp [h2, h3, h4]

theorem simImplDF'Paper_step_with_b {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ₀ qep₀ qep : ℕ)
    (sameHdr : C → C → Bool) (tL : Option ℕ) (t : ℕ) (cfg : SM.Config Msg)
    (q_df : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain)
    (m' : Mirror Msg C) (s : SM.GameState St Msg C) (b : Bool) :
    (simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
      ((DeliverForge.simImplDF'Paper Δ₀ qep₀ q_df).run m')).run (withB b s) =
    ((simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
      ((DeliverForge.simImplDF'Paper Δ₀ qep₀ q_df).run m')).run s >>=
      fun z => pure (z.1, withB b z.2)) := by
  rcases q_df with n | ((((⟨P, m_msg, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | P) | ⟨Q, c, c'⟩
  · unfold DeliverForge.simImplDF'Paper DeliverForge.simCoinsDF
    simp [fullImplBaseDFCellPaper]
  · unfold DeliverForge.simImplDF'Paper DeliverForge.simOraclesDF'Paper
      DeliverForge.simTransmitDF'Paper DeliverForge.transmitQueryDF
    simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_bind, StateT.run_get,
      StateT_run_lift, pure_bind, simulateQ_bind, simulateQ_HasQuery_query,
      fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
      transmitImpl_with_b, bind_assoc]
    congr 1; funext ⟨res, s'⟩
    cases res <;> cases m'.epMgmt Δ₀ qep₀ P false <;> simp
  · unfold DeliverForge.simImplDF'Paper DeliverForge.simOraclesDF'Paper
      DeliverForge.simChallDF'Paper DeliverForge.transmitQueryDF
    simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_bind, StateT.run_get,
      pure_bind]
    cases m'.epMgmt Δ₀ qep₀ P false with
    | none => simp
    | some s₁ =>
      dsimp only
      cases s₁.safeCh Δ₀ P with
      | false => simp
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT_run_lift, simulateQ_bind, simulateQ_HasQuery_query,
          fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
          QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, transmitImpl_with_b, bind_assoc,
          pure_bind]
        congr 1; funext ⟨res, s'⟩
        cases res <;> simp
  · unfold DeliverForge.simImplDF'Paper DeliverForge.simOraclesDF'Paper
      DeliverForge.simDeliverDF DeliverForge.deliverQueryDF
    simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_bind, StateT.run_get,
      StateT_run_lift, pure_bind, simulateQ_bind, simulateQ_HasQuery_query,
      fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
      deliverImpl_with_b, bind_assoc]
    congr 1; funext ⟨res, s'⟩
    cases res with
    | none => simp
    | some rr =>
      cases rr <;> cases m'.inTransit Q.other c <;> simp
  · unfold DeliverForge.simImplDF'Paper DeliverForge.simOraclesDF'Paper
      DeliverForge.simInjectDF DeliverForge.injectQueryDF
    simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_bind, StateT.run_get,
      StateT_run_lift, pure_bind, simulateQ_bind, simulateQ_HasQuery_query,
      fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
      injectImplCell_with_b, bind_assoc]
    congr 1; funext ⟨res, s'⟩
    cases res with
    | none => simp
    | some rr => cases rr <;> simp
  · unfold DeliverForge.simImplDF'Paper DeliverForge.simOraclesDF'Paper
      DeliverForge.simCorrDFPaper DeliverForge.corrQueryDF
    simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_bind, StateT.run_get,
      pure_bind]
    split_ifs with hcorr
    · simp
    · simp only [StateT.run_bind, StateT_run_lift, simulateQ_bind, simulateQ_HasQuery_query,
        fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
        QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, corrImplShiftedPaper_with_b, bind_assoc,
        pure_bind]
      congr 1; funext ⟨res, s'⟩
      cases res <;> simp
  · unfold DeliverForge.simImplDF'Paper DeliverForge.simOraclesDF'Paper
      DeliverForge.simDeliverForgeDF DeliverForge.deliverForgeQuery
    simp only [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, StateT_run_lift,
      pure_bind, simulateQ_bind, simulateQ_HasQuery_query, fullImplBaseDFCellPaper,
      oracleImplBaseDFCellPaper, deliverForgeBaseImplCell_with_b, bind_assoc]
    congr 1; funext ⟨res, s'⟩
    cases res with
    | none => simp
    | some rr => cases rr <;> simp

theorem simulateQ_fullImplBaseDFCellPaper_simImplDF'Paper_with_b
    {α Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ₀ qep₀ qep : ℕ)
    (sameHdr : C → C → Bool) (tL : Option ℕ) (t : ℕ) (cfg : SM.Config Msg)
    (oa : OracleComp (unifSpec + DeliverForge.specDF St Msg Coins C) α) :
    ∀ (m' : Mirror Msg C) (s : SM.GameState St Msg C) (b : Bool),
      (simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
        ((simulateQ (DeliverForge.simImplDF'Paper Δ₀ qep₀) oa).run m')).run
        (withB b s) =
      ((simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
        ((simulateQ (DeliverForge.simImplDF'Paper Δ₀ qep₀) oa).run m')).run s >>=
        fun z => pure (z.1, withB b z.2)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro m' s b
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_df u ih =>
    intro m' s b
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
    change ((simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
        ((DeliverForge.simImplDF'Paper Δ₀ qep₀ q_df).run m')).run (withB b s) >>=
      fun p => (simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
        ((simulateQ (DeliverForge.simImplDF'Paper Δ₀ qep₀) (u p.1.1)).run p.1.2)).run p.2) =
      (((simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
        ((DeliverForge.simImplDF'Paper Δ₀ qep₀ q_df).run m')).run s >>=
      fun x => (simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg)
        ((simulateQ (DeliverForge.simImplDF'Paper Δ₀ qep₀) (u x.1.1)).run x.1.2)).run x.2) >>=
      fun z => pure (z.1, withB b z.2))
    rw [simImplDF'Paper_step_with_b, bind_assoc, bind_assoc]
    congr 1; funext z
    rw [pure_bind]
    exact ih z.1.1 z.1.2 z.2 b

theorem forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForge_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : LibsignalSM.LibAdv PQ (BitVec 512) ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    forgeGuessedAdvantageCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
        (simDeliverForge P ℓ Dh encPt encT decT idOf lam qep A)) =
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let m'₀ : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := { st := fun _ => (), b }
      let z ←
        (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
            tL t (SM.Config.auth t))
          ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
            (((simulateQ (LibsignalSimC.simImplC P encT decT qep fig fs
                (deliverForgeHook Pt ℓ) Dh) A).run sC₀).run [])).run m'₀)).run
          (SM.initState fig k b)
      return cellWinPred tL t z.2] {true} := by
  intro fig fs
  rw [forgeGuessedAdvantageCellPaper_eq_runBaseDFCellPaper]
  rw [runBaseDFCellPaper_challSimDF'Paper_simDeliverForge_eq P ℓ Dh encPt encT decT idOf lam
    qep DeliverForge.sameHdrScheme tL t (SM.Config.auth t)
    (fun s => pure (cellWinPred tL t s))]
  refine congrArg (fun m : ProbComp Bool => 𝒟[m] {true}) ?_
  refine congrArg (($ᵗ Bool : ProbComp Bool) >>= ·) (funext fun b => ?_)
  refine congrArg (($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= ·) (funext fun k => ?_)
  refine congrArg (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= ·) (funext fun pqrKey => ?_)
  dsimp only
  have hinit : SM.initState fig k b = withB b (SM.initState fig k false) := rfl
  rw [hinit, simulateQ_fullImplBaseDFCellPaper_simImplDF'Paper_with_b]
  simp only [bind_assoc, pure_bind, cellWinPred_with_b]
  rfl

/-! ## Cell-family runner and win monotonicity -/

abbrev cellSimRun {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ProbComp ((((α × LibsignalToModularSchemeSimState PQ Pt ℓ) × List (Fig8C Pt)) ×
      Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
      tL t (SM.Config.auth t))
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      (((simulateQ (LibsignalSimC.simImplC P encT decT qep fig fs
          (deliverForgeHook Pt ℓ) Dh) oa).run sC).run sent)).run m')).run s

theorem cellWinPred_mono_step_cell {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (q_df : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain)
    {s : SM.GameState St Msg C} (hwin : cellWinPred tL t s = true)
    {z : (unifSpec + DeliverForge.specDF St Msg Coins C).Range q_df × SM.GameState St Msg C}
    (hz : z ∈ support ((fullImplBaseDFCellPaper sm (qep + 1) sameHdr tL t
      (SM.Config.auth t) q_df).run s)) :
    z.2 = s ∧ cellWinPred tL t z.2 = true := by
  have hswin : s.win = true := s_win_of_cellWinPred hwin
  have hz_eq : z.2 = s := by
    rcases q_df with q_u | q_rest
    · simp only [fullImplBaseDFCellPaper, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_liftM, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] at hz
      rcases hz with ⟨x, _, hzx⟩; rw [hzx]
    · rcases q_rest with q_sm | ⟨Q, c, c'⟩
      · rcases q_sm with (((⟨P, m_msg, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | P
        · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
            SM.transmitImpl, hswin] at hz; exact congrArg Prod.snd hz
        · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
            SM.challImpl, hswin] at hz; exact congrArg Prod.snd hz
        · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
            SM.deliverImpl, hswin] at hz; exact congrArg Prod.snd hz
        · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
            injectImplCell, hswin] at hz; exact congrArg Prod.snd hz
        · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
            corrImplShiftedPaper, hswin] at hz; exact congrArg Prod.snd hz
      · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper,
          deliverForgeBaseImplCell, hswin] at hz; exact congrArg Prod.snd hz
  exact ⟨hz_eq, hz_eq ▸ hwin⟩

theorem simulateQ_fullImplBaseDFCellPaper_cellWinPred_of_true {α Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ)
    (oa : OracleComp (unifSpec + DeliverForge.specDF St Msg Coins C) α) :
    ∀ (s : SM.GameState St Msg C) (z : α × SM.GameState St Msg C),
      z ∈ support ((simulateQ (fullImplBaseDFCellPaper sm (qep + 1) sameHdr tL t
        (SM.Config.auth t)) oa).run s) →
      cellWinPred tL t s = true →
      cellWinPred tL t z.2 = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz hwin
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hwin
  | query_bind q_df u ih =>
    intro s z hz hwin
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u₁, s₁⟩, h₁, h₂⟩
    exact ih u₁ s₁ z h₂ ((cellWinPred_mono_step_cell sm qep sameHdr tL t q_df hwin h₁).2)

theorem evalDist_simulateQ_fullImplBaseDFCellPaper_cellWinPred_eq_one
    {α Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ)
    (oa : OracleComp (unifSpec + DeliverForge.specDF St Msg Coins C) α)
    (s : SM.GameState St Msg C) (hwin : cellWinPred tL t s = true) :
    𝒟[(simulateQ (fullImplBaseDFCellPaper sm (qep + 1) sameHdr tL t
        (SM.Config.auth t)) oa).run s >>=
      fun z => pure (cellWinPred tL t z.2)] {true} = 1 := by
  have hcongr :
      𝒟[(simulateQ (fullImplBaseDFCellPaper sm (qep + 1) sameHdr tL t
          (SM.Config.auth t)) oa).run s >>=
        fun z => pure (cellWinPred tL t z.2)] =
      𝒟[(simulateQ (fullImplBaseDFCellPaper sm (qep + 1) sameHdr tL t
          (SM.Config.auth t)) oa).run s >>=
        fun _ => (pure true : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    simp [simulateQ_fullImplBaseDFCellPaper_cellWinPred_of_true sm qep sameHdr tL t oa s z hz hwin]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

theorem cellSimRun_inl_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (n : unifSpec.Domain)
    (u : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inl n) →
      OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inl n) >>= u) sC sent m' s =
    ((OracleSpec.query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
      fun u₁ => cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC sent m' s) := by
  unfold cellSimRun
  dsimp only
  rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
  change (simulateQ (fullImplBaseDFCellPaper _ _ _ _ _ _)
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      ((((deliverForgeHook Pt ℓ).lift
          (liftM (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) :
            Fig8Comp Pt ℓ _)).run sent >>=
        fun z => pure ((z.1, sC), z.2)) >>=
      fun z => (((simulateQ (LibsignalSimC.simImplC P encT decT qep _ _
        (deliverForgeHook Pt ℓ) Dh) (u z.1.1)).run z.1.2).run z.2))).run m')).run s = _
  rw [deliverForgeHook_lift_liftM_run]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_simImplDF'Paper_liftM_probComp,
    simulateQ_fullImplBaseDFCellPaper_liftM_probComp]

/-! ## 6. Stage-2 `(tL, par)` Bucket Pure-Game Coupling Helpers (`[B7-b]`) -/

/-- Winning predicate of `DeliverForge.forgeGameBucketPaper` at `Δcka = 1` (`Δ = 2 + 1`). -/
@[expose] def bucketWinPred {St Msg C : Type} (tL : Option ℕ) (sw : SM.GameState St Msg C × Option ℕ) :
    Bool :=
  match sw.2 with
  | none => false
  | some tWin => sw.1.win && SM.authLosingConditionsAvoided (2 + 1) tL tWin sw.1

abbrev bucketSimRun {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (sw : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Option ℕ) :
    ProbComp ((((α × LibsignalToModularSchemeSimState PQ Pt ℓ) × List (Fig8C Pt)) ×
      Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Option ℕ)) :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  (simulateQ (DeliverForge.fullImplBaseDFPaperBucket fig 1 (qep + 1) DeliverForge.sameHdrScheme
      tL par)
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      (((simulateQ (LibsignalSimC.simImplC P encT decT qep fig fs
          (deliverForgeHook Pt ℓ) Dh) oa).run sC).run sent)).run m')).run sw

theorem fullImplBaseDFPaper_state_eq_of_win_true
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (sameHdr : C → C → Bool)
    (cfg : SM.Config Msg)
    (q_df : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain)
    {s : SM.GameState St Msg C} (hwin : s.win = true)
    {z : (unifSpec + DeliverForge.specDF St Msg Coins C).Range q_df × SM.GameState St Msg C}
    (hz : z ∈ support ((DeliverForge.fullImplBaseDFPaper sm Δ qep sameHdr cfg q_df).run s)) :
    z.2 = s := by
  rcases q_df with q_u | q_rest
  · simp only [DeliverForge.fullImplBaseDFPaper, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_liftM, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨x, _, hzx⟩; rw [hzx]
  · rcases q_rest with q_sm | ⟨Q, c, c'⟩
    · rcases q_sm with (((⟨P, m_msg, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | P
      · simp [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
          DeliverForge.oracleImplPaper, SM.transmitImpl, hwin] at hz; exact congrArg Prod.snd hz
      · simp [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
          DeliverForge.oracleImplPaper, SM.challImpl, hwin] at hz; exact congrArg Prod.snd hz
      · simp [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
          DeliverForge.oracleImplPaper, SM.deliverImpl, hwin] at hz; exact congrArg Prod.snd hz
      · simp [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
          DeliverForge.oracleImplPaper, SM.injectImpl, hwin] at hz; exact congrArg Prod.snd hz
      · simp [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
          DeliverForge.oracleImplPaper, DeliverForge.corrImplPaper, hwin] at hz
        exact congrArg Prod.snd hz
    · simp [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
        DeliverForge.deliverForgeBaseImpl, hwin] at hz; exact congrArg Prod.snd hz

theorem simulateQ_fullImplBaseDFPaper_win_of_true
    {α Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (sameHdr : C → C → Bool)
    (cfg : SM.Config Msg)
    (oa : OracleComp (unifSpec + DeliverForge.specDF St Msg Coins C) α) :
    ∀ (s : SM.GameState St Msg C) (z : α × SM.GameState St Msg C),
      z ∈ support ((simulateQ (DeliverForge.fullImplBaseDFPaper sm Δ qep sameHdr cfg) oa).run s) →
      s.win = true →
      z.2 = s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz _
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind q_df u ih =>
    intro s z hz hwin
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u₁, s₁⟩, h₁, h₂⟩
    have hs₁ : s₁ = s := fullImplBaseDFPaper_state_eq_of_win_true sm Δ qep sameHdr cfg q_df hwin h₁
    rw [hs₁] at h₂
    exact ih u₁ s z h₂ hwin

theorem fullImplBaseDFPaperBucket_state_eq_of_win_true
    {Key St Msg Coins T E : Type} [DecidableEq Msg] [DecidableEq T] [DecidableEq E]
    [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) (Δcka qep : ℕ)
    (sameHdr : (Header T × E) → (Header T × E) → Bool)
    (tL : Option ℕ) (par : Bool)
    (q_df : (unifSpec + DeliverForge.specDF St Msg Coins (Header T × E)).Domain)
    {sw : SM.GameState St Msg (Header T × E) × Option ℕ} (hwin : sw.1.win = true)
    {z : (unifSpec + DeliverForge.specDF St Msg Coins (Header T × E)).Range q_df ×
      (SM.GameState St Msg (Header T × E) × Option ℕ)}
    (hz : z ∈ support
      ((DeliverForge.fullImplBaseDFPaperBucket sm Δcka qep sameHdr tL par q_df).run sw)) :
    z.2 = sw := by
  rcases sw with ⟨s, winEp⟩
  dsimp only at hwin
  simp only [DeliverForge.fullImplBaseDFPaperBucket, DeliverForge.withWinEpDF, StateT.run_mk,
    MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨r, s'⟩, h₁, h₂⟩
  have hs' : s' = s :=
    fullImplBaseDFPaper_state_eq_of_win_true sm (2 + Δcka) qep sameHdr
      (DeliverForge.bucketAuthCfg Δcka tL par) q_df hwin h₁
  subst hs'
  simp [hwin] at h₂
  rw [h₂]

theorem evalDist_simulateQ_fullImplBaseDFPaperBucket_bucketWinPred_eq_one
    {α Key St Msg Coins T E : Type} [DecidableEq Msg] [DecidableEq T] [DecidableEq E]
    [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) (qep : ℕ)
    (sameHdr : (Header T × E) → (Header T × E) → Bool)
    (tL : Option ℕ) (par : Bool)
    (oa : OracleComp (unifSpec + DeliverForge.specDF St Msg Coins (Header T × E)) α)
    (sw : SM.GameState St Msg (Header T × E) × Option ℕ)
    (hwin : bucketWinPred tL sw = true) :
    𝒟[(simulateQ (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par) oa).run sw >>=
      fun z => pure (bucketWinPred tL z.2)] {true} = 1 := by
  have hswin : sw.1.win = true := by
    rcases sw with ⟨s, _ | tWin⟩
    · simp [bucketWinPred] at hwin
    · simp [bucketWinPred] at hwin; exact hwin.1
  have hstay : ∀ {α' : Type}
      (oa' : OracleComp (unifSpec + DeliverForge.specDF St Msg Coins (Header T × E)) α')
      (sw' : SM.GameState St Msg (Header T × E) × Option ℕ)
      (z : α' × (SM.GameState St Msg (Header T × E) × Option ℕ)),
      z ∈ support ((simulateQ (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par)
        oa').run sw') →
      sw'.1.win = true → z.2 = sw' := by
    intro α' oa'
    induction oa' using OracleComp.inductionOn with
    | pure a =>
      intro sw' z hz _
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    | query_bind q_df u ih =>
      intro sw' z hz hw'
      rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨⟨u₁, sw₁⟩, h₁, h₂⟩
      have hsw₁ := fullImplBaseDFPaperBucket_state_eq_of_win_true sm 1 (qep + 1) sameHdr tL par
        q_df hw' h₁
      rw [hsw₁] at h₂
      exact ih u₁ sw' z h₂ hw'
  have hcongr :
      ((simulateQ (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par) oa).run sw >>=
        fun z => pure (bucketWinPred tL z.2)) =
      ((simulateQ (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par) oa).run sw >>=
        fun _ => (pure true : ProbComp Bool)) := by
    refine OracleComp.bind_congr_of_forall_mem_support _ fun z hz => ?_
    rw [hstay oa sw z hz hswin, hwin]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

theorem fullImplBaseDFPaper_step_eq_and_bucket_of_no_win
    {Key St Msg Coins T E : Type} [DecidableEq Msg] [DecidableEq T] [DecidableEq E]
    [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) (qep : ℕ)
    (sameHdr : (Header T × E) → (Header T × E) → Bool)
    (tL : Option ℕ) (par : Bool)
    (q_df : (unifSpec + DeliverForge.specDF St Msg Coins (Header T × E)).Domain)
    {s₀ : SM.GameState St Msg (Header T × E)} (hwin₀ : s₀.win = false)
    (hno_win : ∀ t ∈ Finset.range ((qep + 1) + 2),
      ∀ z ∈ support ((DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr
        (SM.Config.auth t) q_df).run s₀), z.2.win = false) :
    (∀ t ∈ Finset.range ((qep + 1) + 2),
      (DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr (SM.Config.auth t) q_df).run s₀ =
        (DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr (SM.Config.auth 0) q_df).run s₀) ∧
    (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par q_df).run (s₀, none) =
      ((DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr (SM.Config.auth 0) q_df).run s₀ >>=
        fun z => pure (z.1, (z.2, none))) := by
  have hwin0_out : ∀ z ∈ support ((DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr
      (SM.Config.auth 0) q_df).run s₀), z.2.win = false :=
    hno_win 0 (Finset.mem_range.mpr (by omega))
  have hcfg_eq : ∀ (cfg : SM.Config Msg),
      cfg.deliverWin = false →
      cfg.challAllowedIn = (fun _ => false) →
      cfg.challMsg = (fun _ => none) →
      (DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr cfg q_df).run s₀ =
        (DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr (SM.Config.auth 0) q_df).run s₀ := by
    intro cfg hdw hca hcm
    rcases q_df with q_u | ((((⟨P, m_msg, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | P) | ⟨Q, c, c'⟩
    · rfl
    · rfl
    · simp [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
        DeliverForge.oracleImplPaper, SM.challImpl, SM.Config.auth, hca]
    · simp [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
        DeliverForge.oracleImplPaper, SM.deliverImpl, SM.Config.auth, hdw]
    · simp only [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
        DeliverForge.oracleImplPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      unfold SM.injectImpl
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin₀, Bool.false_or]
      by_cases hg1 : ((s₀.inTransit Q.other c).isSome || !s₀.safeInj (2 + 1)) = true
      · simp only [hg1, ↓reduceIte]
      · simp only [hg1, Bool.false_eq_true, ↓reduceIte]
        cases hrcv : sm.receive (s₀.st Q) c with
        | none => rfl
        | some v =>
          rcases v with ⟨st', t', i', m'⟩
          dsimp only
          by_cases hq : (qep + 1) + 1 < t'
          · simp only [hq, ↓reduceIte]
          · simp only [hq, ↓reduceIte]
            by_cases htriv : s₀.trivial (2 + 1) ⟨Q.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte]
            · exfalso
              have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
              have hz := hno_win t' ht'_mem (some .rejected, { s₀ with win := true }) ?_
              · simp at hz
              · simp only [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
                  DeliverForge.oracleImplPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
                unfold SM.injectImpl
                simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin₀, Bool.false_or,
                  hg1, Bool.false_eq_true, ↓reduceIte, hrcv, hq, htriv, SM.Config.auth,
                  beq_self_eq_true]
                simp [StateT.run_set]
    · rfl
    · simp only [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
        QueryImpl.add_apply_inr]
      unfold DeliverForge.deliverForgeBaseImpl
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin₀, Bool.false_eq_true, ↓reduceIte]
      cases hin : s₀.inTransit Q.other c with
      | none => rfl
      | some r =>
        dsimp only
        by_cases hg1 : ((s₀.inTransit Q.other c').isSome || s₀.comp.contains r.pos || !sameHdr c c') = true
        · simp only [hg1, ↓reduceIte]
        · simp only [hg1, Bool.false_eq_true, ↓reduceIte]
          cases hrcv : sm.receive (s₀.st Q) c' with
          | none => rfl
          | some v =>
            rcases v with ⟨st', t', i', m'⟩
            dsimp only
            by_cases hq : (decide ((qep + 1) + 1 < t') || (t' != r.pos.epoch)) = true
            · simp only [hq, ↓reduceIte]
            · simp only [hq, Bool.false_eq_true, ↓reduceIte]
              by_cases htriv : s₀.trivial (2 + 1) ⟨Q.other, t', i'⟩ = true
              · simp only [htriv, ↓reduceIte]
              · exfalso
                have ht'_le : t' ≤ (qep + 1) + 1 := by
                  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hq
                  exact hq.1
                have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
                have hz := hno_win t' ht'_mem (some .rejected, { s₀ with win := true }) ?_
                · simp at hz
                · simp only [DeliverForge.fullImplBaseDFPaper, DeliverForge.oracleImplBaseDFPaper,
                    QueryImpl.add_apply_inr]
                  unfold DeliverForge.deliverForgeBaseImpl
                  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin₀, hin, hg1,
                    Bool.false_eq_true, ↓reduceIte, hrcv, hq, htriv, SM.Config.auth,
                    beq_self_eq_true]
                  simp [StateT.run_set]
  refine ⟨fun t _ => hcfg_eq (SM.Config.auth t) rfl rfl rfl, ?_⟩
  simp only [DeliverForge.fullImplBaseDFPaperBucket, DeliverForge.withWinEpDF, StateT.run_mk]
  rw [hcfg_eq (DeliverForge.bucketAuthCfg 1 tL par) rfl rfl rfl]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun z hz => ?_
  simp [hwin₀, hwin0_out z hz]

theorem simulateQ_bucket_eq_map_auth0_of_no_win
    {α Key St Msg Coins T E : Type} [DecidableEq Msg] [DecidableEq T] [DecidableEq E]
    [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (Header T × E)) (qep : ℕ)
    (sameHdr : (Header T × E) → (Header T × E) → Bool)
    (tL : Option ℕ) (par : Bool)
    (oa : OracleComp (unifSpec + DeliverForge.specDF St Msg Coins (Header T × E)) α) :
    ∀ {s₀ : SM.GameState St Msg (Header T × E)},
      s₀.win = false →
      (∀ t ∈ Finset.range ((qep + 1) + 2),
        ∀ z ∈ support ((simulateQ (DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr
          (SM.Config.auth t)) oa).run s₀), z.2.win = false) →
      (simulateQ (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par) oa).run
        (s₀, none) =
      ((simulateQ (DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr
          (SM.Config.auth 0)) oa).run s₀ >>=
        fun z => pure (z.1, (z.2, none))) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s₀ _ _
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_df u ih =>
    intro s₀ hwin₀ hno_win
    have hstep_no_win : ∀ t ∈ Finset.range ((qep + 1) + 2),
        ∀ z₁ ∈ support ((DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr
          (SM.Config.auth t) q_df).run s₀), z₁.2.win = false := by
      intro t ht z₁ hz₁
      by_contra hw₁
      simp only [Bool.not_eq_false] at hw₁
      obtain ⟨z₂, hz₂⟩ := support_nonempty
        ((simulateQ (DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr
          (SM.Config.auth t)) (u z₁.1)).run z₁.2)
      have hz_tot : z₂ ∈ support ((simulateQ (DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1)
          sameHdr (SM.Config.auth t)) (OracleSpec.query q_df >>= u)).run s₀) := by
        rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind]
        exact ⟨z₁, hz₁, hz₂⟩
      have heq₂ := simulateQ_fullImplBaseDFPaper_win_of_true sm (2 + 1) (qep + 1) sameHdr
        (SM.Config.auth t) (u z₁.1) z₁.2 z₂ hz₂ hw₁
      have hf := hno_win t ht z₂ hz_tot
      rw [heq₂, hw₁] at hf
      exact Bool.false_ne_true hf.symm
    obtain ⟨hstep_eq, hstep_buck⟩ := fullImplBaseDFPaper_step_eq_and_bucket_of_no_win
      sm qep sameHdr tL par q_df hwin₀ hstep_no_win
    have hrun_q : ∀ {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ β : Type}
        (impl : QueryImpl spec (StateT σ ProbComp)) (q : spec.Domain)
        (k : spec.Range q → OracleComp spec β) (st : σ),
        (simulateQ impl (OracleSpec.query q >>= k)).run st =
          ((impl q).run st >>= fun z => (simulateQ impl (k z.1)).run z.2) := by
      intro ι spec σ β impl q k st
      rw [simulateQ_bind, simulateQ_query, StateT.run_bind]
      simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rw [hrun_q, hrun_q]
    rw [hstep_buck, bind_assoc]
    conv_rhs => rw [bind_assoc]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun z₁ hz₁ => ?_
    rw [pure_bind]
    have hw₁ : z₁.2.win = false :=
      hstep_no_win 0 (Finset.mem_range.mpr (by omega)) z₁ hz₁
    refine ih z₁.1 hw₁ fun t ht z₂ hz₂ => ?_
    have hz₁_t : z₁ ∈ support ((DeliverForge.fullImplBaseDFPaper sm (2 + 1) (qep + 1) sameHdr
        (SM.Config.auth t) q_df).run s₀) := by
      rwa [hstep_eq t ht]
    refine hno_win t ht z₂ ?_
    rw [hrun_q, MonadAttach.mem_support_bind]
    exact ⟨z₁, hz₁_t, hz₂⟩

theorem not_B1_not_B2_imp_inStage2Bucket
    {qep t₀ : ℕ} {tL₀ : Option ℕ}
    (ht₀ : t₀ ∈ Finset.range ((qep + 1) + 2))
    (htL₀ : tL₀ ∈ SM.admissibleLastLeakGuesses 2 t₀)
    (hnotB1 : ¬(2 ≤ t₀ ∧ tL₀ = some (t₀ - 2)))
    (hnotB2 : ¬(3 ≤ t₀ ∧ tL₀ = some (t₀ - 3))) :
    tL₀ ∈ SM.admissibleLastLeakGuesses 4 ((qep + 1) + 1) ∧
    DeliverForge.inStage2Bucket 1 tL₀ (DeliverForge.partyPar (Party.senderOf t₀)) t₀ = true := by
  have ht₀_lt := Finset.mem_range.mp ht₀
  rcases tL₀ with _ | m
  · simp [SM.admissibleLastLeakGuesses, DeliverForge.inStage2Bucket, SM.lastLeakGuessAdmissible]
  · simp only [SM.admissibleLastLeakGuesses, Finset.mem_insert, reduceCtorEq, Finset.mem_image,
      Option.some.injEq, exists_eq_right, Finset.mem_range, false_or] at htL₀ ⊢
    simp only [Option.some.injEq] at hnotB1 hnotB2
    have hm4 : m + 4 ≤ t₀ := by omega
    refine ⟨by omega, ?_⟩
    simp [DeliverForge.inStage2Bucket, SM.lastLeakGuessAdmissible]
    omega

end

end CryptoVerification.LibsignalSession.HeadlineV1

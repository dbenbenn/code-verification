/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8WeightedParts -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.ProgSizeBounds -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.ProgBoundsDefs
import Computational.Proofs.ReductionDsl.Notation
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.GameHop.ReductionDsl.SupportWP
import Computational.Proofs.ReductionDsl.SM.RedCKAPotOK
import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.SM.RedFSPotOK
import Computational.Proofs.ReductionDsl.SM.RedPRNGPrivQepPotOK
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.EtM
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Cost Bounds for Atomic Figure 8 Reductions

Proves `GRedBounded` within `ratchetCostBudget` and semantic query bounds for the compiled atomic
Figure 8 reductions of `Bundles.fig8RedsInst`.-/

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.ProgBounds

open Computational.Proofs.SessionCostedFig8.ProgBoundsDefs (const_le_fig8AtomicStepBound
  linear_le_fig8AtomicStepBound compiled_totalCost_le_ratchetCostBudget
  compiled_le_ratchetCostBudget dummy_le_ratchetCostBudget ckaOpMacro_cost_le)

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface Expr Comp CostedReduction bits reductionSizeBudget
  AtomicUnifBase ckaTargetIface prngTargetIface atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest
  bits_le_succ)
open _root_.CryptoGames (Party)
open _root_.CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open Computational.Proofs.SessionCostedFig8.QuerySubsumes (QuerySubsumes)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (compCostUB exprCostUB
  compCost_le_costUB exprCost_le_costUB)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_succ_le)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded HooksCostBounded.mono
  hooksCKAC_costBounded hooksPRNGC_costBounded hooksFSC_costBounded_linear
  initCKAEStateC_cost_le initPRNGEStateC_cost_le initFSEStateC_cost_le
  implEC_cost_le vRecvC_cost_le commitEC_cost_le
  cInTransitE_cost_le cCompContainsE_cost_le cTrivialE_cost_le
  fig8StepBound thm1_simHandleC_cost_le
  bits_le_bits_qep_add targetsL_bounds
  v0_cost v1_cost v2_cost v3_cost v4_cost v5_cost v6_cost v7_cost
  otherE_cost isSomeE_cost pGet_cost
  cGsEpoch_cost cGsIdx_cost cGsSt_cost cGsB_cost cRecPos_cost
  esG_cost esH_cost esAbort_cost esSetG_cost esSetH_cost esSetAbort_cost
  cGsSetWin_cost cGsSetStP_cost
  authOutE_cost_le privOutC_cost_le)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (HooksExcessBounded HooksExcessBounded.mono
  hooksCKAC_excessBounded hooksPRNGC_excessBounded hooksFSC_excessBounded
  initCKAEStateC_excessUB_le initPRNGEStateC_excessUB_le initFSEStateC_excessUB_le
  implEC_excessUB_le vSendC_excessUB_le vRecvC_excessUB_le commitEC_excessUB_le
  cInTransitE_excessUB optNatLit_excessUB
  smOpC smSampC smQueryC ckaOpC ckaSampC
  ckaQueryC prngQueryC fsQueryC exprExcessUB compExcessUB compCostW_le_cost_add_excessUB
  privOutC_excessUB_le pureEngineExprs_excessUB
  thm1_simInitC_cost_le thm1_simInitC_excessUB_le thm1_simHandleC_excessUB_le
  compExcessUB_bind compExcessUB_ret compExcessUB_sample compExcessUB_ite
  compExcessUB_caseOpt compExcessUB_caseSum compExcessUB_query
  exprExcessUB_v0 exprExcessUB_v1 exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4
  exprExcessUB_v5 exprExcessUB_v6 exprExcessUB_v7 exprExcessUB_var
  exprExcessUB_unit exprExcessUB_bool exprExcessUB_nat exprExcessUB_none exprExcessUB_nil
  exprExcessUB_add exprExcessUB_sub exprExcessUB_mulK exprExcessUB_divK exprExcessUB_modK
  exprExcessUB_lt exprExcessUB_eqN exprExcessUB_not exprExcessUB_and exprExcessUB_ite
  exprExcessUB_pair exprExcessUB_fst exprExcessUB_snd exprExcessUB_inl exprExcessUB_inr
  exprExcessUB_some exprExcessUB_caseOpt exprExcessUB_caseSum exprExcessUB_letE
  exprExcessUB_op exprExcessUB_cons exprExcessUB_len exprExcessUB_take
  exprExcessUB_appendL exprExcessUB_findB exprExcessUB_anyB exprExcessUB_mapB
  exprExcessUB_foldrB exprExcessUB_tconst exprExcessUB_tget exprExcessUB_tset)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound bits_le_add_one
  add_mul_le_ratchetCostBudget_atomic compCostW_le_of_parts
  implEC_compCostW_le_fig8AtomicStepBound
  redCKAAuthProg_parts_le redCKAPrivProg_parts_le redPRNGAuthProg_parts_le
  redPRNGPrivProg_parts_le redFSAuthProg_parts_le redFSPrivProg_parts_le
  redFSPrivCoinProg_parts_le)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW compCostW compilePureAuxRed
  compilePureAuxRed_totalCost_le compilePureAuxRed_totalQueries_le)
open Computational.Proofs.ReductionDsl.MacroLift (toVal dummyRed guardRed guardRed_gRedBounded)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (HooksSizeBounded
  bits_B0_le_ratchetCostBudget bits_le_ratchetCostBudget_of_le_linear
  bits_qep_le_ratchetCostBudget bits_zero bits_one bits_two bits_three bits_four
  optNatLit_sizeW vSendC_sizeW_le vRecvC_sizeW_le commitEC_sizeW_le cInTransitE_sizeW_le
  compSizeW_bind compSizeW_ite compSizeW_ret compSizeW_sample
  compSizeW_caseOpt compSizeW_caseSum compSizeW_query
  exprSizeW_v0 exprSizeW_v1 exprSizeW_v2 exprSizeW_v3 exprSizeW_v4
  exprSizeW_v5 exprSizeW_v6 exprSizeW_v7 exprSizeW_var
  exprSizeW_unit exprSizeW_bool exprSizeW_nat exprSizeW_none exprSizeW_nil
  exprSizeW_add exprSizeW_sub exprSizeW_mulK exprSizeW_divK exprSizeW_modK
  exprSizeW_lt exprSizeW_eqN exprSizeW_not exprSizeW_and exprSizeW_ite
  exprSizeW_pair exprSizeW_fst exprSizeW_snd exprSizeW_inl exprSizeW_inr
  exprSizeW_some exprSizeW_caseOpt exprSizeW_caseSum exprSizeW_letE
  exprSizeW_op exprSizeW_cons exprSizeW_len exprSizeW_take
  exprSizeW_appendL exprSizeW_findB exprSizeW_anyB exprSizeW_mapB
  exprSizeW_foldrB exprSizeW_tconst exprSizeW_tget exprSizeW_tset
  hooksCKAC_sizeBounded hooksFSC_sizeBounded hooksPRNGC_sizeBounded implEC_sizeW_le
  initCKAEStateC_sizeW_le initFSEStateC_sizeW_le initPRNGEStateC_sizeW_le privOutC_sizeW_le
  pureEngineExprs_sizeW_le size_le_ratchetSizeBudget thm1_simHandleC_sizeW_le
  thm1_simInitC_sizeW_le)

/-! ## Arithmetic and cost helpers -/

private theorem pureRetRed_isQueryBoundP
    {S : Sig} {O : Ops S} {ι κ : Type} {T₀ : OracleSpec.{0, 0} ι}
    {I : Iface S (unifSpec + T₀)}
    {G : OracleSpec.{0, 0} κ} {C : _root_.ReductionDsl.GameCodec S G}
    {rIn aIn aOut out σ : Ty S}
    (initE : Expr O [rIn] (.prod aIn σ))
    (handleE : Expr O [σ, C.Q] (.prod C.R σ))
    (finishE : Expr O [σ, aOut] out)
    {P : (unifSpec + T₀).Domain → Prop} [DecidablePred P]
    (hFwdU : ∀ n, I.fwdU n = liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)))
    (hP : ∀ n, ¬ P (.inl n))
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) (k : ℕ) :
    (({ σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE } :
        CostedReduction O I G C rIn aIn aOut out).eval A x).IsQueryBoundP P k := by
  let R : CostedReduction O I G C rIn aIn aOut out :=
    { σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE }
  suffices hSim : ∀ (oa : OracleComp (unifSpec + G) aOut.denote) (s : σ.denote),
      (((simulateQ R.impl oa).run s) >>= fun bs =>
        pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))).IsQueryBoundP P k by
    change (R.eval A x).IsQueryBoundP P k
    unfold CostedReduction.eval
    simp only [R, Comp.eval, pure_bind]
    exact hSim (A (initE.eval (.cons x .nil)).1) (initE.eval (.cons x .nil)).2
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure b =>
    intro s
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s
    rcases q with n | t
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)) >>= fun u =>
            (((simulateQ R.impl (mx u)).run s) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl,
          StateT.run_bind, StateT.run_lift, hFwdU, map_eq_bind_pure_comp, bind_assoc]
      rw [hStep, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (hP n), fun u => by simpa [hP n] using ih u s⟩
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          (((simulateQ R.impl
              (mx (C.rdec t (handleE.eval (.cons s (.cons (C.qenc t) .nil))).1))).run
            (handleE.eval (.cons s (.cons (C.qenc t) .nil))).2) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl, Comp.eval,
          StateT.run_bind, StateT.run_mk, pure_bind]
      rw [hStep]
      exact ih _ _


/-! ## Secure-messaging reductions -/

section SMParts

variable {Key St St₂ Msg Coins RCoins C : Type}
  {init : Party → Key → Option St} {send : St → Msg → Coins → Option (St × C)}
  {receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)}
  {eqMsg : Msg → Msg → Bool} {eqCt : C → C → Bool} {blank : Msg → Msg}
  {injOK : C → Bool} {stOK : Party → St → Bool} {φ : St → Option St₂}
  {stSort : CryptoGames.SM.SMSort}
  {sampKey : ProbComp (Option Key)} {sampCoins : ProbComp (Option Coins)}
  {sampRCoins : ProbComp (Option RCoins)}

theorem challSimProg_parts_le (q qep : ℕ) :
    let P := CryptoGames.SM.challSimProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep
    compCostW smOpC smSampC smQueryC P.init + compCostW smOpC smSampC smQueryC P.finish +
        100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro P
  have hi : compCostW smOpC smSampC smQueryC P.init ≤ 700 := by
    dsimp only [P, CryptoGames.SM.challSimProg]
    exact compCostW_le_of_parts thm1_simInitC_cost_le thm1_simInitC_excessUB_le (by omega)
  have hf : compCostW smOpC smSampC smQueryC P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.challSimProg]
    exact compCostW_le_of_parts (a := 10) (b := 0)
      (by simp only [Comp.cost, v1_cost]; decide)
      (by simp only [compExcessUB_ret, exprExcessUB_v1]; decide) (by omega)
  have hh : compCostW smOpC smSampC smQueryC P.handle ≤
      20 * bits qep + 2000 * q + 1017030 := by
    dsimp only [P, CryptoGames.SM.challSimProg]
    have hb0 : bits 0 = 1 := rfl
    refine compCostW_le_of_parts (thm1_simHandleC_cost_le q qep none)
      (thm1_simHandleC_excessUB_le q qep none) ?_
    simp only [Option.getD_none, hb0]
    omega
  refine ⟨(Nat.add_le_add_right (Nat.add_le_add hi hf) 100000).trans
    (const_le_fig8AtomicStepBound (by decide)), ?_⟩
  refine (Nat.add_le_add_right hh 200000).trans ?_
  refine (le_of_eq ?_).trans (linear_le_fig8AtomicStepBound (k := 20) (a := 2000)
    (b := 1215030) (q := q) (qep := qep) (by decide) (by decide) (by decide))
  ring

theorem privRedBProg_parts_le (q qep i : ℕ) (hi_ep : i < qep + 2) :
    let P := CryptoGames.SM.privRedBProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep i
    compCostW smOpC smSampC smQueryC P.init + compCostW smOpC smSampC smQueryC P.finish +
        100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro P
  have hi : compCostW smOpC smSampC smQueryC P.init ≤ 700 := by
    dsimp only [P, CryptoGames.SM.privRedBProg]
    exact compCostW_le_of_parts thm1_simInitC_cost_le thm1_simInitC_excessUB_le (by omega)
  have hf : compCostW smOpC smSampC smQueryC P.finish ≤ 50 := by
    dsimp only [P, CryptoGames.SM.privRedBProg]
    exact compCostW_le_of_parts (a := 30) (b := 0)
      (by simp only [CryptoGames.SM.boolEq, CryptoGames.SM.mB, Comp.cost, Expr.cost, v0_cost,
        v1_cost, Nat.reduceAdd]; decide)
      (by simp only [CryptoGames.SM.boolEq, CryptoGames.SM.mB, compExcessUB_ret, exprExcessUB_ite,
        exprExcessUB_not, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v1,
        Nat.reduceAdd]; decide)
      (by omega)
  have hh : compCostW smOpC smSampC smQueryC P.handle ≤
      25 * bits qep + 2000 * q + 1017050 := by
    dsimp only [P, CryptoGames.SM.privRedBProg]
    have hbi := bits_le_bits_qep_add (x := i) (qep := qep) (by omega)
    refine compCostW_le_of_parts (thm1_simHandleC_cost_le q qep (some i))
      (thm1_simHandleC_excessUB_le q qep (some i)) ?_
    simp only [Option.getD_some]
    omega
  refine ⟨(Nat.add_le_add_right (Nat.add_le_add hi hf) 100000).trans
    (const_le_fig8AtomicStepBound (by decide)), ?_⟩
  refine (Nat.add_le_add_right hh 200000).trans ?_
  refine (le_of_eq ?_).trans (linear_le_fig8AtomicStepBound (k := 25) (a := 2000)
    (b := 1215050) (q := q) (qep := qep) (by decide) (by decide) (by decide))
  ring

set_option maxRecDepth 100000 in
theorem challSimProg_size_le (q qep : ℕ) (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.challSimProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep
    Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro P
  have hi : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init ≤ 1000 :=
    thm1_simInitC_sizeW_le
  have hh : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle ≤
      50 * bits q + 30 * bits qep + 20010 := by
    have h0 := thm1_simHandleC_sizeW_le (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q qep none
    simp only [Option.getD_none, bits_zero] at h0
    dsimp only [P, CryptoGames.SM.challSimProg]
    omega
  have hf : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.challSimProg]
    simp only [compSizeW_ret, exprSizeW_v1, Nat.reduceAdd]; omega
  have hbq : bits q ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  refine size_le_ratchetSizeBudget (C₀ := 25000) (C₁ := 80) (by decide) (by decide) ?_
  omega

set_option maxRecDepth 100000 in
theorem privRedBProg_size_le (q qep i : ℕ) (hi_ep : i < qep + 2)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.privRedBProg (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q 3 qep i
    Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro P
  have hi : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.init ≤ 1000 :=
    thm1_simInitC_sizeW_le
  have hh : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.handle ≤
      50 * bits q + 30 * bits qep + 10 * bits i + 20000 := by
    have h0 := thm1_simHandleC_sizeW_le (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins) q qep (some i)
    simp only [Option.getD_some] at h0
    dsimp only [P, CryptoGames.SM.privRedBProg]
    omega
  have hf : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS P.finish ≤ 50 := by
    dsimp only [P, CryptoGames.SM.privRedBProg]
    simp only [CryptoGames.SM.boolEq, CryptoGames.SM.mB, compSizeW_ret, exprSizeW_ite,
      exprSizeW_not, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd]
    omega
  have hbq : bits q ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbi : bits i ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  refine size_le_ratchetSizeBudget (C₀ := 25000) (C₁ := 90) (by decide) (by decide) ?_
  omega

end SMParts

section SMWrapper

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : CryptoGames.LibsignalSession.Crypto) (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
  (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)

set_option maxRecDepth 100000 in
theorem compileSmAtomic_gRedBounded
    (R : CostedReduction (Bundles.fig8SmOpsShallow ℓ Pt)
      (CryptoGames.SM.smIface Unit (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt) Unit
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) Unit (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.SM.smCodec Unit (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt) Unit
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) Unit (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW smOpC smSampC smQueryC R.init + compCostW smOpC smSampC smQueryC R.finish +
        100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW smOpC smSampC smQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.init +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.handle +
      Bundles.compSizeW Bundles.smOpS Bundles.smSampS Bundles.smQueryS R.finish + 400 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileSmAtomic ℓ Pt C Dh encPt encT idOf lam R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileSmAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R smOpC smSampC smQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · intro o
      have h1 := Computational.Proofs.ReductionDsl.Fig8Atomic.eqMExpr_cost ℓ Pt C Dh encPt encT lam
      have h2 := Computational.Proofs.ReductionDsl.Fig8Atomic.smEqCtExpr_cost ℓ Pt C Dh encPt encT lam
      have h3 := Computational.Proofs.ReductionDsl.Fig8Atomic.smBlankExpr_cost ℓ Pt C Dh encPt encT lam
      cases o <;> simp only [Bundles.smPureAuxBundle, Bundles.smOpMacro, smOpC, Expr.cost] <;> omega
    · intro s
      cases s <;> simp [Bundles.smPureAuxBundle, Bundles.smSampMacro, smSampC, Comp.cost, Expr.cost]
    · intro g
      cases g <;> simp [smQueryC, Comp.cost, Expr.cost] <;> omega
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
      simp only [Expr.cost]
      omega
    · simp
    · have h1 := Bundles.fig8AdaptQ_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptR_cost ℓ Pt C Dh encPt encT lam
      simp
      omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R Bundles.smOpS Bundles.smSampS Bundles.smQueryS
      (Bundles.smOpMacro_size_le ℓ Pt C Dh encPt encT lam) ?_ ?_).trans ?_
    · intro s
      cases s <;> simp [Bundles.smPureAuxBundle, Bundles.smSampMacro, Bundles.smSampS, Comp.size,
        Expr.size]
    · intro g
      cases g <;> simp [Bundles.smQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQ_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptR_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]
      omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s
      cases s <;> simp [Bundles.smPureAuxBundle, Bundles.smSampMacro, Comp.queries]
    · intro g
      cases g <;> simp [Comp.queries]

end SMWrapper

section SMInstance

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem fig8RedsInst_challSim_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).challSim
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileSmAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ q qep q
    (challSimProg_parts_le q qep) (challSimProg_size_le q qep hqep)
    (by rw [CryptoGames.SM.challSimProg_totalQueries])

theorem fig8RedsInst_privRedB_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1) (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).privRedB i)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileSmAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ q qep q
    (privRedBProg_parts_le q qep i (by omega)) (privRedBProg_size_le q qep i (by omega) hqep)
    (by rw [CryptoGames.SM.privRedBProg_totalQueries])

end SMInstance


/-! ## Compiled CKA, PRNG, and FS-AEAD reductions -/

section CkaWrapper

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : CryptoGames.LibsignalSession.Crypto) (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
  (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)

set_option maxRecDepth 100000 in
theorem compileCkaAtomic_gRedBounded (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.CKA.ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC ckaQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC ckaQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC ckaQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 400 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileCkaAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileCkaAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC ckaQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · exact ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0
    · intro s
      cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, ckaSampC, Comp.cost,
        Expr.cost, AtomicUnifBase.cost]
    · intro g
      cases g <;> simp [ckaQueryC, Comp.cost, Expr.cost]
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
      simp only [Expr.cost]
      omega
    · simp
    · have h1 := Bundles.fig8AdaptQ_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptR_cost ℓ Pt C Dh encPt encT lam
      simp
      omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s
      cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, Bundles.ckaSampS,
        Comp.size, Expr.size]
    · intro g
      cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQ_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptR_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]
      omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s
      cases s <;> simp [Bundles.ckaPureAuxBundle, Bundles.ckaSampMacro, Comp.queries]
    · intro g
      cases g <;> simp [Comp.queries]

set_option maxRecDepth 100000 in
theorem compilePrngAtomic_gRedBounded (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC prngQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC prngQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC prngQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 400 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compilePrngAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compilePrngAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC prngQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · exact ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0
    · intro s
      cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, ckaSampC, Comp.cost,
        Expr.cost, AtomicUnifBase.cost]
    · intro g
      cases g <;> simp [prngQueryC, Comp.cost, Expr.cost]
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
      simp only [Expr.cost]
      omega
    · simp
    · have h1 := Bundles.fig8AdaptQ_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptR_cost ℓ Pt C Dh encPt encT lam
      simp
      omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s
      cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, Bundles.ckaSampS,
        Comp.size, Expr.size]
    · intro g
      cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQ_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptR_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]
      omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s
      cases s <;> simp [Bundles.prngPureAuxBundle, Bundles.prngSampMacro, Comp.queries]
    · intro g
      cases g <;> simp [Comp.queries]


set_option maxRecDepth 100000 in
theorem compileFsAtomic_gRedBounded (B0 : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (q qep qOut : ℕ)
    (hparts : compCostW (ckaOpC B0) ckaSampC fsQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC fsQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC fsQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep)
    (hSize : Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS R.finish + 400 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRedBounded (Bundles.compileFsAtomic ℓ Pt C Dh encPt encT idOf lam B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  unfold Bundles.compileFsAtomic
  refine guardRed_gRedBounded _ _ _ _ _ _ q qOut _ (fun hℓ => ?_) ?_ (fun _ => ?_) ?_ (fun _ => ?_)
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · refine (compilePureAuxRed_totalCost_le _ _ R (ckaOpC B0) ckaSampC fsQueryC ?_ ?_ ?_ q).trans
      (compiled_le_ratchetCostBudget hparts.1 hparts.2 ?_ ?_ ?_)
    · exact ckaOpMacro_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ B0
    · intro s
      cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, ckaSampC, Comp.cost,
        Expr.cost, AtomicUnifBase.cost]
    · intro g
      cases g <;> simp [fsQueryC, Comp.cost, Expr.cost] <;> omega
    · have := Bundles.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
      simp only [Expr.cost]
      omega
    · simp
    · have h1 := Bundles.fig8AdaptQ_cost ℓ Pt C Dh encPt encT lam
      have h2 := Bundles.fig8AdaptR_cost ℓ Pt C Dh encPt encT lam
      simp
      omega
  · exact dummy_le_ratchetCostBudget (by simp [Expr.cost]) (by simp [Expr.cost])
  · refine (Bundles.compilePureAuxRed_size_le _ _ R (Bundles.ckaOpS B0) Bundles.ckaSampS
      Bundles.ckaQueryS (Bundles.ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0) ?_ ?_).trans ?_
    · intro s
      cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, Bundles.ckaSampS,
        Comp.size, Expr.size]
    · intro g
      cases g <;> simp [Bundles.ckaQueryS, Comp.size, Expr.size]
    · have hs := Bundles.fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
      have hq := Bundles.fig8AdaptQ_size ℓ Pt C Dh encPt encT lam
      have hr := Bundles.fig8AdaptR_size ℓ Pt C Dh encPt encT lam
      simp only [Expr.size]
      omega
  · simp [Expr.size, reductionSizeBudget]
  · refine (compilePureAuxRed_totalQueries_le _ _ R _ _ _ _ ?_ ?_ q).trans hQ
    · intro s
      cases s <;> simp [Bundles.fsPureAuxBundle, Bundles.fsSampMacro, Comp.queries]
    · intro g
      cases g <;> simp [Comp.queries]


private theorem liftP_congr {ι : Type} {T : OracleSpec.{0, 0} ι} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' T) (I₁ : Iface S₁' T) (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    {α : Type} (p : ProbComp α) : I₂.liftP p = I₁.liftP p := by
  unfold Iface.liftP
  rw [funext hFwdU]

private theorem ckaPureAuxBundle_samp_querySubsumes (B0 : ℕ) (s : CryptoGames.CKA.CKASamp)
    (z : ((CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    QuerySubsumes
      (((Bundles.ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt) _ z)
          (.cons (idOf .A, idOf .B) .nil)))
      (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt)
        ((CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
            (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
            (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
            (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply QuerySubsumes.of_eq
    exact (liftP_congr (ckaTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    exact
      Bundles.querySubsumes_liftP_of_support_subset (ckaTargetIface ℓ Pt)
        (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp)

private theorem prngPureAuxBundle_samp_querySubsumes (B0 : ℕ) (s : CryptoGames.CKA.CKASamp)
    (z : ((CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    QuerySubsumes
      (((Bundles.prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt) _ z)
          (.cons (idOf .A, idOf .B) .nil)))
      (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt)
        ((CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
            (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
            (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
            (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply QuerySubsumes.of_eq
    exact (liftP_congr (prngTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    exact
      Bundles.querySubsumes_liftP_of_support_subset (prngTargetIface ℓ Pt)
        (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
          (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp)

private theorem compileCkaAtomic_makesAtMostQueries [Inhabited Pt] (B0 qOut : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.CKA.ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hR : (R.eval (fun _ => A) ()).IsQueryBoundP (· matches .inr _) qOut) :
    CryptoGames.CKA.MakesAtMostQueries
      ((Bundles.compileCkaAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut := by
  unfold Bundles.compileCkaAtomic guardRed
  split_ifs with hℓ
  · have hsub := QuerySubsumes.compilePureAuxRed_querySubsumes
      (Bundles.ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (Bundles.ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
      R (Bundles.toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
      (Bundles.fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
      (Bundles.ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
      (ckaPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam B0)
      (fun g z => .of_eq (Bundles.ckaPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
      (fun _ => rfl) (fun _ => rfl)
      (Bundles.fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
      (Bundles.fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
      (fun _ => A) (fun _ => A) id
      (fun _ => .of_eq (id_map A).symm)
      (fun _ => rfl)
      (outEq := id) (fun _ => rfl)
    rw [id_map] at hsub
    exact hsub.isQueryBoundP (fun _ => nofun)
      (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | _) <;> rfl) hR)
  · unfold dummyRed
    apply pureRetRed_isQueryBoundP
    · intro; rfl
    · intro _ h; nomatch h

private theorem compilePrngAtomic_makesAtMostQueries [Inhabited Pt] (B0 qOut : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hR : (R.eval (fun _ => A) ()).IsQueryBoundP (· matches .inr _) qOut) :
    CryptoGames.PRFPRNG.MakesAtMostQueries
      ((Bundles.compilePrngAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut := by
  unfold Bundles.compilePrngAtomic guardRed
  split_ifs with hℓ
  · have hsub := QuerySubsumes.compilePureAuxRed_querySubsumes
      (Bundles.prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (Bundles.ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
      R (Bundles.toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
      (Bundles.fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
      (Bundles.ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
      (prngPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam B0)
      (fun g z => .of_eq (Bundles.prngPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
      (fun _ => rfl) (fun _ => rfl)
      (Bundles.fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
      (Bundles.fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
      (fun _ => A) (fun _ => A) id
      (fun _ => .of_eq (id_map A).symm)
      (fun _ => rfl)
      (outEq := id) (fun _ => rfl)
    rw [id_map] at hsub
    exact hsub.isQueryBoundP (fun _ => nofun)
      (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | _) <;> rfl) hR)
  · unfold dummyRed
    apply pureRetRed_isQueryBoundP
    · intro; rfl
    · intro _ h; nomatch h

private theorem compileFsAtomic_makesAtMostQueries [Inhabited Pt] (B0 qOut : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
      (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt)) Bool)
    (hR : CryptoGames.FSAEAD.MakesAtMostQueries (R.eval (fun _ => A) ()) qOut) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((Bundles.compileFsAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut := by
  unfold Bundles.compileFsAtomic guardRed
  split_ifs with hℓ
  · have hsub := QuerySubsumes.compilePureAuxRed_querySubsumes
      (Bundles.fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (Bundles.ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
      R (Bundles.toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
      (Bundles.fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
      (Bundles.ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
      (Bundles.fsPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam B0)
      (fun g z => .of_eq (Bundles.fsPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
      (fun _ => rfl) (fun _ => rfl)
      (Bundles.fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
      (Bundles.fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
      (fun _ => A) (fun _ => A) id
      (fun _ => .of_eq (id_map A).symm)
      (fun _ => rfl)
      (outEq := id) (fun _ => rfl)
    rw [id_map] at hsub
    exact hsub.isQueryBoundP (fun _ => nofun)
      (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | _) <;> rfl) hR)
  · unfold dummyRed
    apply pureRetRed_isQueryBoundP
    · intro; rfl
    · intro _ h; nomatch h


end CkaWrapper

/-! ## Size bounds and `fig8CostedBounds` instance -/

section EngineSizeParts

open _root_.CryptoGames.SM.Construction (Header healEpoch)
open _root_.CryptoGames.LibsignalSession (maxForwardJumps)

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS} {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_cka" => CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

private theorem bind_ret_pair_unit_sizeW_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {opS : O'.Op → ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {σ : Ty S'} {c : Comp O' I' Γ' σ} {K M : ℕ}
    (hc : Bundles.compSizeW opS sS qS c ≤ K) (hM : K + 5 ≤ M) :
    Bundles.compSizeW opS sS qS (Comp.bind c (Comp.ret (.pair .unit .v0))) ≤ M := by
  simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit, exprSizeW_v0]; omega

private theorem samp_bind_ret_pair_unit_sizeW_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {opS : O'.Op → ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {s : I'.smp.Samp} {u : Expr O' Γ' (I'.smp.sDom s)}
    {σ : Ty S'} {c : Comp O' I' ((I'.smp.sTy s) :: Γ') σ} {K M : ℕ}
    (hc : Bundles.compSizeW opS sS qS c ≤ K)
    (hM : Bundles.exprSizeW opS u + sS s + K + 6 ≤ M) :
    Bundles.compSizeW opS sS qS
      (Comp.bind (Comp.sample s u) (Comp.bind c (Comp.ret (.pair .unit .v0)))) ≤ M := by
  simp only [compSizeW_bind, compSizeW_sample, compSizeW_ret, exprSizeW_pair, exprSizeW_unit,
    exprSizeW_v0]; omega

private theorem authOut_ret_sizeW_le {O' : Ops S_cka} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S_cka TSpec} {vpT hsT : Ty S_cka}
    (opS : O'.Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (q qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hqep : qep ≤ 4096 * q + 100000000) :
    Bundles.compSizeW opS sS qS
      (Comp.ret (I := I') (Γ := [CryptoGames.SM.Engine.esTy vpT hsT, .bool])
        (CryptoGames.SM.Engine.authOutE (q + 1) (2 + 1) mo.policy .v0)) ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  have h0 := (pureEngineExprs_sizeW_le opS (q + 1) mo.policy
    (Γ' := [CryptoGames.SM.Engine.esTy vpT hsT, .bool]) .v0).1
  have hpolL : mo.policy.tL = mo.tL := rfl
  have hpolS : mo.policy.tStar = mo.tStar := rfl
  rw [hpolL, hpolS] at h0; simp only [exprSizeW_v0] at h0
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtS : bits mo.tStar ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (mo.tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  simp only [compSizeW_ret]; omega

theorem implEC_sizeW_le_ratchet {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (q qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hqep : qep ≤ 4096 * q + 100000000)
    (hhk : HooksSizeBounded ((q + 1) * (maxForwardJumps + 1)) sS qS hk
      (80 * bits (ratchetCostBudget q qep) + 15000) 2000
      (14 * bits (ratchetCostBudget q qep) + 5000)) :
    Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      sS qS
      (CryptoGames.SM.Engine.implEC
        (Γ' := [CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
          CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
        hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1) ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  have h0 := implEC_sizeW_le hk
    (80 * bits (ratchetCostBudget q qep) + 15000) 2000 (14 * bits (ratchetCostBudget q qep) + 5000)
    (q + 1) qep maxForwardJumps mo hhk
    (Γ' := [CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [exprSizeW_v0, exprSizeW_v1] at h0
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbm : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hbtS : bits mo.tStar ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (mo.tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  omega

theorem redCKAAuthProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤ 10000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthProg]
    refine bind_ret_pair_unit_sizeW_le (initCKAEStateC_sizeW_le B mo (.bool false)) ?_
    simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksCKAC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 :=
    authOut_ret_sizeW_le _ _ _ q qep mo ht htL1 hqep
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redCKAPrivProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, t⟩
  let II := CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤ 10000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAPrivProg]
    refine samp_bind_ret_pair_unit_sizeW_le (initCKAEStateC_sizeW_le B mo .v0) ?_
    simp only [Bundles.ckaSampS, exprSizeW_unit, exprSizeW_v0]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAPrivProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksCKAC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAPrivProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
    refine (privOutC_sizeW_le (O' := OO_cka) (I' := II)
      (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS (q + 1) mo.policy
      (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CryptoGames.CKA.CKASamp.bit .unit)
      (Γ' := [CryptoGames.SM.Construction.ckaEsTy, .bool])
      (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG .v0)) .v1 .v0).trans ?_
    have hpolL : mo.policy.tL = tL := rfl; have hpolS : mo.policy.tStar = t := rfl
    rw [hpolL, hpolS]
    simp only [CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.esG, Bundles.ckaSampS,
      compSizeW_sample, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_unit,
      Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redPRNGAuthProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      10 * bits (ratchetCostBudget q qep) + 7000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthProg]
    refine bind_ret_pair_unit_sizeW_le (initPRNGEStateC_sizeW_le B mo (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksPRNGC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 :=
    authOut_ret_sizeW_le _ _ _ q qep mo ht htL1 hqep
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redPRNGPrivProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, t⟩
  let II := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      10 * bits (ratchetCostBudget q qep) + 7000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGPrivProg]
    refine samp_bind_ret_pair_unit_sizeW_le (initPRNGEStateC_sizeW_le B mo .v0) ?_
    have hmS : mo.tStar = t := rfl
    rw [hmS]; simp only [Bundles.ckaSampS, exprSizeW_unit, exprSizeW_v0]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGPrivProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksPRNGC_sizeBounded B B mo).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redPRNGPrivProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
    refine (privOutC_sizeW_le (O' := OO_cka) (I' := II)
      (vpT := @CryptoGames.SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS (q + 1) mo.policy
      (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CryptoGames.CKA.CKASamp.bit .unit)
      (Γ' := [CryptoGames.SM.Construction.prngEsTy, .bool])
      (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG .v0)) .v1 .v0).trans ?_
    have hpolL : mo.policy.tL = tL := rfl; have hpolS : mo.policy.tStar = t := rfl
    rw [hpolL, hpolS]
    simp only [CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.esG, Bundles.ckaSampS,
      compSizeW_sample, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_unit,
      Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redFSAuthProg_size_le (q qep j t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t) (hj : j < q)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps j tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbj : bits j ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo j (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksFSC_sizeBounded B (q + 1) B mo j).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSAuthProg]
    simp only [Bundles.ckaSampS, compSizeW_sample, exprSizeW_unit, Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redFSPrivProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, t⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hb0 : bits 0 ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo 0 (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksFSC_sizeBounded B (q + 1) B mo 0).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
    have hpv := (pureEngineExprs_sizeW_le (O' := OO_cka) (Bundles.ckaOpS B)
      (vpT := @CryptoGames.SM.Construction.fsVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.fsHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (q + 1) mo.policy
      (Γ' := [CryptoGames.SM.Construction.fsEsTy KC Γ CCoins T I KR RSt K SS RS M E, .bool]) .v0).2
    have hpolL : mo.policy.tL = tL := rfl; have hpolS : mo.policy.tStar = t := rfl
    rw [hpolL, hpolS] at hpv; dsimp only [mo] at hpv; simp only [exprSizeW_v0] at hpv
    simp only [Bundles.ckaSampS, compSizeW_ite, compSizeW_ret, compSizeW_sample, exprSizeW_v1,
      exprSizeW_unit, Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

theorem redFSPrivCoinProg_size_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) t)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSPrivCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL t
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, t⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hb0 : bits 0 ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivCoinProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo 0 (.bool false)) ?_
    have hmS : mo.tStar = t := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivCoinProg]
    refine implEC_sizeW_le_ratchet _ q qep mo ht htL1 hqep ?_
    exact (hooksFSC_sizeBounded B (q + 1) B mo 0).mono (by dsimp [mo] at *; omega) le_rfl (by omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivCoinProg]
    simp only [Bundles.ckaSampS, compSizeW_sample, exprSizeW_unit, Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

section Stage2Parts

set_option linter.unusedSimpArgs false

open _root_.ReductionDsl (bits_le_succ)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (compCostUB exprCostUB compCost_le_costUB
  exprCost_le_costUB)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded HooksCostBounded.mono
  hooksCKAC_costBounded hooksPRNGC_costBounded
  initCKAEStateC_cost_le initPRNGEStateC_cost_le privOutC_cost_le authOutE_cost_le implEC_cost_le
  cGsB_cost esG_cost esH_cost fig8StepBound)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (HooksExcessBounded HooksExcessBounded.mono
  exprExcessUB hooksCKAC_excessBounded hooksPRNGC_excessBounded
  initCKAEStateC_excessUB_le initPRNGEStateC_excessUB_le privOutC_excessUB_le
  pureEngineExprs_excessUB implEC_excessUB_le
  exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4 exprExcessUB_v5 exprExcessUB_v6 exprExcessUB_v7
  exprExcessUB_var exprExcessUB_unit exprExcessUB_bool exprExcessUB_nat exprExcessUB_modK exprExcessUB_lt
  exprExcessUB_eqN exprExcessUB_and exprExcessUB_pair exprExcessUB_inl exprExcessUB_inr
  exprExcessUB_none exprExcessUB_some exprExcessUB_caseOpt exprExcessUB_caseSum
  exprExcessUB_letE exprExcessUB_op exprExcessUB_tconst exprExcessUB_tget exprExcessUB_tset
  compExcessUB_bind compExcessUB_ite compExcessUB_caseOpt compExcessUB_caseSum
  compExcessUB_sample compExcessUB_query)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (implEC_compCostW_le_fig8AtomicStepBound)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (bits_one exprSizeW_v2 exprSizeW_v3
  exprSizeW_v4 exprSizeW_v5 exprSizeW_v6 exprSizeW_v7 exprSizeW_var exprSizeW_nat exprSizeW_modK exprSizeW_lt
  exprSizeW_eqN exprSizeW_and exprSizeW_inl exprSizeW_inr exprSizeW_none exprSizeW_some
  exprSizeW_caseOpt exprSizeW_caseSum exprSizeW_letE exprSizeW_op exprSizeW_tconst exprSizeW_tget exprSizeW_tset
  compSizeW_caseOpt compSizeW_caseSum compSizeW_query)

private theorem cost_bind_ret_le_costUB {S' : Sig} {O' : Ops S'} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S' TSpec} {Γ' : List (Ty S')} {t u : Ty S'}
    (e : Expr O' Γ' t) (k : Comp O' I' (t :: Γ') u) :
    (Comp.bind (.ret e) k).cost ≤ e.cost + compCostUB k + 2 := by
  have hk := compCost_le_costUB k; simp only [Comp.cost]; omega

private theorem ret_pair_letE_cost_le_costUB {S' : Sig} {O' : Ops S'} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S' TSpec} {Γ' : List (Ty S')} {t u v : Ty S'}
    (e : Expr O' Γ' t) (k : Expr O' (t :: Γ') u) (r : Expr O' Γ' v) :
    (Comp.ret (I := I') (.pair (.letE e k) r)).cost ≤ e.cost + r.cost + exprCostUB k + 3 := by
  have hk := exprCost_le_costUB k; simp only [Comp.cost, Expr.cost]; omega

private theorem init_finish_le_step {q qep k1 k2 a1 a2 b1 b2 x y : ℕ}
    (hx : x ≤ k1 * bits qep + a1 * (q + 1) + b1) (hy : y ≤ k2 * bits qep + a2 * (q + 1) + b2)
    (hk : k1 + k2 ≤ 200) (ha : a1 + a2 ≤ 15000) (hb : b1 + b2 + 100000 ≤ 25000000) :
    x + y + 100000 ≤ fig8AtomicStepBound q qep :=
  (Nat.add_le_add (Nat.add_le_add hx hy) le_rfl).trans <|
    (le_of_eq (by ring)).trans (linear_le_fig8AtomicStepBound hk ha hb)

private theorem hooksCKAUC_costBounded (B : ℕ) (mo : CryptoGames.SM.Construction.Mode) :
    HooksCostBounded
      (CryptoGames.SM.Construction.hooksCKAUC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 mo)
      (3 * bits mo.tH + 3 * bits mo.tStar + (B + 1) + 1200) where
  startSend_le h ctx p t γv σ r := by
    have htH1 := bits_succ_le mo.tH
    dsimp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.SM.Construction.ckaStartSendUC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [CryptoGames.SM.leN, CryptoGames.CKA.ckaIface, CryptoGames.CKA.ckaSamplers,
      CryptoGames.CKA.ckaOps, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
      dsl_cost, Nat.reduceAdd]; omega
  startRecv_le h ctx p t γv σ tn := by
    dsimp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.SM.Construction.ckaStartRecvUAnsE]
    refine (ret_pair_letE_cost_le_costUB _ _ _).trans ?_
    simp only [CryptoGames.CKA.ckaOps, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
      dsl_cost, Nat.reduceAdd]; omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost]; omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    have hB := bits_le_succ B
    simp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost]; omega
  commit_le h ctx p old new := by
    have htH1 := bits_succ_le mo.tH
    dsimp only [CryptoGames.SM.Construction.hooksCKAUC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [CryptoGames.SM.isSomeE, CryptoGames.SM.leN, CryptoGames.SM.Engine.vpSetΓ,
      CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot,
      CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpΓ,
      CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat, CryptoGames.CKA.ckaIface,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, dsl_cost,
      Nat.reduceAdd]; omega
  reveal_le h ctx p vp := by
    dsimp only [CryptoGames.SM.Construction.hooksCKAUC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk,
      CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS,
      CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur,
      CryptoGames.SM.Engine.vpTcurNat, CryptoGames.CKA.ckaIface,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, dsl_cost, Nat.reduceAdd]; omega

private theorem hooksCKAUC_excessBounded (B0 B : ℕ) (mo : CryptoGames.SM.Construction.Mode) :
    HooksExcessBounded B0 ckaSampC ckaQueryC
      (CryptoGames.SM.Construction.hooksCKAUC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 mo)
      3000 380000 (20 * B0 + 3 * bits B + 2710000) where
  startSend_le h ctx p t γv σ r := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.SM.Construction.ckaStartSendUC,
      CryptoGames.SM.leN, ckaOpC, ckaSampC, ckaQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_sample, compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]; omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC,
      CryptoGames.SM.Construction.ckaStartRecvUAnsE, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_eqN, exprExcessUB_and,
      exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tget,
      compExcessUB_ret, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]; omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]; omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]; omega
  commit_le h ctx p old new := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.SM.isSomeE, CryptoGames.SM.leN,
      CryptoGames.SM.Engine.vpSetΓ, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
      CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
      ckaQueryC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add]; omega
  reveal_le h ctx p vp := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.SM.Engine.realPartyE,
      CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot,
      CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpΓ,
      CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat, ckaQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_caseOpt, compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]; omega

private theorem hooksCKAUC_sizeBounded (B0 B : ℕ) (mo : CryptoGames.SM.Construction.Mode) :
    HooksSizeBounded B0 Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.hooksCKAUC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 mo)
      (5 * bits mo.tH + 10 * bits mo.tStar + 6000) 2000 (3 * bits B0 + 2 * bits B + 2000) where
  startSend_le h ctx p t γv σ r := by
    have htH1 := bits_succ_le mo.tH
    simp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.SM.Construction.ckaStartSendUC,
      CryptoGames.SM.leN, Bundles.ckaOpS, Bundles.ckaSampS, Bundles.ckaQueryS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
      exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind,
      compSizeW_ite, compSizeW_caseOpt, compSizeW_sample, compSizeW_query, bits_zero, bits_one,
      Nat.reduceAdd]; omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC,
      CryptoGames.SM.Construction.ckaStartRecvUAnsE, Bundles.ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_eqN, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tget, compSizeW_ret, Nat.reduceAdd]; omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC, Bundles.ckaOpS,
      exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret, Nat.reduceAdd]; omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC, Bundles.ckaOpS,
      exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret, Nat.reduceAdd]; omega
  commit_le h ctx p old new := by
    have htH1 := bits_succ_le mo.tH
    simp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.SM.isSomeE, CryptoGames.SM.leN,
      CryptoGames.SM.Engine.vpSetΓ, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
      CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
      Bundles.ckaQueryS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
      exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, compSizeW_ret, compSizeW_bind,
      compSizeW_ite, compSizeW_caseOpt, compSizeW_query, bits_zero, bits_one, Nat.reduceAdd]; omega
  reveal_le h ctx p vp := by
    simp only [CryptoGames.SM.Construction.hooksCKAUC, CryptoGames.SM.Engine.realPartyE,
      CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot,
      CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpΓ,
      CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat, Bundles.ckaQueryS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_nat,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_letE, compSizeW_ret, compSizeW_bind, compSizeW_caseOpt,
      compSizeW_query, bits_zero, Nat.reduceAdd]; omega

private theorem redCKAPrivUProg_parts_le (q qep i : ℕ) (tL : Option ℕ)
    (hi : i < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAPrivUProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps tL i
    compCostW (ckaOpC B) ckaSampC ckaQueryC P.init +
        compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC ckaQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P; obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, i⟩
  let II := CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
  have ht_bits := bits_le_bits_qep_add (x := i) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhkC := (hooksCKAUC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * bits qep + B + 2500)
    (by dsimp [mo, CryptoGames.SM.Construction.Mode.tH] at *; omega)
  have hhkE := (hooksCKAUC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B B mo).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000) (Hr' := 500 * L + 40 * B + 6 * bits B + 5700000)
    (by omega) (by decide) (by omega)
  have hsmp : II.smp.sCost CryptoGames.CKA.CKASamp.bit = 1 := rfl
  refine ⟨?_, ?_⟩
  · have hiW : compCostW (ckaOpC B) ckaSampC ckaQueryC P.init ≤ 0 * bits qep + 0 * (q + 1) + 2600 := by
      dsimp only [P, CryptoGames.SM.Construction.redCKAPrivUProg]
      have hiC0 := initCKAEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo (Γ' := [.bool, .unit]) .v0
      have hiE0 := initCKAEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo (Γ' := [.bool, .unit]) .v0
      dsimp only [mo] at hiC0 hiE0
      refine compCostW_le_of_parts (a := 560) (b := 1750) ?_ ?_ (by simp)
      · simp only [Comp.cost, Expr.cost, hsmp, CryptoGames.SM.Engine.esG,
          CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, v0_cost] at hiC0 ⊢; omega
      · simp only [compExcessUB_bind, compExcessUB_sample, compExcessUB_ret,
          CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
          exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none,
          exprExcessUB_unit, exprExcessUB_v0, ckaSampC] at hiE0 ⊢; omega
    have hfW : compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish ≤ 5 * bits qep + 100 * (q + 1) + 1000 := by
      dsimp only [P, CryptoGames.SM.Construction.redCKAPrivUProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hfC0 := privOutC_cost_le (O' := OO_cka) (I' := II)
        (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @CryptoGames.SM.Construction.ckaUHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CryptoGames.CKA.CKASamp.bit .unit)
        (Γ' := [CryptoGames.SM.Construction.ckaUEsTy, .bool])
        (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG .v0)) .v1 .v0
      have hfE0 := privOutC_excessUB_le (O' := OO_cka) (I' := II) (ckaOpC B) ckaSampC ckaQueryC
        (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @CryptoGames.SM.Construction.ckaUHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CryptoGames.CKA.CKASamp.bit .unit)
        (Γ' := [CryptoGames.SM.Construction.ckaUEsTy, .bool])
        (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG .v0)) .v1 .v0
      dsimp only [mo] at hfE0
      refine compCostW_le_of_parts
        (a := 2 * (bits (tL.getD 0) + 3) + 2 * bits i + 50 * L + 260) (b := 250)
        ?_ ?_ (by omega)
      · exact hfC0.trans (by
          simp only [cGsB_cost, esG_cost, v0_cost, v1_cost, Comp.cost, Expr.cost, hsmp]
          dsimp only [mo, CryptoGames.SM.Construction.Mode.policy]; omega)
      · exact hfE0.trans (by
          simp only [CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.esG, compExcessUB_sample,
            exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v1,
            exprExcessUB_unit, ckaSampC]; decide)
    exact init_finish_le_step hiW hfW (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, CryptoGames.SM.Construction.redCKAPrivUProg]
    exact implEC_compCostW_le_fig8AtomicStepBound _ q qep mo hi htL1 hhkC hhkE

private theorem redCKAPrivUProg_size_le (q qep i : ℕ) (tL : Option ℕ)
    (hi : i < qep + 2) (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAPrivUProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL i
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P; obtain ⟨htL1, _⟩ := targetsL_bounds htL
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, tL, i⟩
  let II := CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
  have hbi : bits i ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch tL) ≤ _; exact bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hiS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤ 10000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAPrivUProg]
    have h0 := initCKAEStateC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B mo (Γ' := [.bool, .unit]) .v0
    dsimp only [mo] at h0
    simp only [compSizeW_bind, compSizeW_sample, compSizeW_ret, Bundles.ckaSampS,
      CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_unit, exprSizeW_v0] at h0 ⊢
    omega
  have hhS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      800 * bits (ratchetCostBudget q qep) + 200000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAPrivUProg]
    refine implEC_sizeW_le_ratchet _ q qep mo hi htL1 hqep ?_
    exact (hooksCKAUC_sizeBounded B B mo).mono
      (by dsimp [mo, CryptoGames.SM.Construction.Mode.tH] at *; omega) le_rfl (by omega)
  have hfS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAPrivUProg]; rw [show (2 : ℕ) + 1 = 3 from rfl]
    refine (privOutC_sizeW_le (O' := OO_cka) (I' := II)
      (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.ckaUHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS (q + 1) mo.policy
      (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CryptoGames.CKA.CKASamp.bit .unit)
      (Γ' := [CryptoGames.SM.Construction.ckaUEsTy, .bool])
      (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG .v0)) .v1 .v0).trans ?_
    have hpolL : mo.policy.tL = tL := rfl; have hpolS : mo.policy.tStar = i := rfl
    rw [hpolL, hpolS]
    simp only [CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.esG, Bundles.ckaSampS,
      compSizeW_sample, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, exprSizeW_v1, exprSizeW_unit,
      Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 250000) (C₁ := 900) (by decide) (by decide) ?_; omega

private theorem redCKAPrivUProg_totalQueries_le (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (i q : ℕ) :
    (CryptoGames.SM.Construction.redCKAPrivUProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL i).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  simp [CostedReduction.totalQueries, CryptoGames.SM.Construction.redCKAPrivUProg,
    CryptoGames.SM.Construction.initCKAEStateC_queries, CryptoGames.SM.Engine.privOutC,
    CryptoGames.SM.Engine.implEC, CryptoGames.SM.Engine.transmitEC, CryptoGames.SM.Engine.challEC,
    CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Engine.corrEC,
    CryptoGames.SM.Engine.vSendC, CryptoGames.SM.Engine.vSendStep1C,
    CryptoGames.SM.Engine.vRecvC, CryptoGames.SM.Engine.vRecvStep1C,
    CryptoGames.SM.Engine.commitEC, CryptoGames.SM.Construction.hooksCKAUC,
    CryptoGames.SM.Construction.ckaStartSendUC, Comp.queries, Nat.mul_comm]









set_option maxRecDepth 100000 in
private theorem implEC_any_compCostW_le_qep {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka} {Γ' : List (Ty S_cka)}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode)
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (qe : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (hesC : es.cost ≤ 10) (hqeC : qe.cost ≤ 10)
    (hesE : exprExcessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1))) es = 0)
    (hqeE : exprExcessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1))) qe = 0)
    (htStar : mo.tStar < qep + 2)
    (htL : mo.tL.getD 0 < qep + 2)
    (hhkC : HooksCostBounded hk
      (let L := q + 1
       let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * bits qep + B + 2500))
    (hhkE : HooksExcessBounded ((q + 1) * (maxForwardJumps + 1)) ckaSampC qC hk
      (300 * (q + 1) + 250000) 2000000
      (500 * (q + 1) + 40 * ((q + 1) * (maxForwardJumps + 1)) +
        6 * bits ((q + 1) * (maxForwardJumps + 1)) + 5700000)) :
    compCostW (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      (CryptoGames.SM.Engine.implEC hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es qe) + 500000 ≤
      fig8AtomicStepBound q qep := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have htStar_bits := bits_le_bits_qep_add (x := mo.tStar) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := mo.tL.getD 0) (qep := qep) (by omega)
  have hC :
      (CryptoGames.SM.Engine.implEC hk (q + 1) 3 qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es qe).cost ≤
        fig8StepBound q qep + 200 := by
    have himpl := implEC_cost_le hk (320 * L + 10 * bits qep + B + 2500)
      L qep maxForwardJumps mo hhkC es qe
    have hmul : L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) ≤ L * (3 * bits qep + 60) :=
      Nat.mul_le_mul_left L (by omega)
    dsimp only [L, B, fig8StepBound] at himpl hmul ⊢
    omega
  have hE := implEC_excessUB_le hk
    (300 * (q + 1) + 250000) 2000000
    (500 * (q + 1) + 40 * ((q + 1) * (maxForwardJumps + 1)) +
      6 * bits ((q + 1) * (maxForwardJumps + 1)) + 5700000)
    (q + 1) qep maxForwardJumps mo hhkE es qe
  have hW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
    (CryptoGames.SM.Engine.implEC hk (q + 1) 3 qep maxForwardJumps
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es qe)
  have hbB := bits_le_add_one ((q + 1) * (maxForwardJumps + 1))
  rw [hesE, hqeE] at hE
  unfold fig8StepBound at hC
  unfold fig8AtomicStepBound
  dsimp only at hC ⊢
  generalize bits ((q + 1) * (maxForwardJumps + 1)) = bB at hE hbB
  generalize (q + 1) * (maxForwardJumps + 1) = B' at hE hbB hC hW ⊢
  omega

private theorem implEC_any_sizeW_le_qep {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka} {Γ' : List (Ty S_cka)}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (q qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (qe : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (hesS : Bundles.exprSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1))) es ≤ 10)
    (hqeS : Bundles.exprSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1))) qe ≤ 10)
    (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ qep + 2)
    (hqep : qep ≤ 4096 * q + 100000000)
    (hhk : HooksSizeBounded ((q + 1) * (maxForwardJumps + 1)) sS qS hk
      (80 * bits (ratchetCostBudget q qep) + 15000) 2000
      (14 * bits (ratchetCostBudget q qep) + 5000)) :
    Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1))) sS qS
      (CryptoGames.SM.Engine.implEC hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es qe) ≤
      800 * bits (ratchetCostBudget q qep) + 200200 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  have h0 := implEC_sizeW_le hk
    (80 * bits (ratchetCostBudget q qep) + 15000) 2000 (14 * bits (ratchetCostBudget q qep) + 5000)
    (q + 1) qep maxForwardJumps mo hhk es qe
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbm : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hbtS : bits mo.tStar ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (mo.tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  omega






private theorem hooksCKABucketC_costBounded (B : ℕ) (tL : Option ℕ) :
    HooksCostBounded
      (CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 tL)
      (3 * bits (healEpoch tL) + 3 * bits (tL.getD 0) + (B + 1) + 1200) where
  startSend_le h ctx p t γv σ r := by
    refine ((hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B ⟨true, tL, 0⟩).startSend_le h ctx p t γv σ r).trans ?_
    dsimp [CryptoGames.SM.Construction.Mode.tH]; omega
  startRecv_le h ctx p t γv σ tn := by
    dsimp only [CryptoGames.SM.Construction.hooksCKABucketC,
      CryptoGames.SM.Construction.ckaStartRecvBucketAnsE]
    refine (ret_pair_letE_cost_le_costUB _ _ _).trans ?_
    cases tL with
    | none =>
      simp only [CryptoGames.SM.Engine.optNatLit, CryptoGames.SM.validGuessE,
        CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
        CryptoGames.SM.leN, CryptoGames.CKA.ckaOps, Expr.cost,
        Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, Expr.v7,
        dsl_cost, Option.getD_none, Nat.reduceAdd]; omega
    | some n =>
      simp only [CryptoGames.SM.Engine.optNatLit, CryptoGames.SM.validGuessE,
        CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
        CryptoGames.SM.leN, CryptoGames.CKA.ckaOps, Expr.cost,
        Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, Expr.v7,
        dsl_cost, Option.getD_some, Nat.reduceAdd]; omega
  fsSend_le h ctx p t ss hdr m pair := by
    refine ((hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B ⟨true, tL, 0⟩).fsSend_le h ctx p t ss hdr m pair).trans ?_
    dsimp [CryptoGames.SM.Construction.Mode.tH]; omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    refine ((hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B ⟨true, tL, 0⟩).fsRecv_le h ctx p t rs hdr e rec_).trans ?_
    dsimp [CryptoGames.SM.Construction.Mode.tH]; omega
  commit_le h ctx p old new := by
    refine ((hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B ⟨true, tL, 0⟩).commit_le h ctx p old new).trans ?_
    dsimp [CryptoGames.SM.Construction.Mode.tH]; omega
  reveal_le h ctx p vp := by
    refine ((hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B ⟨true, tL, 0⟩).reveal_le h ctx p vp).trans ?_
    dsimp [CryptoGames.SM.Construction.Mode.tH]; omega

private theorem hooksCKABucketC_excessBounded (B0 B : ℕ) (tL : Option ℕ) :
    HooksExcessBounded B0 ckaSampC ckaQueryC
      (CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 tL)
      2000 380000 (20 * B0 + 3 * bits B + 2710000) where
  startSend_le h ctx p t γv σ r :=
    (hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).startSend_le h ctx p t γv σ r
  startRecv_le h ctx p t γv σ tn := by
    simp only [CryptoGames.SM.Construction.hooksCKABucketC,
      CryptoGames.SM.Construction.ckaStartRecvBucketAnsE,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
      CryptoGames.SM.ltOptE, CryptoGames.SM.leN, optNatLit_excessUB, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tget, compExcessUB_ret,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add]; omega
  fsSend_le h ctx p t ss hdr m pair :=
    (hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).fsSend_le h ctx p t ss hdr m pair
  fsRecv_le h ctx p t rs hdr e rec_ :=
    (hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).fsRecv_le h ctx p t rs hdr e rec_
  commit_le h ctx p old new :=
    (hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).commit_le h ctx p old new
  reveal_le h ctx p vp :=
    (hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).reveal_le h ctx p vp

private theorem hooksCKABucketC_sizeBounded (B0 B : ℕ) (tL : Option ℕ) :
    HooksSizeBounded B0 Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 tL)
      (5 * bits (healEpoch tL) + 5 * bits (tL.getD 0) + 6000) 2000 (3 * bits B0 + 2 * bits B + 2000) where
  startSend_le h ctx p t γv σ r := by
    refine ((hooksCKAC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).startSend_le h ctx p t γv σ r).trans ?_
    dsimp [CryptoGames.SM.Construction.Mode.tH]; omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [CryptoGames.SM.Construction.hooksCKABucketC,
      CryptoGames.SM.Construction.ckaStartRecvBucketAnsE,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
      CryptoGames.SM.ltOptE, CryptoGames.SM.leN, optNatLit_sizeW, Bundles.ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
      exprSizeW_v5, exprSizeW_v6, exprSizeW_v7, exprSizeW_var,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_add, exprSizeW_lt, exprSizeW_eqN,
      exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_none, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tget, compSizeW_ret,
      bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
    (try split_ifs) <;> omega
  fsSend_le h ctx p t ss hdr m pair :=
    (hooksCKAC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).fsSend_le h ctx p t ss hdr m pair
  fsRecv_le h ctx p t rs hdr e rec_ :=
    (hooksCKAC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).fsRecv_le h ctx p t rs hdr e rec_
  commit_le h ctx p old new := by
    refine ((hooksCKAC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).commit_le h ctx p old new).trans ?_
    dsimp [CryptoGames.SM.Construction.Mode.tH]; omega
  reveal_le h ctx p vp := by
    refine ((hooksCKAC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩).reveal_le h ctx p vp).trans ?_
    dsimp [CryptoGames.SM.Construction.Mode.tH]; omega

private theorem vpId_cost {O' : Ops S_cka} {γvT svT ssvT vrT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.vpTy γvT svT ssvT vrT)) :
    (CryptoGames.SM.Engine.vpId s).cost = s.cost + 1 := rfl

private theorem vpRoot_cost {O' : Ops S_cka} {γvT svT ssvT vrT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.vpTy γvT svT ssvT vrT)) :
    (CryptoGames.SM.Engine.vpRoot s).cost = s.cost + 2 := rfl

private theorem vpVS_cost {O' : Ops S_cka} {γvT svT ssvT vrT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.vpTy γvT svT ssvT vrT)) :
    (CryptoGames.SM.Engine.vpVS s).cost = s.cost + 3 := rfl

private theorem vpVR_cost {O' : Ops S_cka} {γvT svT ssvT vrT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.vpTy γvT svT ssvT vrT)) :
    (CryptoGames.SM.Engine.vpVR s).cost = s.cost + 4 := rfl

private theorem vpΓ_cost {O' : Ops S_cka} {γvT svT ssvT vrT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.vpTy γvT svT ssvT vrT)) :
    (CryptoGames.SM.Engine.vpΓ s).cost = s.cost + 5 := rfl

private theorem vpTcur_cost {O' : Ops S_cka} {γvT svT ssvT vrT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.vpTy γvT svT ssvT vrT)) :
    (CryptoGames.SM.Engine.vpTcur s).cost = s.cost + 6 := rfl

private theorem vpTcurNat_cost {O' : Ops S_cka} {γvT svT ssvT vrT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.vpTy γvT svT ssvT vrT)) :
    (CryptoGames.SM.Engine.vpTcurNat s).cost = s.cost + 6 := rfl

private theorem vpMk_cost {O' : Ops S_cka} {γvT svT ssvT vrT : Ty S_cka} {Γ'}
    (id : Expr O' Γ' .bool) (root : Expr O' Γ' svT)
    (vS : Expr O' Γ' (.opt ssvT)) (vR : Expr O' Γ' vrT)
    (γ : Expr O' Γ' γvT) (curCkaMsg : Expr O' Γ' (.opt (.base .t)))
    (tcur : Expr O' Γ' .nat) :
    (CryptoGames.SM.Engine.vpMk id root vS vR γ curCkaMsg tcur).cost =
      id.cost + (root.cost + (vS.cost + (vR.cost +
        (γ.cost + (curCkaMsg.cost + tcur.cost + 1) + 1) + 1) + 1) + 1) + 1 := rfl

private theorem vpSetVS_cost {O' : Ops S_cka} {γvT svT ssvT vrT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.vpTy γvT svT ssvT vrT))
    (vS : Expr O' Γ' (.opt ssvT)) :
    (CryptoGames.SM.Engine.vpSetVS s vS).cost = (s.cost + vS.cost + 1) + 44 + 1 := rfl

private theorem vSendStep1C_any_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H : ℕ)
    (hhk : HooksCostBounded hk H)
    {Γ'} (h : Expr OO_cka Γ' hsT)
    (ctx : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (s : Expr OO_cka Γ' (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (r : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    (CryptoGames.SM.Engine.vSendStep1C hk h ctx p s r).cost ≤
      h.cost + ctx.cost + p.cost + s.cost + r.cost + H + 250 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) :=
    .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.opt (.base .ccoins))))) :: Γ'
  have hss := hhk.startSend_le (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (CryptoGames.SM.Engine.vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (CryptoGames.SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v0)))))
    (CryptoGames.SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
  simp only [vpTcurNat_cost, vpΓ_cost, vpRoot_cost, v0_cost, Expr.cost, hb1, Nat.reduceAdd] at hss
  simp only [CryptoGames.SM.Engine.vSendStep1C, CryptoGames.SM.sendsInE, vpMk_cost, vpId_cost,
    vpVR_cost, vpTcurNat_cost, Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost,
    hb0, hb1, hb2, Nat.reduceAdd]
  omega

private theorem vSendC_any_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H : ℕ)
    (hhk : HooksCostBounded hk H)
    {Γ'} (h : Expr OO_cka Γ' hsT)
    (ctx : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (s : Expr OO_cka Γ' (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (m : Expr OO_cka Γ' (.base .msg))
    (pair : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (r : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    (CryptoGames.SM.Engine.vSendC hk h ctx p s m pair r).cost ≤
      h.cost + ctx.cost + p.cost + s.cost + m.cost + pair.cost + r.cost + 2 * H + 600 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) :=
    .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
      (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  let Γ1 : List (Ty S_cka) := ssvT :: vpT :: .prod (.opt vpT) hsT :: Γ0
  have hs1 := vSendStep1C_any_cost_le hk H hhk (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  have hfs := hhk.fsSend_le (Γ' := Γ1)
    (.snd .v2) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (CryptoGames.SM.Engine.vpTcurNat .v1) .v0
    (.pair (CryptoGames.SM.Engine.vpTcurNat .v1) (CryptoGames.SM.Engine.vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
  simp only [vpTcurNat_cost, vpTcur_cost, v0_cost, v1_cost, v2_cost, v3_cost,
    Expr.cost, Nat.reduceAdd] at hs1 hfs
  simp only [CryptoGames.SM.Engine.vSendC, vpVS_cost, vpTcurNat_cost, vpTcur_cost, vpSetVS_cost,
    CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost, v0_cost, v1_cost, v3_cost, Nat.reduceAdd]
  omega

private theorem cChallContainsE_any_cost_le {O' : Ops S_cka} {vpT : Ty S_cka}
    (L : ℕ) {Γ'} (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (pos : Expr O' Γ' CryptoGames.SM.posTy) :
    (CryptoGames.SM.Engine.cChallContainsE L s pos).cost ≤ s.cost + pos.cost + 70 * L + 50 := by
  have hmax34 : max 3 4 = 4 := rfl
  simp only [CryptoGames.SM.Engine.cChallContainsE, CryptoGames.SM.Engine.cGsChall,
    CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    Expr.cost, v0_cost, v1_cost, hmax34, Nat.reduceAdd]
  omega

private theorem cMustBeCorrectE_any_cost_le {O' : Ops S_cka} {vpT : Ty S_cka}
    (L maxSkip : ℕ) {Γ'} (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr O' Γ' .bool) (r : Expr O' Γ' CryptoGames.SM.Engine.cRecTy) :
    (CryptoGames.SM.Engine.cMustBeCorrectE L maxSkip s p r).cost ≤
      s.cost + p.cost + r.cost + (maxSkip + 1) + 400 := by
  have hb1 : bits 1 = 1 := rfl
  have hms := bits_le_succ maxSkip
  let Γ0 : List (Ty S_cka) :=
    .prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool CryptoGames.SM.Engine.cRecTy) :: Γ'
  have hcc := cCompContainsE_cost_le (O' := O') (vpT := vpT) L (Γ' := Γ0)
    (.fst .v0) (CryptoGames.SM.Engine.cRecPos (.snd (.snd .v0)))
  simp only [cRecPos_cost, v0_cost, Expr.cost, Nat.reduceAdd] at hcc
  simp only [CryptoGames.SM.Engine.cMustBeCorrectE, CryptoGames.SM.leN,
    CryptoGames.SM.maxAccGet, CryptoGames.SM.pGet,
    CryptoGames.SM.Engine.cGsMaxAcc, cRecPos_cost, CryptoGames.SM.posIdx, CryptoGames.SM.posEpoch,
    Expr.cost, v0_cost, hb1, Nat.reduceAdd]
  omega

private theorem deliverEC_any_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L maxSkip : ℕ)
    (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    (CryptoGames.SM.Engine.deliverEC hk L maxSkip cfg es arg).cost ≤
      es.cost + arg.cost + 3 * H + 600 * L + (maxSkip + 1) + 4600 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool hdrCtT) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  let Γ3 : List (Ty S_cka) := decT :: Γ2
  let Γ4 : List (Ty S_cka) :=
    CryptoGames.SM.Engine.cGsTy vpT :: .prod (.opt (CryptoGames.SM.Engine.cGsTy vpT)) (CryptoGames.SM.Engine.esTy vpT hsT) :: Γ3
  have hit := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) (.some .v0)
  have hmb3 := cMustBeCorrectE_any_cost_le (O' := OO_cka) (vpT := vpT) L maxSkip (Γ' := Γ2)
    (CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3)) .v2
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ3)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (CryptoGames.SM.Engine.cRecPos .v3)
  have hmb6 := cMustBeCorrectE_any_cost_le (O' := OO_cka) (vpT := vpT) L maxSkip (Γ' := Γ4)
    (CryptoGames.SM.Engine.esG (.fst .v6)) (.fst (.snd .v6)) .v5
  have hcc6 := cChallContainsE_any_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ4)
    (CryptoGames.SM.Engine.esG (.fst .v6)) (CryptoGames.SM.Engine.cRecPos .v5)
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, v6_cost,
    Nat.reduceAdd] at hit hvr hmb3 hcm hmb6 hcc6
  simp only [CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.orE, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.cRecMsg, CryptoGames.SM.posEpoch,
    CryptoGames.SM.posIdx, cRecPos_cost, esG_cost, esAbort_cost, esSetG_cost, cGsSetWin_cost,
    CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v5_cost,
    Nat.reduceAdd]
  omega

private theorem injectEC_bucket_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (tL : Option ℕ) (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    (CryptoGames.SM.Engine.injectEC hk L 3 qep
      (CryptoGames.SM.Construction.bucketAuthCfgEC 1 tL) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 600 * L + bits qep + bits (tL.getD 0) + 4300 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool hdrCtT) :: Γ'
  let Γ1 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ0
  have hit := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsi : (CryptoGames.SM.Engine.cSafeInjE (O' := OO_cka) (vpT := vpT) 3 (Γ' := Γ0)
      (CryptoGames.SM.Engine.esG (.fst .v0))).cost ≤
      (CryptoGames.SM.Engine.esG (O' := OO_cka) (vpT := vpT) (Γ' := Γ0) (.fst .v0)).cost + 80 := by
    simp only [CryptoGames.SM.Engine.cSafeInjE, CryptoGames.SM.healedByE, CryptoGames.SM.leN,
      CryptoGames.SM.minN, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsEpoch,
      Expr.cost, Expr.v0, Expr.v1, bits_three, Nat.reduceAdd]; omega
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ0)
    (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.fst (.snd .v0))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0)))
    (.snd (.snd .v0)) .none
  have htr := cTrivialE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v3))
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij : ((CryptoGames.SM.Construction.bucketAuthCfgEC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      1 tL).injectFullE (O' := OO_cka)
      (Γ' := Γ1) (.fst (.snd .v0))).cost ≤ bits (tL.getD 0) + 100 := by
    refine (exprCost_le_costUB _).trans ?_
    cases tL with
    | none =>
      simp only [CryptoGames.SM.Construction.bucketAuthCfgEC, CryptoGames.SM.Engine.optNatLit,
        CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
        CryptoGames.SM.ltOptE, CryptoGames.SM.leN, Expr.v0, Expr.v1, Expr.v2,
        dsl_cost, bits_three, Option.getD_none, Nat.reduceAdd]; omega
    | some n =>
      simp only [CryptoGames.SM.Construction.bucketAuthCfgEC, CryptoGames.SM.Engine.optNatLit,
        CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
        CryptoGames.SM.ltOptE, CryptoGames.SM.leN, Expr.v0, Expr.v1, Expr.v2,
        dsl_cost, bits_three, Option.getD_some, Nat.reduceAdd]; omega
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, otherE_cost,
    Expr.cost, v0_cost, v2_cost, v3_cost, Nat.reduceAdd] at hit hsi hvr htr hcm
  simp only [CryptoGames.SM.Engine.injectEC, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esMk,
    esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost,
    Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd]
  omega

private theorem cka_bucket_arith_aux (L B bq bB qbq : ℕ) (hbB : bB ≤ B + 1) :
    (7000 * L + 3 * (6 * bq + B + 1300) + 20 * bq + 100000) +
      (500 * L + 45 * B + 6 * bB + 7500000) + 200000 ≤
      100000 * L + qbq + 120 * B + 200 * bq + 25000000 := by
  omega

private theorem cka_bucket_handle_le_fig8AtomicStepBound (q qep : ℕ) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let H := 6 * bits qep + B + 1300
    (7000 * L + 3 * H + 20 * bits qep + 100000) +
      (500 * L + 45 * B + 6 * bits B + 7500000) + 200000 ≤
      fig8AtomicStepBound q qep :=
  cka_bucket_arith_aux (q + 1) ((q + 1) * (maxForwardJumps + 1)) (bits qep)
    (bits ((q + 1) * (maxForwardJumps + 1))) ((q + 1) * (3 * bits qep + 60))
    (bits_le_succ _)

set_option linter.unusedSimpArgs false in
private theorem redCKAAuthBucketProg_init_finish_le (q qep : ℕ) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) (qep + 1)) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAAuthBucketProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL
    compCostW (ckaOpC B) ckaSampC ckaQueryC P.init +
      compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish + 100000 ≤
        fig8AtomicStepBound q qep := by
  intro B P
  let L := q + 1
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  have hbtL : bits (tL.getD 0) ≤ bits qep + 4 :=
    (bits_mono htL1).trans ((bits_succ_le qep).trans (by omega))
  have hbtH : bits (healEpoch tL) ≤ bits qep + 4 :=
    (bits_mono htL2).trans ((bits_succ_le qep).trans (by omega))
  have hiW : compCostW (ckaOpC B) ckaSampC ckaQueryC P.init ≤ 0 * bits qep + 0 * (q + 1) + 5000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthBucketProg]
    have hiC0 := initCKAEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) ⟨true, tL, 0⟩ (Γ' := [.unit]) (.bool false)
    have hiE0 := initCKAEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B ⟨true, tL, 0⟩ (Γ' := [.unit]) (.bool false)
    refine compCostW_le_of_parts (a := 800) (b := 2200) ?_ ?_ (by omega)
    · simp only [Comp.cost, Expr.cost, Expr.v0] at hiC0 ⊢; omega
    · simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit,
        exprExcessUB_bool, exprExcessUB_none, exprExcessUB_v0] at hiE0 ⊢; omega
  have hfW : compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish ≤ 2 * bits qep + 200 * (q + 1) + 600 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthBucketProg]
    rw [show (2 : ℕ) + 1 = 3 from rfl]
    refine compCostW_le_of_parts (a := bits (tL.getD 0) + 180 * L + 400) (b := 0) ?_ ?_ (by dsimp [L]; omega)
    · refine (compCost_le_costUB _).trans ?_
      cases tL with
      | none =>
        simp only [CryptoGames.SM.Engine.cAuthOKE, CryptoGames.SM.Engine.cCanonE,
          CryptoGames.SM.Engine.optNatLit, CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE,
          CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
          CryptoGames.SM.boolEq, CryptoGames.SM.receiverOfE,
          CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.cGsWin,
          CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
          Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
          dsl_cost, bits_zero, bits_one, bits_two, bits_three,
          Option.getD_none, L, Nat.reduceAdd]; omega
      | some n =>
        simp only [CryptoGames.SM.Engine.cAuthOKE, CryptoGames.SM.Engine.cCanonE,
          CryptoGames.SM.Engine.optNatLit, CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE,
          CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
          CryptoGames.SM.boolEq, CryptoGames.SM.receiverOfE,
          CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.cGsWin,
          CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
          Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
          dsl_cost, bits_zero, bits_one, bits_two, bits_three,
          Option.getD_some, L, Nat.reduceAdd]; omega
    · simp only [CryptoGames.SM.Engine.cAuthOKE, CryptoGames.SM.Engine.cCanonE,
        CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
        CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
        CryptoGames.SM.receiverOfE, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esG,
        CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
        optNatLit_excessUB, compExcessUB_bind, compExcessUB_ret, compExcessUB_caseOpt,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
        exprExcessUB_v5, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
        exprExcessUB_add, exprExcessUB_sub, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN,
        exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
        exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
        exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_foldrB,
        Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega
  refine (Nat.add_le_add_right (Nat.add_le_add hiW hfW) 100000).trans ?_
  refine (le_of_eq ?_).trans (linear_le_fig8AtomicStepBound (k := 2) (a := 200)
    (b := 105600) (q := q) (qep := qep) (by decide) (by decide) (by decide))
  ring

set_option linter.unusedSimpArgs false in
private theorem redCKAAuthBucketProg_handle_cost_le (L B qep maxSkip H : ℕ) (tL : Option ℕ)
    (hhkC : HooksCostBounded
      (CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 tL) H) :
    (CryptoGames.SM.Construction.redCKAAuthBucketProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip tL).handle.cost ≤
      7000 * L + 3 * H + 5 * bits qep + 2 * bits (tL.getD 0) + maxSkip + 30000 := by
  dsimp only [CryptoGames.SM.Construction.redCKAAuthBucketProg]
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  let vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E
  let hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := CryptoGames.SM.Construction.ckaEsTy (KC := KC) (Γ := Γ) (CCoins := CCoins)
    (T := T) (I := I) (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) smqT) ::
    [CryptoGames.SM.Construction.ckaBucketEsTy, smqT]
  let Γ_cr : List (Ty S_cka) := .bool :: Γ0
  let Γ_s1 : List (Ty S_cka) := .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ0
  let Γ_ij : List (Ty S_cka) := dlQ :: Γ_s1
  let Γ_s2 : List (Ty S_cka) := .sum (.sum trQ chQ) dlQ :: Γ_s1
  let Γ_dl : List (Ty S_cka) := dlQ :: Γ_s2
  let Γ_s3 : List (Ty S_cka) := .sum trQ chQ :: Γ_s2
  let Γ_tr : List (Ty S_cka) := trQ :: Γ_s3
  let Γ_tr0 : List (Ty S_cka) := trQ :: Γ_tr
  let Γ_tr1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ_tr0
  let Γ_tr2 : List (Ty S_cka) := .prod vpT hdrCtT :: .prod (.opt (.prod vpT hdrCtT)) hsT :: Γ_tr1
  have hrvC := hhkC.reveal_le (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) .v0
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) .v0)
  dsimp only [CryptoGames.SM.Construction.hooksCKABucketC] at hrvC
  generalize CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B 1 tL = hk at hhkC ⊢
  have hepC : (CryptoGames.SM.Engine.cEpMgmtE (O' := OO_cka) (vpT := vpT) 3 qep (Γ' := Γ_tr0)
      (CryptoGames.SM.Engine.esG (.fst .v5)) (.fst .v0) (CryptoGames.SM.isSomeE (.snd (.snd .v0)))).cost ≤
      2 * bits qep + 600 := by
    refine (exprCost_le_costUB _).trans ?_
    simp only [CryptoGames.SM.Engine.cEpMgmtE, CryptoGames.SM.Engine.cSafeChE,
      CryptoGames.SM.Engine.cLeakE, CryptoGames.SM.Engine.cGsMk,
      CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
      CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
      CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
      CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      CryptoGames.SM.Engine.esG, CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE,
      CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.boolEq,
      Expr.v0, Expr.v1, Expr.v2, Expr.v5, dsl_cost,
      bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]; omega
  have hvsC := vSendC_any_cost_le hk H hhkC (Γ' := Γ_tr1)
    (CryptoGames.SM.Engine.esH (.fst .v6)) .v0 (.fst .v1)
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
    (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hrecC : (CryptoGames.SM.Engine.cRecordE (O' := OO_cka) (vpT := vpT) L 3 (Γ' := Γ_tr2)
      .v2 (.fst .v3) (.fst .v0)
      (.pair (.pair (.fst .v3) (.pair (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
        (.add (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
        (.pair (.fst (.snd .v3)) (.snd .v0))) (.bool false)).cost ≤ 200 * L + 2000 := by
    refine (exprCost_le_costUB _).trans ?_
    simp only [CryptoGames.SM.Engine.cRecordE, CryptoGames.SM.Engine.cSafeChE,
      CryptoGames.SM.Engine.cCompInsertE,
      CryptoGames.SM.Engine.cCompSetE, CryptoGames.SM.Engine.cGsMk,
      CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
      CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
      CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
      CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE,
      CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
      CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
      CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, dsl_cost,
      bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]; omega
  have hdlC := deliverEC_any_cost_le hk H L maxSkip
    (CryptoGames.SM.Construction.bucketAuthCfgEC 1 tL) hhkC (Γ' := Γ_dl) (.fst .v3) .v0
  have hijC := injectEC_bucket_cost_le hk H L qep tL hhkC (Γ' := Γ_ij) (.fst .v2) .v0
  have hcaC : (CryptoGames.SM.Engine.cCorrAllowedE (O' := OO_cka) (vpT := vpT) L (Γ' := Γ_cr)
      (CryptoGames.SM.Engine.esG (.fst .v1)) .v0).cost ≤ 200 * L + 300 := by
    refine (exprCost_le_costUB _).trans ?_
    simp only [CryptoGames.SM.Engine.cCorrAllowedE, CryptoGames.SM.Engine.cCompContainsE,
      CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsComp,
      CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.Engine.esG,
      CryptoGames.SM.pGet, CryptoGames.SM.otherE, CryptoGames.SM.boolEq,
      CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
      Expr.v0, Expr.v1, dsl_cost, Nat.reduceAdd]; omega
  let psT := CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ_cr2 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ_cr
  have hacC : (CryptoGames.SM.Engine.cAfterCorrE (O' := OO_cka) (vpT := vpT) L (Γ' := Γ_cr2)
      (CryptoGames.SM.Engine.esG (.fst .v3)) .v2).cost ≤ 5100 * L + 5000 := by
    refine (exprCost_le_costUB _).trans ?_
    simp only [CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.cLeakE,
      CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
      CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB,
      CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
      CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall,
      CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks,
      CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.Engine.esG,
      CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.otherE, CryptoGames.SM.leN,
      CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.boolEq,
      CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, dsl_cost, Nat.reduceAdd]; omega
  simp only [esG_cost, esH_cost, pGet_cost, cGsSt_cost,
    Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v5_cost, v6_cost, Nat.reduceAdd]
    at hvsC hdlC hijC hrvC
  simp only [CryptoGames.SM.orE, isSomeE_cost, pGet_cost,
    esG_cost, esH_cost, esAbort_cost, esSetG_cost, esSetH_cost, esSetAbort_cost,
    cGsSetWin_cost, cGsSt_cost, cGsEpoch_cost, cGsIdx_cost,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.cGsWin,
    Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, v6_cost, v7_cost,
    bits_one, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
private theorem cEpMgmtE_excessUB_le {O' : Ops S_cka} (opEx : O'.Op → ℕ) {vpT : Ty S_cka}
    (Δ qep : ℕ) {Γ'} (gs : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (p bad : Expr O' Γ' .bool) :
    exprExcessUB opEx (CryptoGames.SM.Engine.cEpMgmtE Δ qep gs p bad) ≤
      exprExcessUB opEx gs + exprExcessUB opEx p + exprExcessUB opEx bad := by
  simp only [CryptoGames.SM.Engine.cEpMgmtE, CryptoGames.SM.Engine.cSafeChE,
    CryptoGames.SM.Engine.cLeakE, CryptoGames.SM.Engine.cGsMk,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE,
    CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE,
    CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.boolEq,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
    exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
    exprExcessUB_letE, exprExcessUB_cons, exprExcessUB_anyB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

set_option linter.unusedSimpArgs false in
private theorem cRecordE_excessUB_le {O' : Ops S_cka} (opEx : O'.Op → ℕ) {vpT : Ty S_cka}
    (L Δ : ℕ) {Γ'} (gs : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr O' Γ' .bool) (vp : Expr O' Γ' vpT)
    (rec : Expr O' Γ' CryptoGames.SM.Engine.cRecTy) (isCh : Expr O' Γ' .bool) :
    exprExcessUB opEx (CryptoGames.SM.Engine.cRecordE L Δ gs p vp rec isCh) ≤
      exprExcessUB opEx gs + exprExcessUB opEx p + exprExcessUB opEx vp +
        exprExcessUB opEx rec + exprExcessUB opEx isCh := by
  simp only [CryptoGames.SM.Engine.cRecordE, CryptoGames.SM.Engine.cSafeChE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE, CryptoGames.SM.Engine.cGsMk,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE,
    CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
    CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
    exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
    exprExcessUB_letE, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

set_option linter.unusedSimpArgs false in
private theorem cCorrAllowedE_excessUB_le {O' : Ops S_cka} (opEx : O'.Op → ℕ) {vpT : Ty S_cka}
    (L : ℕ) {Γ'} (gs : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    exprExcessUB opEx (CryptoGames.SM.Engine.cCorrAllowedE L gs p) ≤
      exprExcessUB opEx gs + exprExcessUB opEx p := by
  simp only [CryptoGames.SM.Engine.cCorrAllowedE, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.pGet, CryptoGames.SM.otherE, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
    exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_modK,
    exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_letE,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

set_option linter.unusedSimpArgs false in
private theorem cAfterCorrE_excessUB_le {O' : Ops S_cka} (opEx : O'.Op → ℕ) {vpT : Ty S_cka}
    (L : ℕ) {Γ'} (gs : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    exprExcessUB opEx (CryptoGames.SM.Engine.cAfterCorrE L gs p) ≤
      exprExcessUB opEx gs + exprExcessUB opEx p := by
  simp only [CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall,
    CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks,
    CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.otherE, CryptoGames.SM.leN,
    CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
    exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
    exprExcessUB_letE, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

set_option linter.unusedSimpArgs false in
private theorem deliverEC_any_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sE : I'.smp.Samp → ℕ} {qE : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L maxSkip : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hhk : HooksExcessBounded B0 sE qE hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compExcessUB (ckaOpC B0) sE qE (CryptoGames.SM.Engine.deliverEC hk L maxSkip cfg es arg) ≤
      exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg +
        2 * Ho + Hr + 150 * L + 34000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_dl0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  have hit_dl := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr_dl := vRecvC_excessUB_le hk Ho Hs Hr hhk
    (Γ' := CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) (.some .v0)
  have hcm_dl := commitEC_excessUB_le hk Ho Hs Hr L hhk
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (CryptoGames.SM.Engine.cRecPos .v3)
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet, CryptoGames.SM.otherE,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_var, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_some, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hit_dl hvr_dl hcm_dl
  simp only [CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cChallContainsE, CryptoGames.SM.Engine.cMustBeCorrectE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esSetAbort,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.Engine.cRecMsg, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.otherE,
    CryptoGames.SM.leN, CryptoGames.SM.maxAccGet, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_unit,
    exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add, exprExcessUB_sub,
    exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

set_option linter.unusedSimpArgs false in
private theorem injectEC_bucket_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sE : I'.smp.Samp → ℕ} {qE : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep : ℕ) (tL : Option ℕ)
    (hhk : HooksExcessBounded B0 sE qE hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compExcessUB (ckaOpC B0) sE qE
      (CryptoGames.SM.Engine.injectEC hk L 3 qep
        (CryptoGames.SM.Construction.bucketAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) 1 tL) es arg) ≤
      exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg +
        2 * Ho + Hr + 150 * L + 2000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_ij0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  have hit_ij := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr_ij := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ_ij0)
    (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.fst (.snd .v0))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0)))
    (.snd (.snd .v0)) .none
  have hcm_ij := commitEC_excessUB_le hk Ho Hs Hr L hhk
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0)
    (CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, CryptoGames.SM.otherE,
    exprExcessUB_v0, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var, exprExcessUB_not,
    exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none,
    exprExcessUB_letE, Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hit_ij hvr_ij hcm_ij
  simp only [CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Construction.bucketAuthCfgEC,
    optNatLit_excessUB, CryptoGames.SM.validGuessE, CryptoGames.SM.optNatEqE,
    CryptoGames.SM.Engine.cSafeInjE, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG,
    CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG,
    CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esSetAbort,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE, CryptoGames.SM.pGet,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.leN,
    CryptoGames.SM.minN, CryptoGames.SM.ltOptE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7,
    exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not,
    exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
    exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

section BucketHandleAbs

open _root_.CryptoGames.SM (orE isSomeE pGet)
open _root_.CryptoGames.SM.Engine (HooksC esTy vpTblTy esAbort esG esH esMk cGsWin cGsSt cGsEpoch cGsIdx
  cEpMgmtE vSendC cRecordE deliverEC injectEC cCorrAllowedE cAfterCorrE)
open _root_.CryptoGames.SM.Construction (bucketAuthCfgEC)
open scoped Computational.Proofs.ReductionDsl.Notation

private def bucketHandleC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L Δcka qep maxSkip : ℕ) (tL : Option ℕ) :
    Comp OO_cka I'
      [.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT) (.opt .nat),
       CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E]
      (.prod (CryptoGames.CKA.ckaSMR KC Γ CCoins T I KR RSt K SS RS M E)
        (.prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT) (.opt .nat))) :=
  rdsl [st, q] do
    (es0, winEp0, q0) ← return (st.1, st.2, q)
    match q0 with
    | .inl (.inl (.inl (.inl x))) =>
      (p0, m0, r0) ← return x
      if orE (esAbort es0) (cGsWin (esG es0)) then
        return (inl (inl (inl (inl none))), (es0, winEp0))
      else
        match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
        | none => return (inl (inl (inl (inl none))), (es0, winEp0))
        | some s1 =>
          (res, h') ← vSendC (raw hk) (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
          match res with
          | none => return (inl (inl (inl (inl none))), (esMk (esG es0) h' true, winEp0))
          | some (st', ct) =>
            let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
            let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
            return (inl (inl (inl (inl (some ct)))), (esMk g' h' (esAbort es0), winEp0))
    | .inl (.inl (.inl (.inr _))) =>
      return (inl (inl (inl (inr none))), (es0, winEp0))
    | .inl (.inl (.inr x)) =>
      (out, es') ← deliverEC (raw hk) L maxSkip
        (raw (bucketAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) Δcka tL)) es0 x
      return (inl (inl (inr out)), (es', winEp0))
    | .inl (.inr x) =>
      let wasWin := cGsWin (esG es0)
      (out, es') ← injectEC (raw hk) L (raw (2 + Δcka)) qep
        (raw (bucketAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) Δcka tL)) es0 x
      let winEp' := if !wasWin && cGsWin (esG es') then some x.2.1.1 else winEp0
      return (inl (inr out), (es', winEp'))
    | .inr p0 =>
      let s0 := esG es0
      if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedE (raw L) s0 p0))) then
        return (inr none, (es0, winEp0))
      else
        let s1 := cAfterCorrE (raw L) s0 p0
        (res, h') ← hk.reveal (esH es0) s0 p0 (pGet (cGsSt s0) p0)
        match res with
        | none => return (inr none, (esMk s0 h' true, winEp0))
        | some stOut =>
          return (inr (some stOut), (esMk s1 h' (esAbort es0), winEp0))

end BucketHandleAbs

set_option linter.unusedSimpArgs false in
private theorem bucketHandleC_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sE : I'.smp.Samp → ℕ} {qE : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L qep maxSkip Ho Hs Hr : ℕ) (tL : Option ℕ)
    (hhkE : HooksExcessBounded B0 sE qE hk Ho Hs Hr) :
    compExcessUB (ckaOpC B0) sE qE (bucketHandleC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) hk L 1 qep maxSkip tL) ≤
      500 * L + 6 * Ho + 4 * Hs + 2 * Hr + 5 * B0 + 60000 := by
  dsimp only [bucketHandleC]
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let psT := CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) smqT) :: [.prod esT (.opt .nat), smqT]
  let Γ_cr : List (Ty S_cka) := .bool :: Γ0
  let Γ_cr2 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ_cr
  let Γ_s1 : List (Ty S_cka) := .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ0
  let Γ_ij : List (Ty S_cka) := dlQ :: Γ_s1
  let Γ_s2 : List (Ty S_cka) := .sum (.sum trQ chQ) dlQ :: Γ_s1
  let Γ_dl : List (Ty S_cka) := dlQ :: Γ_s2
  let Γ_s3 : List (Ty S_cka) := .sum trQ chQ :: Γ_s2
  let Γ_tr : List (Ty S_cka) := trQ :: Γ_s3
  let Γ_tr0 : List (Ty S_cka) := trQ :: Γ_tr
  let Γ_tr1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ_tr0
  let Γ_tr2 : List (Ty S_cka) := .prod vpT hdrCtT :: .prod (.opt (.prod vpT hdrCtT)) hsT :: Γ_tr1
  have hrvE := hhkE.reveal_le (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) .v0
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) .v0)
  have hvsE := vSendC_excessUB_le hk Ho Hs Hr hhkE (Γ' := Γ_tr1)
    (CryptoGames.SM.Engine.esH (.fst .v6)) .v0 (.fst .v1)
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
    (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hepE := cEpMgmtE_excessUB_le (O' := OO_cka) (ckaOpC B0) (vpT := vpT) 3 qep (Γ' := Γ_tr0)
    (CryptoGames.SM.Engine.esG (.fst .v5)) (.fst .v0) (CryptoGames.SM.isSomeE (.snd (.snd .v0)))
  have hrecE := cRecordE_excessUB_le (O' := OO_cka) (ckaOpC B0) (vpT := vpT) L 3 (Γ' := Γ_tr2)
    .v2 (.fst .v3) (.fst .v0)
    (.pair (.pair (.fst .v3) (.pair (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
      (.add (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
      (.pair (.fst (.snd .v3)) (.snd .v0))) (.bool false)
  have hdlE := deliverEC_any_excessUB_le hk Ho Hs Hr L maxSkip
    (CryptoGames.SM.Construction.bucketAuthCfgEC 1 tL) hhkE (Γ' := Γ_dl) (.fst .v3) .v0
  have hijE := injectEC_bucket_excessUB_le hk Ho Hs Hr L qep tL hhkE (Γ' := Γ_ij) (.fst .v2) .v0
  have hcaE := cCorrAllowedE_excessUB_le (O' := OO_cka) (ckaOpC B0) (vpT := vpT) L (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esG (.fst .v1)) .v0
  have hacE := cAfterCorrE_excessUB_le (O' := OO_cka) (ckaOpC B0) (vpT := vpT) L (Γ' := Γ_cr2)
    (CryptoGames.SM.Engine.esG (.fst .v3)) .v2
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.isSomeE, CryptoGames.SM.pGet,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v5, exprExcessUB_v6,
    exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
    exprExcessUB_add, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
    at hvsE hrvE hepE hrecE hdlE hijE hcaE hacE
  simp only [CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esSetAbort,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_lt, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    compExcessUB_caseSum,
    Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  revert hepE; generalize exprExcessUB _ _ = q_ep; intro hepE
  revert hrecE; generalize exprExcessUB _ _ = q_rec; intro hrecE
  revert hcaE; generalize exprExcessUB _ _ = q_ca; intro hcaE
  revert hacE; generalize exprExcessUB _ _ = q_ac; intro hacE
  revert hvsE; generalize compExcessUB _ _ _ _ = q_vs; intro hvsE
  revert hrvE; generalize compExcessUB _ _ _ _ = q_rv; intro hrvE
  revert hdlE; generalize compExcessUB _ _ _ _ = q_dl; intro hdlE
  revert hijE; generalize compExcessUB _ _ _ _ = q_ij; intro hijE
  omega

private theorem redCKAAuthBucketProg_handle_excessUB_le (B0 B L qep maxSkip Ho Hs Hr : ℕ)
    (tL : Option ℕ)
    (hhkE : HooksExcessBounded B0 ckaSampC ckaQueryC
      (CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 tL) Ho Hs Hr) :
    compExcessUB (ckaOpC B0) ckaSampC ckaQueryC
      (CryptoGames.SM.Construction.redCKAAuthBucketProg (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip tL).handle ≤
      500 * L + 6 * Ho + 4 * Hs + 2 * Hr + 5 * B0 + 60000 :=
  bucketHandleC_excessUB_le
    (CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B 1 tL)
    L qep maxSkip Ho Hs Hr tL hhkE

private theorem redCKAAuthBucketProg_parts_le (q qep : ℕ) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) (qep + 1)) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAAuthBucketProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL
    compCostW (ckaOpC B) ckaSampC ckaQueryC P.init +
      compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish + 100000 ≤
        fig8AtomicStepBound q qep ∧
    compCostW (ckaOpC B) ckaSampC ckaQueryC P.handle + 200000 ≤
      fig8AtomicStepBound q qep := by
  intro B P
  refine ⟨redCKAAuthBucketProg_init_finish_le q qep tL htL, ?_⟩
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  have hbtL : bits (tL.getD 0) ≤ bits qep + 4 :=
    (bits_mono htL1).trans ((bits_succ_le qep).trans (by omega))
  have hbtH : bits (healEpoch tL) ≤ bits qep + 4 :=
    (bits_mono htL2).trans ((bits_succ_le qep).trans (by omega))
  have hmfj : maxForwardJumps ≤ 25000 := by decide
  let H := 6 * bits qep + B + 1300
  have hhkC : HooksCostBounded
      (CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 tL) H :=
    (hooksCKABucketC_costBounded B tL).mono (H' := H) (by dsimp [H]; omega)
  have hhkE := hooksCKABucketC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B B tL
  have hC := redCKAAuthBucketProg_handle_cost_le (q + 1) B qep maxForwardJumps H tL hhkC
  have hE := redCKAAuthBucketProg_handle_excessUB_le B B (q + 1) qep maxForwardJumps
    2000 380000 (20 * B + 3 * bits B + 2710000) tL hhkE
  refine (Nat.add_le_add_right (compCostW_le_of_parts
    (a := 7000 * (q + 1) + 3 * H + 20 * bits qep + 100000)
    (b := 500 * (q + 1) + 45 * B + 6 * bits B + 7500000)
    (hC.trans (by omega)) (hE.trans (by omega)) le_rfl) 200000).trans ?_
  exact cka_bucket_handle_le_fig8AtomicStepBound q qep


set_option linter.unusedSimpArgs false in
private theorem cEpMgmtE_sizeW_le {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka}
    (Δ qep : ℕ) {Γ'} (gs : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (p bad : Expr O' Γ' .bool) :
    Bundles.exprSizeW opS (CryptoGames.SM.Engine.cEpMgmtE Δ qep gs p bad) ≤
      6 * (Bundles.exprSizeW opS gs + Bundles.exprSizeW opS p + Bundles.exprSizeW opS bad) +
        10 * bits Δ + 10 * bits qep + 1000 := by
  simp only [CryptoGames.SM.Engine.cEpMgmtE, CryptoGames.SM.Engine.cSafeChE,
    CryptoGames.SM.Engine.cLeakE, CryptoGames.SM.Engine.cGsMk,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE,
    CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE,
    CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.boolEq,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v5, exprSizeW_v6, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
    exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt,
    exprSizeW_letE, exprSizeW_cons, exprSizeW_anyB, exprSizeW_foldrB,
    exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
private theorem cRecordE_sizeW_le {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka}
    (L Δ : ℕ) {Γ'} (gs : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr O' Γ' .bool) (vp : Expr O' Γ' vpT)
    (rec : Expr O' Γ' CryptoGames.SM.Engine.cRecTy) (isCh : Expr O' Γ' .bool) :
    Bundles.exprSizeW opS (CryptoGames.SM.Engine.cRecordE L Δ gs p vp rec isCh) ≤
      6 * (Bundles.exprSizeW opS gs + Bundles.exprSizeW opS p + Bundles.exprSizeW opS vp +
        Bundles.exprSizeW opS rec + Bundles.exprSizeW opS isCh) +
        10 * bits L + 10 * bits Δ + 2000 := by
  simp only [CryptoGames.SM.Engine.cRecordE, CryptoGames.SM.Engine.cSafeChE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE, CryptoGames.SM.Engine.cGsMk,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE,
    CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
    CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v5, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
    exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt,
    exprSizeW_letE, exprSizeW_cons, exprSizeW_len, exprSizeW_take,
    exprSizeW_findB, exprSizeW_anyB, exprSizeW_mapB, exprSizeW_foldrB,
    exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
private theorem cCorrAllowedE_sizeW_le {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka}
    (L : ℕ) {Γ'} (gs : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    Bundles.exprSizeW opS (CryptoGames.SM.Engine.cCorrAllowedE L gs p) ≤
      6 * (Bundles.exprSizeW opS gs + Bundles.exprSizeW opS p) + 10 * bits L + 500 := by
  simp only [CryptoGames.SM.Engine.cCorrAllowedE, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.pGet, CryptoGames.SM.otherE, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_modK,
    exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_findB, exprSizeW_anyB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
private theorem cAfterCorrE_sizeW_le {O' : Ops S_cka} (opS : O'.Op → ℕ) {vpT : Ty S_cka}
    (L : ℕ) {Γ'} (gs : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    Bundles.exprSizeW opS (CryptoGames.SM.Engine.cAfterCorrE L gs p) ≤
      11 * (Bundles.exprSizeW opS gs + Bundles.exprSizeW opS p) + 48 * bits L + 5300 := by
  simp only [CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall,
    CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks,
    CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.otherE, CryptoGames.SM.leN,
    CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v5, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
    exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt,
    exprSizeW_letE, exprSizeW_cons, exprSizeW_len, exprSizeW_take,
    exprSizeW_findB, exprSizeW_anyB, exprSizeW_mapB, exprSizeW_foldrB,
    exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
private theorem deliverEC_any_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L maxSkip : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.deliverEC hk L maxSkip cfg es arg) ≤
      6 * (Bundles.exprSizeW (Bundles.ckaOpS B0) es + Bundles.exprSizeW (Bundles.ckaOpS B0) arg) +
        2 * Ho + Hr + 9 * bits L + 5 * bits maxSkip + 6000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_dl0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  have hit_dl := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr_dl := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) (.some .v0)
  have hcm_dl := commitEC_sizeW_le hk Ho Hs Hr L hhk
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (CryptoGames.SM.Engine.cRecPos .v3)
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet, CryptoGames.SM.otherE,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_var, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_some, exprSizeW_letE, Nat.reduceAdd] at hit_dl hvr_dl hcm_dl
  simp only [CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cChallContainsE, CryptoGames.SM.Engine.cMustBeCorrectE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esSetAbort,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.Engine.cRecMsg, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.otherE,
    CryptoGames.SM.leN, CryptoGames.SM.maxAccGet, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, Bundles.ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v5, exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool,
    exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_modK,
    exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
    exprSizeW_findB, exprSizeW_anyB, exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget,
    exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
private theorem injectEC_bucket_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep : ℕ) (tL : Option ℕ)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS
      (CryptoGames.SM.Engine.injectEC hk L 3 qep
        (CryptoGames.SM.Construction.bucketAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) 1 tL) es arg) ≤
      6 * (Bundles.exprSizeW (Bundles.ckaOpS B0) es + Bundles.exprSizeW (Bundles.ckaOpS B0) arg) +
        2 * Ho + Hr + 8 * bits L + 4 * bits qep + 6 * bits (tL.getD 0) + 6500 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_ij0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  have hit_ij := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr_ij := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := Γ_ij0)
    (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.fst (.snd .v0))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0)))
    (.snd (.snd .v0)) .none
  have hcm_ij := commitEC_sizeW_le hk Ho Hs Hr L hhk
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0)
    (CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, CryptoGames.SM.otherE,
    exprSizeW_v0, exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_not,
    exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none,
    exprSizeW_letE, Nat.reduceAdd] at hit_ij hvr_ij hcm_ij
  simp only [CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Construction.bucketAuthCfgEC,
    optNatLit_sizeW, CryptoGames.SM.validGuessE, CryptoGames.SM.optNatEqE,
    CryptoGames.SM.Engine.cSafeInjE, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG,
    CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG,
    CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esSetAbort,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
    CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE, CryptoGames.SM.pGet,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.leN,
    CryptoGames.SM.minN, CryptoGames.SM.ltOptE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, Bundles.ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v5, exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool,
    exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_modK,
    exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
    exprSizeW_findB, exprSizeW_anyB, exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget,
    exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
  (try split_ifs) <;> omega

set_option linter.unusedSimpArgs false in
private theorem bucketHandleC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep maxSkip : ℕ) (tL : Option ℕ)
    (hhkS : HooksSizeBounded B0 sS qS hk Ho Hs Hr) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS
      (bucketHandleC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) hk L 1 qep maxSkip tL) ≤
      6 * Ho + 2 * Hs + 2 * Hr + 90 * bits L + 20 * bits qep + 10 * bits maxSkip +
        10 * bits (tL.getD 0) + 31000 := by
  dsimp only [bucketHandleC]
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let hdrCtT := CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let psT := CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) smqT) :: [.prod esT (.opt .nat), smqT]
  let Γ_cr : List (Ty S_cka) := .bool :: Γ0
  let Γ_cr2 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ_cr
  let Γ_s1 : List (Ty S_cka) := .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ0
  let Γ_ij : List (Ty S_cka) := dlQ :: Γ_s1
  let Γ_s2 : List (Ty S_cka) := .sum (.sum trQ chQ) dlQ :: Γ_s1
  let Γ_dl : List (Ty S_cka) := dlQ :: Γ_s2
  let Γ_s3 : List (Ty S_cka) := .sum trQ chQ :: Γ_s2
  let Γ_tr : List (Ty S_cka) := trQ :: Γ_s3
  let Γ_tr0 : List (Ty S_cka) := trQ :: Γ_tr
  let Γ_tr1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ_tr0
  let Γ_tr2 : List (Ty S_cka) := .prod vpT hdrCtT :: .prod (.opt (.prod vpT hdrCtT)) hsT :: Γ_tr1
  have hrvS := hhkS.reveal_le (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) .v0
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) .v0)
  have hvsS := vSendC_sizeW_le hk Ho Hs Hr hhkS (Γ' := Γ_tr1)
    (CryptoGames.SM.Engine.esH (.fst .v6)) .v0 (.fst .v1)
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
    (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hepS := cEpMgmtE_sizeW_le (O' := OO_cka) (Bundles.ckaOpS B0) (vpT := vpT) 3 qep (Γ' := Γ_tr0)
    (CryptoGames.SM.Engine.esG (.fst .v5)) (.fst .v0) (CryptoGames.SM.isSomeE (.snd (.snd .v0)))
  have hrecS := cRecordE_sizeW_le (O' := OO_cka) (Bundles.ckaOpS B0) (vpT := vpT) L 3 (Γ' := Γ_tr2)
    .v2 (.fst .v3) (.fst .v0)
    (.pair (.pair (.fst .v3) (.pair (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
      (.add (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
      (.pair (.fst (.snd .v3)) (.snd .v0))) (.bool false)
  have hdlS := deliverEC_any_sizeW_le hk Ho Hs Hr L maxSkip
    (CryptoGames.SM.Construction.bucketAuthCfgEC 1 tL) hhkS (Γ' := Γ_dl) (.fst .v3) .v0
  have hijS := injectEC_bucket_sizeW_le hk Ho Hs Hr L qep tL hhkS (Γ' := Γ_ij) (.fst .v2) .v0
  have hcaS := cCorrAllowedE_sizeW_le (O' := OO_cka) (Bundles.ckaOpS B0) (vpT := vpT) L (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esG (.fst .v1)) .v0
  have hacS := cAfterCorrE_sizeW_le (O' := OO_cka) (Bundles.ckaOpS B0) (vpT := vpT) L (Γ' := Γ_cr2)
    (CryptoGames.SM.Engine.esG (.fst .v3)) .v2
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.isSomeE, CryptoGames.SM.pGet,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v5, exprSizeW_v6,
    exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
    exprSizeW_add, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
    bits_zero, bits_one, bits_three, Nat.reduceAdd]
    at hvsS hrvS hepS hrecS hdlS hijS hcaS hacS
  simp only [CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH,
    CryptoGames.SM.Engine.esSetAbort,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, Bundles.ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v5, exprSizeW_v6, exprSizeW_v7, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
    exprSizeW_add, exprSizeW_sub, exprSizeW_lt, exprSizeW_eqN,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
    exprSizeW_some, exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd]
  revert hepS; generalize Bundles.exprSizeW _ _ = q_ep; intro hepS
  revert hrecS; generalize Bundles.exprSizeW _ _ = q_rec; intro hrecS
  revert hcaS; generalize Bundles.exprSizeW _ _ = q_ca; intro hcaS
  revert hacS; generalize Bundles.exprSizeW _ _ = q_ac; intro hacS
  revert hvsS; generalize Bundles.compSizeW _ _ _ _ = q_vs; intro hvsS
  revert hrvS; generalize Bundles.compSizeW _ _ _ _ = q_rv; intro hrvS
  revert hdlS; generalize Bundles.compSizeW _ _ _ _ = q_dl; intro hdlS
  revert hijS; generalize Bundles.compSizeW _ _ _ _ = q_ij; intro hijS
  omega

set_option linter.unusedSimpArgs false in
private theorem redCKAAuthBucketProg_size_le (q qep : ℕ) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) (qep + 1))
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redCKAAuthBucketProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps tL
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P
  let L := q + 1
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbm : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits (healEpoch tL) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hiS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤ 8500 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthBucketProg]
    have h0 := initCKAEStateC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B ⟨true, tL, 0⟩ (Γ' := [.unit]) (.bool false)
    simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit,
      exprSizeW_bool, exprSizeW_none, exprSizeW_v0] at h0 ⊢; omega
  have hfS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      50 * bits (ratchetCostBudget q qep) + 2000 := by
    dsimp only [P, CryptoGames.SM.Construction.redCKAAuthBucketProg]
    rw [show (2 : ℕ) + 1 = 3 from rfl]
    simp only [CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.cGsWin,
      CryptoGames.SM.Engine.cAuthOKE, CryptoGames.SM.Engine.cCanonE,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
      CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      optNatLit_sizeW, compSizeW_bind, compSizeW_ret, compSizeW_caseOpt,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
      exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN,
      exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_anyB, exprSizeW_foldrB,
      bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
    (try split_ifs) <;> omega
  have hhS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      900 * bits (ratchetCostBudget q qep) + 250000 := by
    let Ho := 80 * bits (ratchetCostBudget q qep) + 15000
    let Hs := 2000
    let Hr := 14 * bits (ratchetCostBudget q qep) + 5000
    have hhkS : HooksSizeBounded B Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 tL) Ho Hs Hr :=
      (hooksCKABucketC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B B tL).mono
        (Ho' := Ho) (Hs' := Hs) (Hr' := Hr) (by dsimp [Ho]; omega) le_rfl (by dsimp [Hr]; omega)
    have h0 := bucketHandleC_sizeW_le
      (CryptoGames.SM.Construction.hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 tL)
      Ho Hs Hr L qep maxForwardJumps tL hhkS
    refine h0.trans ?_
    dsimp only [Ho, Hs, Hr, L]
    omega
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1000) (by decide) (by decide) ?_; omega

private theorem redCKAAuthBucketProg_totalQueries_le (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (q : ℕ) :
    (CryptoGames.SM.Construction.redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  simp only [CostedReduction.totalQueries, CryptoGames.SM.Construction.redCKAAuthBucketProg,
    CryptoGames.SM.Construction.initCKAEStateC_queries, CryptoGames.SM.Engine.deliverEC,
    CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Engine.vSendC, CryptoGames.SM.Engine.vSendStep1C,
    CryptoGames.SM.Engine.vRecvC, CryptoGames.SM.Engine.vRecvStep1C, CryptoGames.SM.Engine.commitEC,
    CryptoGames.SM.Construction.hooksCKABucketC, CryptoGames.SM.Construction.ckaStartSendC,
    CryptoGames.SM.Construction.ckaFsSendC, CryptoGames.SM.Construction.ckaFsRecvC,
    CryptoGames.SM.Construction.ckaCommitC, CryptoGames.SM.Construction.ckaRevealC,
    Comp.queries, zero_add, add_zero, max_self, Nat.zero_max, Nat.max_zero, Nat.reduceAdd]
  have hm21 : max 2 1 = 2 := rfl
  have hm12 : max 1 2 = 2 := rfl
  simp only [hm21, hm12, max_self]; omega

end Stage2Parts

section FSPrivUniParts

set_option linter.unusedSimpArgs false

open _root_.ReductionDsl (bits_le_succ)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (compCostUB exprCostUB compCost_le_costUB
  exprCost_le_costUB)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded HooksCostBounded.mono
  hooksFSC_costBounded_linear initFSEStateC_cost_le implEC_cost_le
  pGet_cost cGsEpoch_cost cGsSt_cost esG_cost esH_cost fig8StepBound)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (HooksExcessBounded HooksExcessBounded.mono
  exprExcessUB hooksFSC_excessBounded initFSEStateC_excessUB_le corrDoomE_excessUB
  implEC_excessUB_le
  exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4 exprExcessUB_var
  exprExcessUB_unit exprExcessUB_bool exprExcessUB_nat exprExcessUB_lt
  exprExcessUB_eqN exprExcessUB_and exprExcessUB_pair exprExcessUB_inl exprExcessUB_inr
  exprExcessUB_none exprExcessUB_some exprExcessUB_caseOpt exprExcessUB_caseSum
  exprExcessUB_letE exprExcessUB_op exprExcessUB_tget exprExcessUB_tset
  compExcessUB_bind compExcessUB_ite compExcessUB_caseOpt compExcessUB_caseSum
  compExcessUB_sample compExcessUB_query)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (HooksSizeBounded.mono
  bits_one bits_two bits_three bits_four corrDoomE_sizeW_le optNatLit_sizeW
  compSizeW_caseOpt compSizeW_caseSum compSizeW_query
  exprSizeW_v2 exprSizeW_v3 exprSizeW_v4 exprSizeW_v5 exprSizeW_v6 exprSizeW_v7
  exprSizeW_var exprSizeW_nat exprSizeW_none exprSizeW_nil exprSizeW_add exprSizeW_sub
  exprSizeW_mulK exprSizeW_divK exprSizeW_modK exprSizeW_lt exprSizeW_eqN exprSizeW_and
  exprSizeW_inl exprSizeW_inr exprSizeW_some exprSizeW_caseOpt exprSizeW_caseSum
  exprSizeW_letE exprSizeW_op exprSizeW_cons exprSizeW_len exprSizeW_take
  exprSizeW_appendL exprSizeW_findB exprSizeW_anyB exprSizeW_mapB exprSizeW_foldrB
  exprSizeW_tconst exprSizeW_tget exprSizeW_tset)

private theorem implUniEC_compCostW_le (q qep i : ℕ) (hi : i < qep + 2) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let esT := CryptoGames.SM.Construction.fsEsTy KC Γ CCoins T I KR RSt K SS RS M E
    let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
    compCostW (ckaOpC B) ckaSampC fsQueryC
      (CryptoGames.SM.Construction.implUniEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps i
        (Γ' := [esT, smqT]) .v0 .v1) + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B esT smqT
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, none, i⟩
  let mo_pol : CryptoGames.SM.Construction.Mode :=
    ⟨false, if 2 + 1 ≤ i then some (i - (2 + 1)) else none, i⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hi_bits := bits_le_bits_qep_add (x := i) (qep := qep) (by omega)
  have hhkC := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B mo 0).mono
    (H' := 320 * L + 10 * bits qep + B + 2500)
    (by dsimp [mo, CryptoGames.SM.Construction.Mode.tH, healEpoch] at *; omega)
  have hhkE := (hooksFSC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B L B mo 0).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000)
    (Hr' := 500 * L + 40 * B + 6 * bits B + 5700000)
    (by omega) (by decide) (by omega)
  have htL_pol : mo_pol.tL.getD 0 < qep + 2 := by
    dsimp only [mo_pol]; split_ifs <;> (simp; try omega)
  have h500 : compCostW (ckaOpC B) ckaSampC fsQueryC
      (CryptoGames.SM.Engine.implEC
        (CryptoGames.SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
          (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B 1 mo 0)
        L (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo_pol) mo_pol.policy
        (Γ' := [esT, smqT]) .v0 .v1) + 500000 ≤ fig8AtomicStepBound q qep :=
    implEC_any_compCostW_le_qep _ q qep mo_pol .v0 .v1
      (by simp [Expr.cost, v0_cost]) (by simp [Expr.cost, v1_cost])
      (by simp [exprExcessUB_v0]) (by simp [exprExcessUB_v1])
      hi htL_pol hhkC hhkE
  dsimp only [CryptoGames.SM.Construction.implUniEC]
  exact (Nat.add_le_add_left (by decide : 200000 ≤ 500000) _).trans h500

private theorem implUniEC_sizeW_le (q qep i : ℕ) (hi : i < qep + 2)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let esT := CryptoGames.SM.Construction.fsEsTy KC Γ CCoins T I KR RSt K SS RS M E
    let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.implUniEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps i
        (Γ' := [esT, smqT]) .v0 .v1) ≤
      960 * bits (ratchetCostBudget q qep) + 240000 := by
  intro L B esT smqT
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, none, i⟩
  let mo_pol : CryptoGames.SM.Construction.Mode :=
    ⟨false, if 2 + 1 ≤ i then some (i - (2 + 1)) else none, i⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hb0 : bits 0 ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbi : bits i ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hhkS := (hooksFSC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B L B mo 0).mono
    (Ho' := 80 * bits (ratchetCostBudget q qep) + 15000) (Hs' := 2000)
    (Hr' := 14 * bits (ratchetCostBudget q qep) + 5000)
    (by dsimp [mo, L, CryptoGames.SM.Construction.Mode.tH, healEpoch] at *; omega) le_rfl
    (by dsimp [L] at *; omega)
  have htL_pol : mo_pol.tL.getD 0 ≤ qep + 2 := by
    dsimp only [mo_pol]
    by_cases h : 2 + 1 ≤ i
    · simp [h]; omega
    · simp [h]
  have h800 : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Engine.implEC
        (CryptoGames.SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
          (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B 1 mo 0)
        L (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo_pol) mo_pol.policy
        (Γ' := [esT, smqT]) .v0 .v1) ≤ 800 * bits (ratchetCostBudget q qep) + 200200 :=
    implEC_any_sizeW_le_qep _ q qep mo_pol .v0 .v1
      (by simp [exprSizeW_v0]) (by simp [exprSizeW_v1])
      hi htL_pol hqep hhkS
  exact h800.trans (by omega)

private theorem redFSPrivUniCoinProg_parts_le (q qep i : ℕ) (hi : i < qep + 2) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSPrivUniCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps i
    compCostW (ckaOpC B) ckaSampC fsQueryC P.init +
        compCostW (ckaOpC B) ckaSampC fsQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC fsQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  have hnone : (none : Option ℕ) ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i := by
    simp [CryptoGames.SM.admissibleLastLeakGuesses]
  refine ⟨?_, implUniEC_compCostW_le q qep i hi⟩
  exact (redFSPrivCoinProg_parts_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) q qep i none hi hnone).1

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
private theorem redFSPrivUniProg_parts_le (q qep i : ℕ) (hi : i < qep + 2) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSPrivUniProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps i
    compCostW (ckaOpC B) ckaSampC fsQueryC P.init +
        compCostW (ckaOpC B) ckaSampC fsQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC fsQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  refine ⟨?_, implUniEC_compCostW_le q qep i hi⟩
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, none, i⟩
  have hi_bits := bits_le_bits_qep_add (x := i) (qep := qep) (by omega)
  have hiW : compCostW (ckaOpC B) ckaSampC fsQueryC P.init ≤ 4 * bits qep + 500 * L + 8000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivUniProg]
    have hiC0 := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo 0 (Γ' := [.unit]) (.bool false)
    have hiE0 := initFSEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B L mo 0 (Γ' := [.unit]) (.bool false)
    dsimp only [mo, CryptoGames.SM.Construction.Mode.tH, healEpoch] at hiC0 hiE0
    refine compCostW_le_of_parts (a := 200 * L + 2 * bits i + 2050) (b := 200 * L + 5100) ?_ ?_ (by omega)
    · simp only [Comp.cost, Expr.cost, v0_cost, bits_zero, Nat.reduceAdd] at hiC0 ⊢; omega
    · simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit,
        exprExcessUB_v0, exprExcessUB_bool, Nat.reduceAdd] at hiE0 ⊢; omega
  have hfW : compCostW (ckaOpC B) ckaSampC fsQueryC P.finish ≤ 4 * bits qep + 100 * L + 500 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivUniProg]
    rw [show (2 : ℕ) + 1 = 3 from rfl]
    refine compCostW_le_of_parts (a := 3 * bits i + 80 * L + 200) (b := 220) ?_ ?_ (by omega)
    · refine (compCost_le_costUB _).trans ?_
      have hb3 : bits 3 = 2 := rfl
      simp only [CryptoGames.SM.Construction.privValidUniE, CryptoGames.SM.Engine.cCanonE,
        CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE,
        CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.Engine.esAbort,
        CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.cGsLeaks,
        CryptoGames.PRFPRNG.fsaeadHeaderAdIface, CryptoGames.CKA.ckaSamplers,
        Expr.v0, Expr.v1, Expr.v2, dsl_cost, hb3, Nat.reduceAdd]
      omega
    · simp only [CryptoGames.SM.Construction.privValidUniE, CryptoGames.SM.Engine.cCanonE,
        CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE,
        CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.Engine.esAbort,
        CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.cGsLeaks, ckaSampC,
        compExcessUB_ite, compExcessUB_ret, compExcessUB_sample,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var,
        exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_lt,
        exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
        exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
        exprExcessUB_caseOpt, exprExcessUB_letE,
        Computational.Proofs.ReductionDsl.Fig8ExcessCosts.exprExcessUB_add,
        Computational.Proofs.ReductionDsl.Fig8ExcessCosts.exprExcessUB_foldrB, Nat.reduceAdd]
      omega
  unfold fig8AtomicStepBound
  dsimp only [L, B] at hiW hfW ⊢
  omega

private theorem redFSPrivUniCoinProg_size_le (q qep i : ℕ) (hi : i < qep + 2)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSPrivUniCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps i
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, none, i⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hb0 : bits 0 ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbi : bits i ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch none) ≤ _; simp only [healEpoch]; exact hb0
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hiS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivUniCoinProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo 0 (.bool false)) ?_
    have hmS : mo.tStar = i := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hhS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      960 * bits (ratchetCostBudget q qep) + 240000 :=
    implUniEC_sizeW_le q qep i hi hqep
  have hfS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤ 20 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivUniCoinProg]
    simp only [Bundles.ckaSampS, compSizeW_sample, exprSizeW_unit, Nat.reduceAdd]; omega
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by decide) (by decide) ?_; omega

set_option linter.unusedSimpArgs false in
private theorem redFSPrivUniProg_size_le (q qep i : ℕ) (hi : i < qep + 2)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := CryptoGames.SM.Construction.redFSPrivUniProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B 1 qep maxForwardJumps i
    Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 400 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  intro B P
  let mo : CryptoGames.SM.Construction.Mode := ⟨false, none, i⟩
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hb0 : bits 0 ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbi : bits i ≤ bits (ratchetCostBudget q qep) := bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits mo.tH ≤ bits (ratchetCostBudget q qep) := by
    change bits (healEpoch none) ≤ _; simp only [healEpoch]; exact hb0
  have hbB : bits B ≤ bits (ratchetCostBudget q qep) := bits_B0_le_ratchetCostBudget q qep
  have hiS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      45 * bits (ratchetCostBudget q qep) + 15000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivUniProg]
    refine bind_ret_pair_unit_sizeW_le (initFSEStateC_sizeW_le B (q + 1) mo 0 (.bool false)) ?_
    have hmS : mo.tStar = i := rfl; rw [hmS]; simp only [exprSizeW_bool]; omega
  have hhS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      960 * bits (ratchetCostBudget q qep) + 240000 :=
    implUniEC_sizeW_le q qep i hi hqep
  have hfS : Bundles.compSizeW (Bundles.ckaOpS B) Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      20 * bits (ratchetCostBudget q qep) + 1000 := by
    dsimp only [P, CryptoGames.SM.Construction.redFSPrivUniProg]
    rw [show (2 : ℕ) + 1 = 3 from rfl]
    simp only [CryptoGames.SM.Construction.privValidUniE, CryptoGames.SM.Engine.cCanonE,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.Engine.esAbort,
      CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.cGsLeaks, Bundles.ckaSampS,
      compSizeW_ite, compSizeW_ret, compSizeW_sample,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_add,
      exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
      exprSizeW_foldrB, bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
    omega
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by decide) (by decide) ?_; omega

private theorem redFSPrivUniProg_totalQueries_le (L B Δcka qep maxSkip i q : ℕ) :
    (CryptoGames.SM.Construction.redFSPrivUniProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip i).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  simp [CostedReduction.totalQueries, CryptoGames.SM.Construction.redFSPrivUniProg,
    CryptoGames.SM.Construction.implUniEC,
    CryptoGames.SM.Construction.initFSEStateC_queries,
    CryptoGames.SM.Engine.implEC, CryptoGames.SM.Engine.transmitEC, CryptoGames.SM.Engine.challEC,
    CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Engine.corrEC,
    CryptoGames.SM.Engine.vSendC, CryptoGames.SM.Engine.vSendStep1C,
    CryptoGames.SM.Engine.vRecvC, CryptoGames.SM.Engine.vRecvStep1C,
    CryptoGames.SM.Engine.commitEC, CryptoGames.SM.Construction.hooksFSC,
    Comp.queries]
  omega

private theorem redFSPrivUniCoinProg_totalQueries_le (L B Δcka qep maxSkip i q : ℕ) :
    (CryptoGames.SM.Construction.redFSPrivUniCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip i).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  simp [CostedReduction.totalQueries, CryptoGames.SM.Construction.redFSPrivUniCoinProg,
    CryptoGames.SM.Construction.implUniEC,
    CryptoGames.SM.Construction.initFSEStateC_queries,
    CryptoGames.SM.Engine.implEC, CryptoGames.SM.Engine.transmitEC, CryptoGames.SM.Engine.challEC,
    CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Engine.corrEC,
    CryptoGames.SM.Engine.vSendC, CryptoGames.SM.Engine.vSendStep1C,
    CryptoGames.SM.Engine.vRecvC, CryptoGames.SM.Engine.vRecvStep1C,
    CryptoGames.SM.Engine.commitEC, CryptoGames.SM.Construction.hooksFSC,
    Comp.queries]
  omega

end FSPrivUniParts

end EngineSizeParts

namespace PrngPrivQepPotOK

set_option linter.unusedSimpArgs false

open _root_.ReductionDsl (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction handlerImpl
  isGameQuery)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CKA (CKASamp CKAOp ckaSMQ ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngIface)
open _root_.CryptoGames.SM (Adversary MakesAtMostQueries posTy posEpoch partyEnc partyDec
  partyDec_partyEnc sendsInE otherE pGet pSet maxN_eval orE isSomeE letE_eval ite_eval some_eval
  sendsInE_eval)
open _root_.CryptoGames.SM.Engine (ConfigEC Policy modeCfgEC cRecTy cGsTy esG esH esAbort esMk
  esSetG esSetH esSetAbort cGsSt cGsEpoch cGsTrans cGsWin cGsB cGsMk cGsSetStP cGsSetWin cRecPos
  cRecCt hdrCtEqE cLeakE cEpMgmtE cDeleteE cAcceptE cRecordE cAfterCorrE cInTransitE privOutC
  mkPartiesE cGsInitE vpMk vpId vpTcurNat vpΓ vpRoot vpSetVS vpSetVR vSendStep1C vSendC vRecvStep1C
  vRecvC commitEC transmitEC challEC deliverEC injectEC corrEC implEC eval_bind eval_bind_ret
  eval_ret)
open _root_.CryptoGames.SM.Construction (Header PartyState Mode prngHsTy prngVpTy prngEsTy rootPRNGC
  rootPRNGC_queries prngStartSendC_queries prngStartRecvC prngFsSendC prngFsRecvC prngCommitC
  prngRevealC_queries hooksPRNGC initPRNGEStateC redPRNGPrivProg)
open Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK (pGet_eval_st_prng pSet_eval_st_prng
  cLeakE_st_prng cAcceptE_st_prng cGsSetStP_st_prng cGsSetWin_st_prng cRecordE_st_prng
  cAfterCorrE_st_prng isQueryBoundP_min_prng prngIface_fwdU_zero ite_fst_eq_prng
  prngStartRecvC_potOKS redPRNGPrivProg_makesAtMostQueries_q3)


variable
  {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "P_prng" => isGameQuery (G := _root_.CryptoGames.PRFPRNG.spec RSt I K)
private structure PotOKInv {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α : Type}
    (P : ι' → Prop) [DecidablePred P] (Inv : α → Prop) (B : α → ℕ)
    (oa : OracleComp T' α) (n : ℕ) : Prop where
  run : ∀ {β : Type} (k : α → OracleComp T' β),
    (∀ a, Inv a → (k a).IsQueryBoundP P (B a)) → (oa >>= k).IsQueryBoundP P n
private theorem PotOKInv.mono {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α : Type}
    {P : ι' → Prop} [DecidablePred P] {Inv : α → Prop} {B : α → ℕ}
    {oa : OracleComp T' α} {n₁ n₂ : ℕ} (h : PotOKInv P Inv B oa n₁) (hle : n₁ ≤ n₂) :
    PotOKInv P Inv B oa n₂ := ⟨fun k hk => (h.run k hk).mono hle⟩
private theorem PotOKInv.bindPot {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type} {P : ι' →
    Prop} [DecidablePred P] {Inv₁ : α → Prop} {Inv₂ : γ → Prop} {B₁ : α → ℕ} {B₂ : γ → ℕ} {oa :
    OracleComp T' α} {f : α → OracleComp T' γ} {n : ℕ} (h1 : PotOKInv P Inv₁ B₁ oa n) (h2 : ∀ a,
    Inv₁ a → PotOKInv P Inv₂ B₂ (f a) (B₁ a)) : PotOKInv P Inv₂ B₂ (oa >>= f) n :=
  ⟨fun k hk => by rw [bind_assoc]; exact h1.run _ (fun a ha => (h2 a ha).run k hk)⟩
private theorem PotOKInv.bindSupp {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type} {P : ι' →
    Prop} [DecidablePred P] {Inv : γ → Prop} {B : γ → ℕ} {oa : OracleComp T' α} {f : α → OracleComp
    T' γ} {m r n : ℕ} (hoa : oa.IsQueryBoundP P m) (hf : ∀ a ∈ support oa, PotOKInv P Inv B (f a) r)
    (hmn : m + r ≤ n) : PotOKInv P Inv B (oa >>= f) n :=
  ⟨fun k hk => by
    rw [bind_assoc]; exact (isQueryBoundP_bind hoa (fun a ha => (hf a ha).run k hk)).mono hmn⟩
private theorem potInv_ret {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {O' : Ops S'} {I' :
    Iface S' T'} {P : ι' → Prop} [DecidablePred P] {Γ' : List (Ty S')} {τ : Ty S'} {Inv : τ.denote →
    Prop} {B : τ.denote → ℕ} {e : Expr O' Γ' τ} {ρ : Env Γ'} {n : ℕ} (hInv : Inv (e.eval ρ)) (hB : B
    (e.eval ρ) ≤ n) : PotOKInv P Inv B ((Comp.ret (I := I') e).eval ρ) n :=
  ⟨fun _ hk => by rw [eval_ret, pure_bind]; exact (hk (e.eval ρ) hInv).mono hB⟩
private theorem potInv_ite {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {O' : Ops S'} {I' :
    Iface S' T'} {P : ι' → Prop} [DecidablePred P] {Γ' : List (Ty S')} {τ : Ty S'} {Inv : τ.denote →
    Prop} {B : τ.denote → ℕ} {cond : Expr O' Γ' .bool} {t f : Comp O' I' Γ' τ} {ρ : Env Γ'} {n : ℕ}
    (ht : cond.eval ρ = true → PotOKInv P Inv B (t.eval ρ) n) (hf : cond.eval ρ = false → PotOKInv P
    Inv B (f.eval ρ) n) : PotOKInv P Inv B ((Comp.ite cond t f).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases hc : cond.eval ρ
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact (hf hc).run k hk
    · simp only [↓reduceIte]; exact (ht hc).run k hk⟩
private theorem potInv_caseOpt {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {O' : Ops S'} {I'
    : Iface S' T'} {P : ι' → Prop} [DecidablePred P] {Γ' : List (Ty S')} {α τ : Ty S'} {Inv :
    τ.denote → Prop} {B : τ.denote → ℕ} {scrut : Expr O' Γ' (.opt α)} {onNone : Comp O' I' Γ' τ}
    {onSome : Comp O' I' (α :: Γ') τ} {ρ : Env Γ'} {n : ℕ} (hNone : scrut.eval ρ = none → PotOKInv P
    Inv B (onNone.eval ρ) n) (hSome : ∀ v, scrut.eval ρ = some v → PotOKInv P Inv B (onSome.eval
    (.cons v ρ)) n) : PotOKInv P Inv B ((Comp.caseOpt scrut onNone onSome).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases h : scrut.eval ρ with
    | none => exact (hNone h).run k hk
    | some v => exact (hSome v h).run k hk⟩
private theorem potInv_caseSum {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {O' : Ops S'} {I'
    : Iface S' T'} {P : ι' → Prop} [DecidablePred P] {Γ' : List (Ty S')} {α β τ : Ty S'} {Inv :
    τ.denote → Prop} {B : τ.denote → ℕ} {scrut : Expr O' Γ' (.sum α β)} {onInl : Comp O' I' (α ::
    Γ') τ} {onInr : Comp O' I' (β :: Γ') τ} {ρ : Env Γ'} {n : ℕ} (hInl : ∀ v, scrut.eval ρ = .inl v
    → PotOKInv P Inv B (onInl.eval (.cons v ρ)) n) (hInr : ∀ v, scrut.eval ρ = .inr v → PotOKInv P
    Inv B (onInr.eval (.cons v ρ)) n) : PotOKInv P Inv B ((Comp.caseSum scrut onInl onInr).eval ρ) n
    :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases h : scrut.eval ρ with
    | inl v => exact (hInl v h).run k hk
    | inr v => exact (hInr v h).run k hk⟩
private theorem potOKInv_simulateQ_handlerImpl_c0 {S' : Sig} {O' : Ops S'} {ι' : Type} {T' :
    OracleSpec.{0, 0} ι'} {I' : Iface S' T'} {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S'
    G} {σ : Ty S'} {α : Type} {P : ι' → Prop} [DecidablePred P] (Inv : σ.denote → Prop) (B :
    σ.denote → ℕ) (hU : ∀ n, (I'.fwdU n).IsQueryBoundP P 0) (h : Comp O' I' [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ q s, Inv s → PotOKInv P (fun x : C.R.denote × σ.denote => Inv x.2) (fun x => B x.2)
    (h.eval (.cons s (.cons q .nil))) (B s)) (mx : OracleComp (unifSpec + G) α) {st : σ.denote} (hst
    : Inv st) : PotOKInv P (fun x : α × σ.denote => Inv x.2) (fun _ => 0) ((simulateQ (handlerImpl
    (C := C) h) mx).run st) (B st) := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact ⟨fun k hk => by simpa using (hk (a, st) hst).mono (Nat.zero_le (B st))⟩
  | query_bind q k ih =>
    rw [simulateQ_query_bind, StateT.run_bind]; rcases q with uq | gq
    · change PotOKInv P _ _
        ((do let u ← I'.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) (B st)
      rw [bind_assoc]
      refine PotOKInv.bindSupp (hU uq) (fun u _ => ?_) (Nat.zero_add (B st)).le
      rw [pure_bind]; exact ih u hst
    · change PotOKInv P _ _
        ((do let p ← h.eval (.cons st (.cons (C.qenc gq) .nil)); return (C.rdec gq p.1, p.2)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) (B st)
      rw [bind_assoc]
      refine PotOKInv.bindPot (hStep (C.qenc gq) st hst) (fun p hp => ?_)
      rw [pure_bind]; exact ih (C.rdec gq p.1) hp
private def prngPrivPartyCount (P : Party) (e : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => prngPrivPartyCount P e k + (if P.sendsIn (k + 1) && decide (e < k + 1) then 1 else 0)
private theorem party_sendsIn_succ_partition (k : ℕ) : (if Party.A.sendsIn (k + 1) then 1 else 0) +
    (if Party.B.sendsIn (k + 1) then 1 else 0) = 1 := by
  cases hA : Party.A.sendsIn (k + 1) <;> cases hB : Party.B.sendsIn (k + 1)
  · exfalso; simp [Party.sendsIn] at hA hB; omega
  · rfl
  · rfl
  · exfalso; simp [Party.sendsIn] at hA hB; omega
private theorem prngPrivPartyCount_zero_sum (qep : ℕ) : prngPrivPartyCount .A 0 qep +
    prngPrivPartyCount .B 0 qep = qep := by
  induction qep with
  | zero => rfl
  | succ k ih =>
    have hp := party_sendsIn_succ_partition k
    simp only [prngPrivPartyCount, Nat.zero_lt_succ, decide_true, Bool.and_true]; omega
private theorem prngPrivPartyCount_anti (P : Party) {e₁ e₂ : ℕ} (hle : e₁ ≤ e₂) (qep : ℕ) :
    prngPrivPartyCount P e₂ qep ≤ prngPrivPartyCount P e₁ qep := by
  induction qep with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [prngPrivPartyCount]; refine Nat.add_le_add ih ?_
    by_cases hk2 : e₂ < k + 1
    · have hk1 : e₁ < k + 1 := Nat.lt_of_le_of_lt hle hk2; simp [hk1, hk2]
    · simp [hk2]
private theorem prngPrivPartyCount_step (P : Party) (e qep : ℕ) (hs : P.sendsIn (e + 1) = true) (hle
    : e + 1 ≤ qep) : prngPrivPartyCount P (e + 1) qep + 1 ≤ prngPrivPartyCount P e qep := by
  induction qep with
  | zero => omega
  | succ k ih =>
    by_cases heq : e = k
    · subst heq
      have hanti := prngPrivPartyCount_anti P (show e ≤ e + 1 by omega) e
      simp only [prngPrivPartyCount, hs, Nat.lt_succ_self, Nat.lt_irrefl, decide_true, decide_false,
        Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      omega
    · have ih' := ih (by omega)
      have hk1 : e < k + 1 := by omega
      have hk2 : e + 1 < k + 1 := by omega
      simp only [prngPrivPartyCount, hk1, hk2, decide_true, Bool.and_true]; omega
private def prngPrivVpPot (qep : ℕ) (vp : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : ℕ
    :=
  2 * prngPrivPartyCount (partyDec vp.1) vp.2.2.2.2.2.2 qep
private def prngPrivPot (qep : ℕ) (es : (@prngEsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : ℕ
    :=
  if es.2.2 then 0 else prngPrivVpPot qep es.1.1.1 + prngPrivVpPot qep es.1.1.2
private def prngPrivOtherPot (qep : ℕ) (stAB : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote
    × (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (p : Bool) : ℕ :=
  if p then prngPrivVpPot qep stAB.1 else prngPrivVpPot qep stAB.2
private theorem prngPrivOtherPot_add_pGet (qep : ℕ) (stAB : (@prngVpTy KC Γ CCoins T I KR RSt K SS
    RS M E).denote × (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (p : Bool) :
    prngPrivOtherPot qep stAB p + prngPrivVpPot qep (if p then stAB.2 else stAB.1) = prngPrivVpPot
    qep stAB.1 + prngPrivVpPot qep stAB.2 := by
  cases p <;> simp [prngPrivOtherPot, Nat.add_comm]
private theorem prngPrivPot_pSet_eq (qep : ℕ) (stAB : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M
    E).denote × (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (p : Bool) (vp' : (@prngVpTy
    KC Γ CCoins T I KR RSt K SS RS M E).denote) : (let st' := if p then (stAB.1, vp') else (vp',
    stAB.2); prngPrivVpPot qep st'.1 + prngPrivVpPot qep st'.2) = prngPrivOtherPot qep stAB p +
    prngPrivVpPot qep vp' := by
  cases p <;> simp [prngPrivOtherPot, Nat.add_comm]
private theorem prngPrivPot_mk_eq (qep : ℕ) {g1 g2 : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E
    prngVpTy).denote} {h1 h2 : (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote} {ab : Bool}
    (hst : g1.1 = g2.1) : prngPrivPot qep (g1, h1, ab) = prngPrivPot qep (g2, h2, ab) := by
  simp only [prngPrivPot, hst]
private def prngGsInv (g : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E prngVpTy).denote) : Prop :=
  g.1.1.1 = false ∧ g.1.2.1 = true ∧
  g.1.1.2.2.2.2.2.2 ≤ g.2.2.2.1.1 ∧ g.1.2.2.2.2.2.2.2 ≤ g.2.2.2.1.2 ∧
  ∀ r ∈ g.2.2.2.2.2.2.1, r.2.2.1.1 ≤ r.1.2.1
private def prngPrivInv (es : (@prngEsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : Prop :=
  es.2.2 = false → prngGsInv es.1
private theorem prngPrivInv_abort {g : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E prngVpTy).denote}
    {h : (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote} :
    prngPrivInv (g, h, true) := fun hab => by cases hab
private theorem prngGsInv_of_fields_eq {g₁ g₂ : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E
    prngVpTy).denote} (hSt : g₁.1 = g₂.1) (hEp : g₁.2.2.2.1 = g₂.2.2.2.1) (hTr : ∀ r ∈
    g₁.2.2.2.2.2.2.1, r ∈ g₂.2.2.2.2.2.2.1) (hg : prngGsInv g₂) : prngGsInv g₁ :=
  ⟨by rw [hSt]; exact hg.1, by rw [hSt]; exact hg.2.1,
   by rw [hSt, hEp]; exact hg.2.2.1, by rw [hSt, hEp]; exact hg.2.2.2.1,
   fun r hr => hg.2.2.2.2 r (hTr r hr)⟩
private theorem prngGsInv_ite {P_cond : Prop} [Decidable P_cond] {g₁ g₂ : (@cGsTy KC Γ CCoins T I KR
    RSt K SS RS M E prngVpTy).denote} (h₁ : prngGsInv g₁) (h₂ : prngGsInv g₂) : prngGsInv (if P_cond
    then g₁ else g₂) := by
  by_cases hc : P_cond <;> simp [hc, h₁, h₂]
private theorem cGsSetWin_gsInv {O' : Ops S} {Γ' : List (Ty S)} (s : Expr O' Γ' (cGsTy prngVpTy)) (w
    : Expr O' Γ' .bool) (ρ : Env Γ') (hg : prngGsInv (s.eval ρ)) : prngGsInv ((cGsSetWin s w).eval
    ρ) :=
  prngGsInv_of_fields_eq
    (by simp [cGsSetWin, letE_eval, cGsMk, cGsSt, Expr.eval, Expr.v0])
    (by simp [cGsSetWin, letE_eval, cGsMk, cGsEpoch, Expr.eval, Expr.v0])
    (fun _ hr => by simpa [cGsSetWin, letE_eval, cGsMk, cGsTrans, Expr.eval, Expr.v0] using hr) hg
private theorem cLeakE_priv_fields {O' : Ops S} {Γ' : List (Ty S)} (s : Expr O' Γ' (cGsTy prngVpTy))
    (l : Expr O' Γ' .nat) (ρ : Env Γ') : ((cLeakE s l).eval ρ).1 = (s.eval ρ).1 ∧ ((cLeakE s l).eval
    ρ).2.2.2.1 = (s.eval ρ).2.2.2.1 ∧ ((cLeakE s l).eval ρ).2.2.2.2.2.2.1 = (s.eval ρ).2.2.2.2.2.2.1
    := by
  simp [cLeakE, letE_eval, cGsMk, cGsSt, cGsEpoch, cGsTrans, Expr.eval, Expr.v0]
private theorem cAfterCorrE_gsInv {O' : Ops S} {Γ' : List (Ty S)} (L : ℕ) (s : Expr O' Γ' (cGsTy
    prngVpTy)) (p : Expr O' Γ' .bool) (ρ : Env Γ') (hg : prngGsInv (s.eval ρ)) : prngGsInv
    ((cAfterCorrE L s p).eval ρ) := by
  refine prngGsInv_of_fields_eq ?_ ?_ (fun _ hr => ?_) hg
  · simp [cAfterCorrE, letE_eval, cGsMk, cGsSt, cLeakE_st_prng, Expr.eval, Expr.v0]
  · simp [cAfterCorrE, letE_eval, cGsMk, cGsEpoch, cLeakE, Expr.eval, Expr.v0]
  · simpa [cAfterCorrE, letE_eval, cGsMk, cGsTrans, cLeakE, Expr.eval, Expr.v0] using hr
private theorem cEpMgmtE_some_priv {O' : Ops S} {Γ' : List (Ty S)} (Δ qep : ℕ) (s : Expr O' Γ'
    (cGsTy prngVpTy)) (p bad : Expr O' Γ' .bool) (ρ : Env Γ') {s₁ : (cGsTy prngVpTy).denote} (hg :
    prngGsInv (s.eval ρ)) (h : (cEpMgmtE Δ qep s p bad).eval ρ = some s₁) : s₁.1 = (s.eval ρ).1 ∧
    prngGsInv s₁ ∧ (if (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval ρ).1.1).1 = p.eval ρ ∧ (if
    (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval ρ).1.1).2.2.2.2.2.2 ≤ (if (p.eval ρ : Bool)
    then s₁.2.2.2.1.2 else s₁.2.2.2.1.1) ∧ ((partyDec (if (p.eval ρ : Bool) then (s.eval ρ).1.2 else
    (s.eval ρ).1.1).1).sendsIn ((if (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval
    ρ).1.1).2.2.2.2.2.2 + 1) = true → (if (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval
    ρ).1.1).2.2.2.2.2.2 + 1 ≤ qep ∧ (if (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval
    ρ).1.1).2.2.2.2.2.2 + 1 ≤ (if (p.eval ρ : Bool) then s₁.2.2.2.1.2 else s₁.2.2.2.1.1)) := by
  set g := s.eval ρ; set p0 : Bool := p.eval ρ; set b0 : Bool := bad.eval ρ
  have hvpId : (if p0 then g.1.2 else g.1.1).1 = p0 := by cases p0 <;> simp [hg.1, hg.2.1]
  have hvpEp : (if p0 then g.1.2 else g.1.1).2.2.2.2.2.2 ≤
      (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) := by cases p0 <;> simp [hg.2.2.1, hg.2.2.2.1]
  unfold cEpMgmtE at h; rw [letE_eval] at h
  have hp0 : (Expr.pair s (.pair p bad)).eval ρ = (g, p0, b0) := rfl
  rw [hp0] at h; set ρ₁ := Env.cons (t := .prod (cGsTy prngVpTy) (.prod .bool .bool)) (g, p0, b0) ρ
  rw [ite_eval] at h
  have hSends : (sendsInE (.fst (.snd (Expr.v0 (O := O')))) (.add (pGet (cGsEpoch (.fst (Expr.v0 (O
    := O')))) (.fst (.snd (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ =
      (partyDec p0).sendsIn ((if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1) := by
    rw [sendsInE_eval _ _ ρ₁ (partyDec p0) (by simp [ρ₁, Expr.eval, Expr.v0])]
    simp [ρ₁, pGet_eval_st_prng, cGsEpoch, Expr.eval, Expr.v0]; rfl
  rw [hSends] at h
  by_cases h1 : (partyDec p0).sendsIn ((if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1) = true
  · simp only [h1, ↓reduceIte, ite_eval] at h
    have hlt1 : (Expr.lt (.nat qep) (.add (pGet (cGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd
        (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ = decide (qep < (if p0 then g.2.2.2.1.2 else
        g.2.2.2.1.1) + 1) := by
      simp [ρ₁, pGet_eval_st_prng, cGsEpoch, Expr.eval, Expr.v0]; exact Iff.rfl
    rw [hlt1] at h
    by_cases h2 : qep < (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1
    · simp [h2, Expr.eval] at h
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, letE_eval, some_eval,
      Option.some.injEq] at h
      set s_mid := (Expr.ite _ (cLeakE _ _) (.fst .v0)).eval ρ₁
      have hmid : s_mid.1 = g.1 ∧ s_mid.2.2.2.1 = g.2.2.2.1 ∧ s_mid.2.2.2.2.2.2.1 = g.2.2.2.2.2.2.1
          := by
        dsimp only [s_mid]; rw [ite_eval]; split_ifs
        · exact cLeakE_priv_fields _ _ ρ₁
        · exact ⟨rfl, rfl, rfl⟩
      have hSt : s₁.1 = g.1 := by rw [← h]; simp [cGsMk, cGsSt, Expr.eval, Expr.v0, hmid.1]
      have hEpA : s₁.2.2.2.1 = if p0 then (g.2.2.2.1.1, g.2.2.2.1.2 + 1) else (g.2.2.2.1.1 + 1,
          g.2.2.2.1.2) := by
        rw [← h]; cases hp0_val : p0 <;>
          simp [ρ₁, hp0_val, cGsMk, cGsEpoch, pSet_eval_st_prng, pGet_eval_st_prng,
            Expr.eval, Expr.v0, Expr.v1, hmid.2.1]
      have hTr : s₁.2.2.2.2.2.2.1 = g.2.2.2.2.2.2.1 := by
        rw [← h]; simp [cGsMk, cGsTrans, Expr.eval, Expr.v0, hmid.2.2]
      refine ⟨hSt, ?_, hvpId, ?_, fun _ => ?_⟩
      · refine ⟨by rw [hSt]; exact hg.1, by rw [hSt]; exact hg.2.1, ?_, ?_,
          fun r hr => hg.2.2.2.2 r (by rwa [hTr] at hr)⟩
        · rw [hSt, hEpA]; cases p0
          · exact Nat.le_trans hg.2.2.1 (Nat.le_succ _)
          · exact hg.2.2.1
        · rw [hSt, hEpA]; cases p0
          · exact hg.2.2.2.1
          · exact Nat.le_trans hg.2.2.2.1 (Nat.le_succ _)
      · rw [hEpA]; cases hp0_val : p0 <;>
          (rw [hp0_val] at hvpEp; exact Nat.le_trans hvpEp (Nat.le_succ _))
      · rw [hEpA]
        have h2' : (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1 ≤ qep := Nat.le_of_not_lt h2
        cases hp0_val : p0
        · rw [hp0_val] at hvpEp h2'
          exact ⟨Nat.le_trans (Nat.add_le_add_right hvpEp 1) h2', Nat.add_le_add_right hvpEp 1⟩
        · rw [hp0_val] at hvpEp h2'
          exact ⟨Nat.le_trans (Nat.add_le_add_right hvpEp 1) h2', Nat.add_le_add_right hvpEp 1⟩
  · have h1f : (partyDec p0).sendsIn ((if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1) = false :=
      Bool.eq_false_iff.mpr h1
    simp only [h1f, Bool.false_eq_true, ↓reduceIte, ite_eval] at h
    have hlt2 : (Expr.lt (.nat qep) (pGet (cGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0
        (O := O')))))).eval ρ₁ = decide (qep < (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1)) := by
      simp [ρ₁, pGet_eval_st_prng, cGsEpoch, Expr.eval, Expr.v0]; exact Iff.rfl
    rw [hlt2] at h
    by_cases h2 : qep < (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1)
    · simp [h2, Expr.eval] at h
    · simp only [ρ₁, h2, decide_false, Bool.false_eq_true, ↓reduceIte, Expr.eval, Expr.v0,
      Env.get_cons_zero, Option.some.injEq] at h
      subst h; refine ⟨rfl, hg, hvpId, hvpEp, fun hsVp => ?_⟩; rw [hvpId] at hsVp
      have hne : (if p0 then g.1.2 else g.1.1).2.2.2.2.2.2 ≠
          (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) := fun heq => h1 (heq ▸ hsVp)
      have hlt_ep := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hvpEp hne)
      exact ⟨Nat.le_trans hlt_ep (Nat.le_of_not_lt h2), hlt_ep⟩
private theorem cRecordE_gsInv {O' : Ops S} {Γ' : List (Ty S)} (L Δ : ℕ) (s : Expr O' Γ' (cGsTy
    prngVpTy)) (p : Expr O' Γ' .bool) (st' : Expr O' Γ' prngVpTy) (r : Expr O' Γ' cRecTy) (isChall :
    Expr O' Γ' .bool) (ρ : Env Γ') (hs : prngGsInv (s.eval ρ)) (hp : (st'.eval ρ).1 = p.eval ρ)
    (hstEp : (st'.eval ρ).2.2.2.2.2.2 ≤ (if (p.eval ρ : Bool) then (s.eval ρ).2.2.2.1.2 else (s.eval
    ρ).2.2.2.1.1)) (hr : (r.eval ρ).2.2.1.1 ≤ (r.eval ρ).1.2.1) : prngGsInv ((cRecordE L Δ s p st' r
    isChall).eval ρ) := by
  have hSt := cRecordE_st_prng L Δ s p st' r isChall ρ
  have hEp : ((cRecordE L Δ s p st' r isChall).eval ρ).2.2.2.1 = (s.eval ρ).2.2.2.1 := by
    simp [cRecordE, letE_eval, cGsMk, cGsEpoch, Expr.eval, Expr.v0]
  have hTr : ((cRecordE L Δ s p st' r isChall).eval ρ).2.2.2.2.2.2.1 = (r.eval ρ) :: (s.eval
      ρ).2.2.2.2.2.2.1 := by
    simp [cRecordE, letE_eval, cGsMk, cGsTrans, Expr.eval, Expr.v0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hSt]; cases hp0 : (p.eval ρ : Bool) <;> simp [hp0, hp, hs.1]
  · rw [hSt]; cases hp0 : (p.eval ρ : Bool) <;> simp [hp0, hp, hs.2.1]
  · rw [hSt, hEp]; cases hp0 : (p.eval ρ : Bool) <;> simp [hp0] at hstEp ⊢
    · exact hstEp
    · exact hs.2.2.1
  · rw [hSt, hEp]; cases hp0 : (p.eval ρ : Bool) <;> simp [hp0] at hstEp ⊢
    · exact hs.2.2.2.1
    · exact hstEp
  · rw [hTr]; rintro x hx; rcases List.mem_cons.mp hx with rfl | hmem
    · exact hr
    · exact hs.2.2.2.2 x hmem
private theorem find?_eq_some_mem_and {α : Type} {ls : List α} {p : α → Bool} {x : α} (h : ls.find?
    p = some x) : x ∈ ls ∧ p x = true := by
  induction ls with
  | nil => cases h
  | cons hd tl ih =>
    simp only [List.find?] at h
    cases hp : p hd
    · simp only [hp] at h; obtain ⟨hm, hpx⟩ := ih h; exact ⟨List.mem_cons_of_mem hd hm, hpx⟩
    · simp only [hp, Option.some.injEq] at h; subst h; exact ⟨List.mem_cons_self, hp⟩
private theorem foldr_filter_acc_mem {α : Type} (ls : List α) (f : α → List α → Bool) {x : α} (hx :
    x ∈ ls.foldr (fun r acc => if f r acc then r :: acc else acc) []) : x ∈ ls := by
  induction ls with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.foldr_cons] at hx; split_ifs at hx
    · rcases List.mem_cons.mp hx with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem hd (ih hmem)
    · exact List.mem_cons_of_mem hd (ih hx)
private theorem cInTransitE_some_priv {Γ' : List (Ty S)} (L : ℕ) (s : Expr OO Γ' (cGsTy prngVpTy))
    (qParty : Expr OO Γ' .bool) (c : Expr OO Γ' hdrCtTy) (ρ : Env Γ') {r1 : cRecTy.denote} (hg :
    prngGsInv (s.eval ρ)) (h : (cInTransitE L s qParty c).eval ρ = some r1) : (c.eval ρ).1.1 ≤
    r1.1.2.1 := by
  simp only [cInTransitE, letE_eval, cGsTrans, Expr.eval, Expr.v0, Env.get_cons_zero] at h
  obtain ⟨hmemTake, hpred⟩ := find?_eq_some_mem_and h
  have hrLe : r1.2.2.1.1 ≤ r1.1.2.1 := hg.2.2.2.2 r1 (List.mem_of_mem_take hmemTake)
  simp only [Bool.and_eq_true] at hpred
  have hct := hpred.2
  simp only [hdrCtEqE, letE_eval, cRecCt, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero,
    Env.get_cons_succ, Bool.and_eq_true] at hct
  have heq : r1.2.2.1.1 = (c.eval ρ).1.1 := of_decide_eq_true hct.1.1
  exact heq ▸ hrLe
private theorem cDeleteE_trans_mem {O' : Ops S} {Γ' : List (Ty S)} (L : ℕ) (s : Expr O' Γ' (cGsTy
    prngVpTy)) (pos : Expr O' Γ' posTy) (ρ : Env Γ') {r : cRecTy.denote} (hr : r ∈ ((cDeleteE L s
    pos).eval ρ).2.2.2.2.2.2.1) : r ∈ (s.eval ρ).2.2.2.2.2.2.1 := by
  simp only [cDeleteE, letE_eval, cGsMk, cGsTrans, Expr.eval, Expr.v0, Env.get_cons_zero] at hr
  exact List.mem_of_mem_take (foldr_filter_acc_mem _ _ hr)
private def prngVSendStep1PrivInv (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (ep1
    : ℕ) (res : (Ty.prod (.opt prngVpTy) prngHsTy : Ty S).denote) : Prop :=
  ∀ s1, res.1 = some s1 → s1.1 = s0.1 ∧ s1.2.2.2.2.2.2 ≤ ep1
private def prngVpOptPrivPost (qep m_other : ℕ) (res : (Ty.prod (.opt prngVpTy) prngHsTy : Ty
    S).denote) : ℕ :=
  match res.1 with
  | none => 0
  | some vp' => m_other + prngPrivVpPot qep vp'
private theorem vSendStep1C_priv_potOKInv (B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE
    : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr
    OO Γ' prngVpTy) (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m_other ep1 : ℕ) (hEp0 :
    (sE.eval ρ).2.2.2.2.2.2 ≤ ep1) (hSendQep : (partyDec (sE.eval ρ).1).sendsIn ((sE.eval
    ρ).2.2.2.2.2.2 + 1) = true → (sE.eval ρ).2.2.2.2.2.2 + 1 ≤ qep ∧ (sE.eval ρ).2.2.2.2.2.2 + 1 ≤
    ep1) : PotOKInv P_prng (prngVSendStep1PrivInv (sE.eval ρ) ep1) (prngVpOptPrivPost qep m_other)
    ((vSendStep1C (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) hE ctxE pE sE rE).eval ρ) (m_other +
    prngPrivVpPot qep (sE.eval ρ)) := by
  unfold vSendStep1C; rw [eval_bind_ret]
  refine potInv_ite (fun hs => ?_) (fun _ => ?_)
  · rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at hs
    simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hs
    obtain ⟨hqep, hep1⟩ := hSendQep hs
    have hStep := prngPrivPartyCount_step (partyDec (sE.eval ρ).1) (sE.eval ρ).2.2.2.2.2.2 qep hs hqep
    rw [eval_bind]
    refine PotOKInv.bindSupp
      (r := m_other + 2 * prngPrivPartyCount (partyDec (sE.eval ρ).1)
        ((sE.eval ρ).2.2.2.2.2.2 + 1) qep)
      (Comp.queryBound_eval P_prng (fun _ => 1) (fun _ => 0)
        (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero _ _) (fun _ _ => ?_)
      (by simp only [hooksPRNGC, prngStartSendC_queries, prngPrivVpPot]; omega)
    refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h)
        (by simp [prngVpOptPrivPost, Expr.eval]))
      (fun _ _ => potInv_ret ?_ ?_)
    · intro s1 hs1; simp only [Expr.eval, Option.some.injEq] at hs1; subst hs1
      exact ⟨by simp [vpMk, vpId, Expr.eval, Expr.v0, Expr.v2],
        by simpa [vpMk, vpTcurNat, Expr.eval, Expr.v0, Expr.v2] using hep1⟩
    · simp [prngVpOptPrivPost, prngPrivVpPot, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v2]
  · exact potInv_ret
      (fun s1 hs1 => by
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hs1
        subst hs1; exact ⟨rfl, hEp0⟩)
      (by simp [prngVpOptPrivPost, Expr.eval, Expr.v0])
private def prngVSendPrivInv (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (ep1 : ℕ)
    (res : (Ty.prod (.opt (.prod prngVpTy hdrCtTy)) prngHsTy : Ty S).denote) : Prop :=
  ∀ vp' ct, res.1 = some (vp', ct) → vp'.1 = s0.1 ∧ vp'.2.2.2.2.2.2 ≤ ep1 ∧ ct.1.1 ≤ ep1
private def prngVSendPrivPost (qep m_other : ℕ) (res : (Ty.prod (.opt (.prod prngVpTy hdrCtTy))
    prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => 0
  | some (vp', _) => m_other + prngPrivVpPot qep vp'
private theorem vSendC_priv_potOKInv (B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE :
    Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr OO
    Γ' prngVpTy) (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base
    .msg)))) (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m_other ep1 : ℕ) (hEp0 :
    (sE.eval ρ).2.2.2.2.2.2 ≤ ep1) (hSendQep : (partyDec (sE.eval ρ).1).sendsIn ((sE.eval
    ρ).2.2.2.2.2.2 + 1) = true → (sE.eval ρ).2.2.2.2.2.2 + 1 ≤ qep ∧ (sE.eval ρ).2.2.2.2.2.2 + 1 ≤
    ep1) : PotOKInv P_prng (prngVSendPrivInv (sE.eval ρ) ep1) (prngVSendPrivPost qep m_other)
    ((vSendC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI :=
    sampI) (sampK := sampK) B ⟨false, tL, t⟩) hE ctxE pE sE mE pairE rE).eval ρ) (m_other +
    prngPrivVpPot qep (sE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  have h1 := vSendStep1C_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (.fst (Expr.v0 (O := OO))) (.fst (.snd
    .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd
    (.snd .v0)))))) (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ,
    rE.eval ρ) ρ)
    m_other ep1 (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hEp0)
    (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hSendQep)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at h1
  refine PotOKInv.bindPot h1 (fun step1Out hInv1 => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun s1 hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (fun _ _ h => by simp [Expr.eval] at h)
      (by simp [prngVSendPrivPost, prngVpOptPrivPost, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    obtain ⟨hs1Id, hs1Ep⟩ := hInv1 s1 hSome
    refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · refine potInv_ret ?_ (by simp [prngVSendPrivPost, prngVpOptPrivPost, hSome, Expr.eval, Expr.v0])
      intro vp' ct hEq
      simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq, Prod.mk.injEq]
        at hEq
      rcases hEq with ⟨rfl, hct⟩; rw [← hct]; exact ⟨hs1Id, hs1Ep, hs1Ep⟩
    · rw [eval_bind]; dsimp only [hooksPRNGC, prngFsSendC]; rw [eval_ret, pure_bind]
      refine potInv_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone) (fun _ _ => ?_)
      refine potInv_ret ?_
        (by simp [prngVSendPrivPost, prngVpOptPrivPost, hSome, prngPrivVpPot,
          vpSetVS, letE_eval, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v3])
      intro vp' ct hEq
      simp only [vpSetVS, letE_eval, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v3,
        Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq, Prod.mk.injEq] at hEq
      rcases hEq with ⟨rfl, hct⟩; rw [← hct]; exact ⟨hs1Id, hs1Ep, hs1Ep⟩
private theorem prngStartRecvC_priv_queries_zero (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE :
    Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (tE : Expr OO
    Γ' .nat) (γE : Expr OO Γ' (.base .γ)) (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ'
    (.base .t)) (ρ : Env Γ') : ((prngStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) ⟨false, tL, t⟩ hE ctxE pE tE γE σvE tnE).eval
    ρ).IsQueryBoundP P_prng 0 := by
  have h := (prngStartRecvC_potOKS (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    ⟨false, tL, t⟩ hE ctxE pE tE γE σvE tnE ρ 0).run pure (fun _ => by simp)
  simpa using h
private def prngVRecvStep1PrivInv (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (t0 :
    ℕ) (res : (Ty.prod (.opt (.opt prngVpTy)) prngHsTy : Ty S).denote) : Prop :=
  ∀ s1, res.1 = some (some s1) →
    s1.1 = s0.1 ∧ s0.2.2.2.2.2.2 ≤ s1.2.2.2.2.2.2 ∧
    (s1.2.2.2.2.2.2 = s0.2.2.2.2.2.2 ∨ s1.2.2.2.2.2.2 = t0)
private def prngVRecvStep1PrivPost (qep m_other : ℕ) (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS
    M E).denote) (res : (Ty.prod (.opt (.opt prngVpTy)) prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => 0
  | some none => m_other + prngPrivVpPot qep s0
  | some (some s1) => m_other + max (prngPrivVpPot qep s0) (prngPrivVpPot qep s1)
private theorem vRecvStep1C_priv_potOKInv (B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE
    : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr
    OO Γ' prngVpTy) (cE : Expr OO Γ' hdrCtTy) (ρ : Env Γ') (m_other : ℕ) : PotOKInv P_prng
    (prngVRecvStep1PrivInv (sE.eval ρ) (cE.eval ρ).1.1) (prngVRecvStep1PrivPost qep m_other (sE.eval
    ρ)) ((vRecvStep1C (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) hE ctxE pE sE cE).eval ρ) (m_other +
    prngPrivVpPot qep (sE.eval ρ)) := by
  unfold vRecvStep1C; rw [eval_bind_ret]
  refine potInv_ite (fun ht => ?_) (fun _ => ?_)
  · have ht' : ((cE.eval ρ).1.1 : ℕ) = ((sE.eval ρ).2.2.2.2.2.2 : ℕ) + 1 := of_decide_eq_true ht
    have hle_c : ((sE.eval ρ).2.2.2.2.2.2 : ℕ) ≤ ((cE.eval ρ).1.1 : ℕ) := ht' ▸ Nat.le_succ _
    refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h)
        (by simp [prngVRecvStep1PrivPost, Expr.eval]))
      (fun Tn _ => ?_)
    rw [eval_bind]
    refine PotOKInv.bindSupp
      (prngStartRecvC_priv_queries_zero (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) tL t
        (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
        (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
        (vpΓ (.fst (.snd (.snd (.snd .v1))))) (vpRoot (.fst (.snd (.snd (.snd .v1)))))
        .v0 (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ)))
      (fun _ _ => ?_) (Nat.zero_add _).le
    refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h)
        (by simp [prngVRecvStep1PrivPost, Expr.eval]))
      (fun _ _ => potInv_caseOpt
        (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h)
          (by simp [prngVRecvStep1PrivPost, Expr.eval]))
        (fun _ _ => potInv_ret ?_ ?_))
    · intro s1 hs1; simp only [Expr.eval, Option.some.injEq] at hs1; subst hs1
      exact ⟨by simp [vpMk, vpId, Expr.eval, Expr.v0, Expr.v4],
        by simpa [vpMk, Expr.eval, Expr.v0, Expr.v4] using hle_c,
        Or.inr (by simp [vpMk, Expr.eval, Expr.v0, Expr.v4])⟩
    · have hAnti := prngPrivPartyCount_anti (partyDec (sE.eval ρ).1) hle_c qep
      simp only [prngVRecvStep1PrivPost, prngPrivVpPot, vpMk, vpId, Expr.eval, Expr.v0, Expr.v4,
        Env.get_cons_zero, Env.get_cons_succ]; omega
  · exact potInv_ret
      (fun s1 hs1 => by
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hs1
        subst hs1; exact ⟨rfl, Nat.le_refl _, Or.inl rfl⟩)
      (by simp [prngVRecvStep1PrivPost, Expr.eval, Expr.v0])
private def prngVRecvPrivInv (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (t0 : ℕ)
    (res : (Ty.prod (.opt (.opt (.prod prngVpTy (.prod .nat (.prod .nat (.base .msg)))))) prngHsTy :
    Ty S).denote) : Prop :=
  ∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
    st'.1 = s0.1 ∧ t' = t0 ∧ s0.2.2.2.2.2.2 ≤ st'.2.2.2.2.2.2 ∧
    (st'.2.2.2.2.2.2 = s0.2.2.2.2.2.2 ∨ st'.2.2.2.2.2.2 = t0)
private def prngVRecvPrivPost (qep m_other : ℕ) (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M
    E).denote) (res : (Ty.prod (.opt (.opt (.prod prngVpTy (.prod .nat (.prod .nat (.base .msg))))))
    prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => 0
  | some none => m_other + prngPrivVpPot qep s0
  | some (some (st', _, _, _)) => m_other + max (prngPrivVpPot qep s0) (prngPrivVpPot qep st')
private theorem vRecvC_priv_potOKInv (B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE :
    Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr OO
    Γ' prngVpTy) (cE : Expr OO Γ' hdrCtTy) (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ') (m_other :
    ℕ) : PotOKInv P_prng (prngVRecvPrivInv (sE.eval ρ) (cE.eval ρ).1.1) (prngVRecvPrivPost qep
    m_other (sE.eval ρ)) ((vRecvC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) hE ctxE pE sE cE recE).eval ρ)
    (m_other + prngPrivVpPot qep (sE.eval ρ)) := by
  unfold vRecvC; rw [eval_bind_ret]
  refine potInv_ite
    (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
      (by simp [prngVRecvPrivPost, Expr.eval]))
    (fun _ => ?_)
  rw [eval_bind]
  have hStep1 := vRecvStep1C_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (.fst (Expr.v0 (O := OO))) (.fst (.snd
    .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd (.snd
    .v0))))) (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ)
    m_other
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hStep1
  refine PotOKInv.bindPot hStep1 (fun step1Out hInv1 => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun inner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
      (by simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potInv_caseOpt (fun hInNone => ?_) (fun s1 hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      exact potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
        (by simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hSome, hInNone, Expr.eval])
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      obtain ⟨hs1Id, hs1Le, hs1Cases⟩ := hInv1 s1 (by rw [hSome, hInSome])
      refine potInv_caseOpt
        (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
          (by simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hSome, hInSome, Expr.eval]))
        (fun _ _ => ?_)
      rw [eval_bind]; dsimp only [hooksPRNGC, prngFsRecvC]; rw [eval_ret, pure_bind]
      refine potInv_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone)
        (fun _ _ => potInv_caseOpt
          (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
            (by simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hSome, hInSome, Expr.eval]))
          (fun _ _ => potInv_ret ?_ ?_))
      · intro st' t' i' m' hEq
        simp only [vpSetVR, letE_eval, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v4,
          Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq, Prod.mk.injEq] at hEq
        rcases hEq with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨hs1Id, rfl, hs1Le, hs1Cases⟩
      · simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hSome, hInSome, prngPrivVpPot,
          vpSetVR, letE_eval, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v4]
private def prngCommitPrivInv (res : (Ty.prod (.opt (cGsTy prngVpTy)) prngEsTy : Ty S).denote) :
    Prop :=
  match res.1 with
  | none => prngPrivInv res.2
  | some s_acc => res.2.2.2 = false ∧ prngGsInv s_acc
private def prngCommitPrivPost (qep : ℕ) (res : (Ty.prod (.opt (cGsTy prngVpTy)) prngEsTy : Ty
    S).denote) : ℕ :=
  match res.1 with
  | none => prngPrivPot qep res.2
  | some s_acc => prngPrivPot qep (s_acc, res.2.2.1, res.2.2.2)
private theorem commitEC_priv_potOKInv (L B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (esE
    : Expr OO Γ' prngEsTy) (sE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (oldE newE :
    Expr OO Γ' prngVpTy) (posE : Expr OO Γ' posTy) (ρ : Env Γ') (hNoAbort : (esE.eval ρ).2.2 =
    false) (hg : prngGsInv (sE.eval ρ)) (hNewId : (newE.eval ρ).1 = pE.eval ρ) (hNewEp : (newE.eval
    ρ).2.2.2.2.2.2 ≤ max (if (pE.eval ρ : Bool) then (sE.eval ρ).2.2.2.1.2 else (sE.eval
    ρ).2.2.2.1.1) (posE.eval ρ).2.1) : PotOKInv P_prng prngCommitPrivInv (prngCommitPrivPost qep)
    ((commitEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI
    := sampI) (sampK := sampK) B ⟨false, tL, t⟩) L esE sE pE oldE newE posE).eval ρ)
    (prngPrivOtherPot qep (sE.eval ρ).1 (pE.eval ρ) + prngPrivVpPot qep (newE.eval ρ)) := by
  unfold commitEC; rw [eval_bind_ret, eval_bind]
  dsimp only [hooksPRNGC, prngCommitC]; rw [eval_ret, pure_bind]
  refine potInv_caseOpt (fun hCNone => by simp [Expr.eval, Expr.v0] at hCNone) (fun _ hCSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hCSome; subst hCSome
  refine potInv_ret ?_ ?_
  · simp only [prngCommitPrivInv, esMk, esAbort, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero,
    Env.get_cons_succ, hNoAbort, true_and]
    set s_acc := (cGsSetStP _ _ _).eval _
    have hAccSt : s_acc.1 = if (pE.eval ρ : Bool) then ((sE.eval ρ).1.1, newE.eval ρ) else
        (newE.eval ρ, (sE.eval ρ).1.2) := by
      cases hp : pE.eval ρ <;> simp [s_acc, hp, cGsSetStP_st_prng, cAcceptE_st_prng, Expr.eval]
    have hAccEp : s_acc.2.2.2.1 = if (pE.eval ρ : Bool) then ((sE.eval ρ).2.2.2.1.1, max (sE.eval
        ρ).2.2.2.1.2 (posE.eval ρ).2.1) else (max (sE.eval ρ).2.2.2.1.1 (posE.eval ρ).2.1, (sE.eval
        ρ).2.2.2.1.2) := by
      cases hp : pE.eval ρ <;>
        simp [s_acc, hp, cGsSetStP, cAcceptE, cDeleteE, letE_eval, cGsMk, cGsEpoch,
          pSet_eval_st_prng, pGet_eval_st_prng, posEpoch, maxN_eval, Expr.eval, Expr.v0]
    have hAccTr : ∀ r ∈ s_acc.2.2.2.2.2.2.1, r ∈ (sE.eval ρ).2.2.2.2.2.2.1 := fun r hr =>
      cDeleteE_trans_mem L sE posE ρ
        (by simpa [s_acc, cGsSetStP, cAcceptE, letE_eval, cGsMk, cGsTrans, Expr.eval, Expr.v0] using hr)
    refine ⟨?_, ?_, ?_, ?_, fun r hr => hg.2.2.2.2 r (hAccTr r hr)⟩
    · rw [hAccSt]; cases hp : pE.eval ρ <;> simp [hp, hNewId, hg.1]
    · rw [hAccSt]; cases hp : pE.eval ρ <;> simp [hp, hNewId, hg.2.1]
    · rw [hAccSt, hAccEp]; cases hp : pE.eval ρ <;> simp [hp] at hNewEp ⊢
      · exact hNewEp
      · exact hg.2.2.1
    · rw [hAccSt, hAccEp]; cases hp : pE.eval ρ <;> simp [hp] at hNewEp ⊢
      · exact hg.2.2.2.1
      · exact hNewEp
  · simp only [prngCommitPrivPost, prngPrivPot, esMk, esAbort, cGsSetStP_st_prng, cAcceptE_st_prng,
    Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, hNoAbort, Bool.false_eq_true,
    ↓reduceIte]
    cases (pE.eval ρ : Bool)
    · simp only [prngPrivOtherPot, Bool.false_eq_true, ↓reduceIte]; omega
    · simp only [prngPrivOtherPot, ↓reduceIte]; omega
private theorem transmitEC_priv_potOKInv (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (π : Policy) {Γ'
    : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool (.prod (.base .msg)
    (.opt (.base .ccoins))))) (ρ : Env Γ') (hInv : prngPrivInv (esE.eval ρ)) : PotOKInv P_prng (fun
    x => prngPrivInv x.2) (fun x => prngPrivPot qep x.2) ((transmitEC (hooksPRNGC (sampKR := sampKR)
    (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B ⟨false, tL,
    t⟩) L (2 + Δcka) qep π esE argE).eval ρ) (prngPrivPot qep (esE.eval ρ)) := by
  unfold transmitEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, cGsWin, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotAbWin
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotAbWin]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  refine potInv_caseOpt (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun s1 hs1 => ?_)
  refine potInv_ite (fun _ => potInv_ret
    (by simp [esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1]; exact prngPrivInv_abort)
    (by simp [prngPrivPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1])) (fun _ => ?_)
  rw [eval_bind]
  have hs1Props := cEpMgmtE_some_priv (2 + Δcka) qep (esG (.fst .v0)) (.fst (.snd .v0)) (isSomeE
    (.snd (.snd (.snd .v0)))) (.cons (esE.eval ρ, argE.eval ρ) ρ)
    (by simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hg0) hs1
  simp only [esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hs1Props
  obtain ⟨hs1_st, hs1Inv, hvpId, hvpEp, hSendQep⟩ := hs1Props; set p0 : Bool := (argE.eval ρ).1
  set ep1 : ℕ := if p0 then s1.2.2.2.1.2 else s1.2.2.2.1.1
  set m_other := prngPrivOtherPot qep s1.1 p0
  have hSend := vSendC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (esH (.fst (Expr.v1 (O := OO)))) .v0
    (.fst (.snd .v1)) (pGet (cGsSt .v0) (.fst (.snd .v1))) (.fst (.snd (.snd .v1))) .none (.snd
    (.snd (.snd .v1))) (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m_other ep1
    (by simpa [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, hs1_st] using hvpEp)
    (by simpa [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, hs1_st] using hSendQep)
  simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero,
    Env.get_cons_succ] at hSend
  change PotOKInv P_prng (prngVSendPrivInv (if p0 then s1.1.2 else s1.1.1) ep1) (prngVSendPrivPost
    qep m_other) _ (m_other + prngPrivVpPot qep (if p0 then s1.1.2 else s1.1.1)) at hSend
  have hSum : m_other + prngPrivVpPot qep (if p0 then s1.1.2 else s1.1.1) = prngPrivPot qep
      (esE.eval ρ) := by rw [prngPrivOtherPot_add_pGet, hs1_st]; simp [prngPrivPot, hab]
  rw [← hSum]
  refine PotOKInv.bindPot hSend (fun sendOut hSendInv => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngVSendPrivPost, hNone, prngPrivPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    obtain ⟨hVp'Id, hVp'Ep, hCtEp⟩ := hSendInv stCt.1 stCt.2 hSome
    refine potInv_ret ?_ ?_
    · simp only [esMk, esAbort, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero,
      Env.get_cons_succ, hab]
      exact fun _ => cRecordE_gsInv L (2 + Δcka) .v2 (.fst (.snd .v3)) (.fst .v0) _ (.bool false) _
        hs1Inv (by simpa [Expr.eval, Expr.v0, Expr.v3, hs1_st, hvpId] using hVp'Id)
        (by simpa [Expr.eval, Expr.v0, Expr.v2, Expr.v3] using hVp'Ep)
        (by simp only [pGet_eval_st_prng, cGsEpoch, Expr.eval, Env.get_cons_zero,
          Env.get_cons_succ]; exact hCtEp)
    · simp only [prngVSendPrivPost, hSome, prngPrivPot, esMk, esAbort, cRecordE_st_prng, Expr.eval,
      Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab, Bool.false_eq_true,
      ↓reduceIte]
      have hEq := prngPrivPot_pSet_eq qep s1.1 p0 stCt.1; dsimp only at hEq
      change (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
        prngPrivVpPot qep st'.1 + prngPrivVpPot qep st'.2) ≤ m_other + prngPrivVpPot qep stCt.1
      rw [hEq]
private theorem challEC_priv_potOKInv (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (cfg : ConfigEC OO)
    (π : Policy) {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool
    (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins)))))) (ρ : Env Γ') (hInv :
    prngPrivInv (esE.eval ρ)) : PotOKInv P_prng (fun x => prngPrivInv x.2) (fun x => prngPrivPot qep
    x.2) ((challEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) L (2 + Δcka) qep cfg π esE argE).eval ρ)
    (prngPrivPot qep (esE.eval ρ)) := by
  unfold challEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, cGsWin, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotAbWin
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotAbWin]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  refine potInv_caseOpt (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun s1 hs1 => potInv_ite
      (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v1] using hInv) (by simp [Expr.eval, Expr.v1]))
      (fun _ => potInv_ite (fun _ => potInv_ret
        (by simp [esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1]; exact prngPrivInv_abort)
        (by simp [prngPrivPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1])) (fun _ => ?_)))
  rw [eval_bind]
  have hs1Props := cEpMgmtE_some_priv (2 + Δcka) qep (esG (.fst .v0)) (.fst (.snd .v0)) (isSomeE
    (.snd (.snd (.snd (.snd .v0))))) (.cons (esE.eval ρ, argE.eval ρ) ρ)
    (by simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hg0) hs1
  simp only [esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hs1Props
  obtain ⟨hs1_st, hs1Inv, hvpId, hvpEp, hSendQep⟩ := hs1Props; set p0 : Bool := (argE.eval ρ).1
  set ep1 : ℕ := if p0 then s1.2.2.2.1.2 else s1.2.2.2.1.1
  set m_other := prngPrivOtherPot qep s1.1 p0
  have hSend := vSendC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (esH (.fst (Expr.v1 (O := OO)))) .v0
    (.fst (.snd .v1)) (pGet (cGsSt .v0) (.fst (.snd .v1))) (cfg.challMsgE (pGet (cGsEpoch .v0) (.fst
    (.snd .v1))) (cGsB (esG (.fst .v1))) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))) (.snd (.snd (.snd (.snd
    .v1)))) (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m_other ep1
    (by simpa [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, hs1_st] using hvpEp)
    (by simpa [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, hs1_st] using hSendQep)
  simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero,
    Env.get_cons_succ] at hSend
  change PotOKInv P_prng (prngVSendPrivInv (if p0 then s1.1.2 else s1.1.1) ep1) (prngVSendPrivPost
    qep m_other) _ (m_other + prngPrivVpPot qep (if p0 then s1.1.2 else s1.1.1)) at hSend
  have hSum : m_other + prngPrivVpPot qep (if p0 then s1.1.2 else s1.1.1) = prngPrivPot qep
      (esE.eval ρ) := by rw [prngPrivOtherPot_add_pGet, hs1_st]; simp [prngPrivPot, hab]
  rw [← hSum]
  refine PotOKInv.bindPot hSend (fun sendOut hSendInv => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngVSendPrivPost, hNone, prngPrivPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    obtain ⟨hVp'Id, hVp'Ep, hCtEp⟩ := hSendInv stCt.1 stCt.2 hSome
    refine potInv_ret ?_ ?_
    · simp only [esMk, esAbort, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero,
      Env.get_cons_succ, hab]
      exact fun _ => cRecordE_gsInv L (2 + Δcka) .v2 (.fst (.snd .v3)) (.fst .v0) _ (.bool true) _
        hs1Inv (by simpa [Expr.eval, Expr.v0, Expr.v3, hs1_st, hvpId] using hVp'Id)
        (by simpa [Expr.eval, Expr.v0, Expr.v2, Expr.v3] using hVp'Ep)
        (by simp only [pGet_eval_st_prng, cGsEpoch, Expr.eval, Env.get_cons_zero,
          Env.get_cons_succ]; exact hCtEp)
    · simp only [prngVSendPrivPost, hSome, prngPrivPot, esMk, esAbort, cRecordE_st_prng, Expr.eval,
      Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab, Bool.false_eq_true,
      ↓reduceIte]
      have hEq := prngPrivPot_pSet_eq qep s1.1 p0 stCt.1; dsimp only at hEq
      change (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
        prngPrivVpPot qep st'.1 + prngPrivVpPot qep st'.2) ≤ m_other + prngPrivVpPot qep stCt.1
      rw [hEq]
private theorem deliverEC_priv_potOKInv (L B maxSkip qep : ℕ) (tL : Option ℕ) (t : ℕ) (cfg :
    ConfigEC OO) {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool
    hdrCtTy)) (ρ : Env Γ') (hInv : prngPrivInv (esE.eval ρ)) : PotOKInv P_prng (fun x => prngPrivInv
    x.2) (fun x => prngPrivPot qep x.2) ((deliverEC (hooksPRNGC (sampKR := sampKR) (sampKC :=
    sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) L maxSkip
    cfg esE argE).eval ρ) (prngPrivPot qep (esE.eval ρ)) := by
  unfold deliverEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, cGsWin, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotAbWin
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotAbWin]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  refine potInv_caseOpt (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun r1 hr1 => ?_)
  have hcLe : (argE.eval ρ).2.1.1 ≤ r1.1.2.1 := by
    simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using cInTransitE_some_priv L (esG (.fst .v0))
      (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) (.cons (esE.eval ρ, argE.eval ρ) ρ)
      (by simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hg0) hr1
  rw [eval_bind]; set m_other := prngPrivOtherPot qep (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (esH (.fst (Expr.v1 (O := OO)))) (esG
    (.fst .v1)) (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd
    .v1)) (.some .v0) (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero,
    Env.get_cons_succ] at hRecv
  change PotOKInv P_prng (prngVRecvPrivInv (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
    (esE.eval ρ).1.1.1) (argE.eval ρ).2.1.1) (prngVRecvPrivPost qep m_other (if ((argE.eval ρ).1 :
    Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ (m_other + prngPrivVpPot qep (if
    ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) at hRecv
  have hSum : m_other + prngPrivVpPot qep (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
      (esE.eval ρ).1.1.1) = prngPrivPot qep (esE.eval ρ) := by
    rw [prngPrivOtherPot_add_pGet]; simp [prngPrivPot, hab]
  rw [← hSum]
  refine PotOKInv.bindPot hRecv (fun recvOut hRecvInv => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngVRecvPrivPost, hNone, prngPrivPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potInv_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potInv_ret ?_ ?_
      · simp only [esMk, esAbort, esG, Expr.eval, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero,
        Env.get_cons_succ, hab]
        exact fun _ => prngGsInv_ite
          (cGsSetWin_gsInv _ _ _ (by simpa [esG, Expr.eval, Expr.v3] using hg0)) hg0
      · simp only [prngVRecvPrivPost, hSome, hInNone, esMk, esAbort, esG, Expr.eval, Expr.v1,
        Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
        refine Nat.le_trans
          (Nat.le_of_eq (prngPrivPot_mk_eq qep (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
            (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) ?_
        simpa [prngPrivPot, hab] using hSum.symm.le
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      obtain ⟨hstId, _, _, hstCases⟩ :=
        hRecvInv tup.1 tup.2.1 tup.2.2.1 tup.2.2.2 (by rw [hSome, hInSome])
      have hvpId : (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1).1 =
          (argE.eval ρ).1 := by cases ((argE.eval ρ).1 : Bool) <;> simp [hg0.1, hg0.2.1]
      have hvpEp : (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval
          ρ).1.1.1).2.2.2.2.2.2 ≤ (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.2.2.2.1.2 else
          (esE.eval ρ).1.2.2.2.1.1) := by
        cases ((argE.eval ρ).1 : Bool) <;> simp [hg0.2.2.1, hg0.2.2.2.1]
      rw [eval_bind]
      have hCom := commitEC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
        sampCCoins) (sampI := sampI) (sampK := sampK) L B qep tL t (esSetH (.fst (Expr.v4 (O :=
        OO))) (.snd .v2)) (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst
        (.snd .v4))) (.fst .v0) (cRecPos .v3) (.cons tup (.cons resInner (.cons recvOut (.cons r1
        (.cons (esE.eval ρ, argE.eval ρ) ρ)))))
        (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v4, hab])
        (by simpa [esG, Expr.eval, Expr.v4] using hg0)
        (by simpa [Expr.eval, Expr.v0, Expr.v4, hvpId] using hstId)
        (by simp only [esG, cRecPos, Expr.eval, Expr.v0, Expr.v3, Expr.v4, Env.get_cons_zero,
          Env.get_cons_succ]
            rcases hstCases with hEq0 | hEqC
            · rw [hEq0]; exact Nat.le_trans hvpEp (Nat.le_max_left _ _)
            · rw [hEqC]; exact Nat.le_trans hcLe (Nat.le_max_right _ _))
      simp only [esG, Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ] at hCom
      have hPre : prngPrivOtherPot qep (esE.eval ρ).1.1 (argE.eval ρ).1 + prngPrivVpPot qep tup.1 ≤
          prngVRecvPrivPost qep m_other (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
          (esE.eval ρ).1.1.1) recvOut := by simp [prngVRecvPrivPost, hSome, hInSome, m_other]
      refine (PotOKInv.bindPot hCom (fun comOut hComInv => ?_)).mono hPre
      refine potInv_caseOpt (fun hCNone => ?_) (fun s_acc hCSome => ?_)
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
        exact potInv_ret (by simpa [prngCommitPrivInv, hCNone, Expr.eval, Expr.v0] using hComInv)
          (by simp [prngCommitPrivPost, hCNone, Expr.eval, Expr.v0])
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
        simp only [prngCommitPrivInv, hCSome] at hComInv; obtain ⟨hComAb, hsAccInv⟩ := hComInv
        refine potInv_ret ?_ ?_
        · simp only [esSetG, letE_eval, esMk, esAbort, esH, Expr.eval, Expr.v0, Expr.v1,
          Env.get_cons_zero, Env.get_cons_succ, hComAb]
          exact fun _ => prngGsInv_ite (cGsSetWin_gsInv _ _ _ hsAccInv) hsAccInv
        · simp only [prngCommitPrivPost, hCSome, esSetG, letE_eval, esMk, esAbort, esH, Expr.eval,
          Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
          exact Nat.le_of_eq
            (prngPrivPot_mk_eq qep (g2 := s_acc) (h2 := comOut.2.2.1)
              (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))
private theorem injectEC_priv_potOKInv (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (cfg : ConfigEC
    OO) {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool hdrCtTy)) (ρ
    : Env Γ') (hInv : prngPrivInv (esE.eval ρ)) : PotOKInv P_prng (fun x => prngPrivInv x.2) (fun x
    => prngPrivPot qep x.2) ((injectEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins
    := sampCCoins) (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) L (2 + Δcka) qep cfg esE
    argE).eval ρ) (prngPrivPot qep (esE.eval ρ)) := by
  unfold injectEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotRef
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotRef]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  rw [eval_bind]; set m_other := prngPrivOtherPot qep (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (esH (.fst (Expr.v0 (O := OO)))) (esG
    (.fst .v0)) (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd
    .v0)) .none (.cons (esE.eval ρ, argE.eval ρ) ρ) m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  change PotOKInv P_prng (prngVRecvPrivInv (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
    (esE.eval ρ).1.1.1) (argE.eval ρ).2.1.1) (prngVRecvPrivPost qep m_other (if ((argE.eval ρ).1 :
    Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ (m_other + prngPrivVpPot qep (if
    ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) at hRecv
  have hSum : m_other + prngPrivVpPot qep (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
      (esE.eval ρ).1.1.1) = prngPrivPot qep (esE.eval ρ) := by
    rw [prngPrivOtherPot_add_pGet]; simp [prngPrivPot, hab]
  rw [← hSum]
  refine PotOKInv.bindPot hRecv (fun recvOut hRecvInv => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngVRecvPrivPost, hNone, prngPrivPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potInv_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      exact potInv_ret
        (by simp only [esSetH, letE_eval, esMk, esAbort, esG, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
          Env.get_cons_zero, Env.get_cons_succ, hab]; exact fun _ => hg0)
        (by simp only [prngVRecvPrivPost, hSome, hInNone, prngPrivPot, esSetH, letE_eval, esMk,
          esAbort, esG, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
          hab, Bool.false_eq_true, ↓reduceIte]
            simpa [prngPrivPot, hab] using hSum.symm.le)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      obtain ⟨hstId, ht'Eq, _, hstCases⟩ :=
        hRecvInv tup.1 tup.2.1 tup.2.2.1 tup.2.2.2 (by rw [hSome, hInSome])
      refine potInv_ite
        (fun _ => potInv_ret
          (by simp only [esSetH, letE_eval, esMk, esAbort, esG, Expr.eval, Expr.v0, Expr.v2,
            Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]; exact fun _ => hg0)
          (by simp only [prngVRecvPrivPost, hSome, hInSome, prngPrivPot, esSetH, letE_eval, esMk,
            esAbort, esG, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero,
            Env.get_cons_succ, hab, Bool.false_eq_true, ↓reduceIte]
              have hEqSum : prngPrivVpPot qep (esE.eval ρ).1.1.1 + prngPrivVpPot qep (esE.eval
                  ρ).1.1.2 = m_other + prngPrivVpPot qep (if ((argE.eval ρ).1 : Bool) then (esE.eval
                  ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
                simpa [prngPrivPot, hab] using hSum.symm
              omega))
        (fun _ => potInv_ite (fun _ => ?_) (fun _ => ?_))
      · have hvpId : (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
            (esE.eval ρ).1.1.1).1 = (argE.eval ρ).1 := by
          cases ((argE.eval ρ).1 : Bool) <;> simp [hg0.1, hg0.2.1]
        have hvpEp : (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
            (esE.eval ρ).1.1.1).2.2.2.2.2.2 ≤ (if ((argE.eval ρ).1 : Bool) then
            (esE.eval ρ).1.2.2.2.1.2 else (esE.eval ρ).1.2.2.2.1.1) := by
          cases ((argE.eval ρ).1 : Bool) <;> simp [hg0.2.2.1, hg0.2.2.2.1]
        rw [eval_bind]
        have hCom := commitEC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
          sampCCoins) (sampI := sampI) (sampK := sampK) L B qep tL t (esSetH (.fst (Expr.v3 (O :=
          OO))) (.snd .v2)) (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst
          (.snd .v3))) (.fst .v0) (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst
          (.snd (.snd .v0))))) (.cons tup (.cons resInner (.cons recvOut (.cons (esE.eval ρ,
          argE.eval ρ) ρ))))
          (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v3, hab])
          (by simpa [esG, Expr.eval, Expr.v3] using hg0)
          (by simpa [Expr.eval, Expr.v0, Expr.v3, hvpId] using hstId)
          (by simp only [esG, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
              rcases hstCases with hEq0 | hEqC
              · rw [hEq0]; exact Nat.le_trans hvpEp (Nat.le_max_left _ _)
              · rw [hEqC, ← ht'Eq]; exact Nat.le_max_right _ _)
        simp only [esG, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hCom
        have hPre : prngPrivOtherPot qep (esE.eval ρ).1.1 (argE.eval ρ).1 + prngPrivVpPot qep tup.1
            ≤ prngVRecvPrivPost qep m_other (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2
            else (esE.eval ρ).1.1.1) recvOut := by simp [prngVRecvPrivPost, hSome, hInSome, m_other]
        refine (PotOKInv.bindPot hCom (fun comOut hComInv => ?_)).mono hPre
        refine potInv_caseOpt (fun hCNone => ?_) (fun s_acc hCSome => ?_)
        · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
          exact potInv_ret (by simpa [prngCommitPrivInv, hCNone, Expr.eval, Expr.v0] using hComInv)
            (by simp [prngCommitPrivPost, hCNone, Expr.eval, Expr.v0])
        · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
          simp only [prngCommitPrivInv, hCSome] at hComInv; obtain ⟨_, hsAccInv⟩ := hComInv
          exact potInv_ret
            (by simp only [esSetG, letE_eval, esMk, esAbort, esH, Expr.eval, Expr.v0, Expr.v1]
                exact fun _ => hsAccInv)
            (by simp [prngCommitPrivPost, hCSome, prngPrivPot, esSetG, letE_eval, esMk, esAbort,
                  esH, Expr.eval, Expr.v0, Expr.v1])
      · refine potInv_ret ?_ ?_
        · simp only [esSetG, esSetH, letE_eval, esMk, esAbort, esG, esH, Expr.eval, Expr.v0,
          Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
          exact fun _ => prngGsInv_ite
            (cGsSetWin_gsInv _ _ _ (by simpa [esG, Expr.eval, Expr.v3] using hg0)) hg0
        · simp only [prngVRecvPrivPost, hSome, hInSome, esSetG, esSetH, letE_eval, esMk, esAbort,
          esG, esH, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.le_of_eq (prngPrivPot_mk_eq qep (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
              (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) ?_
          simp only [prngPrivPot, Bool.false_eq_true, ↓reduceIte]
          have hEqSum : prngPrivVpPot qep (esE.eval ρ).1.1.1 + prngPrivVpPot qep (esE.eval ρ).1.1.2
              = m_other + prngPrivVpPot qep (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2
              else (esE.eval ρ).1.1.1) := by simpa [prngPrivPot, hab] using hSum.symm
          omega
private theorem corrEC_priv_potOKInv (L B qep : ℕ) (tL : Option ℕ) (t : ℕ) (π : Policy) {Γ' : List
    (Ty S)} (esE : Expr OO Γ' prngEsTy) (pE : Expr OO Γ' .bool) (ρ : Env Γ') (hInv : prngPrivInv
    (esE.eval ρ)) : PotOKInv P_prng (fun x => prngPrivInv x.2) (fun x => prngPrivPot qep x.2)
    ((corrEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI :=
    sampI) (sampK := sampK) B ⟨false, tL, t⟩) L π esE pE).eval ρ) (prngPrivPot qep (esE.eval ρ)) :=
    by
  unfold corrEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotRef
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotRef]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  refine potInv_ite (fun _ => potInv_ret
    (by simp [esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0]; exact prngPrivInv_abort)
    (by simp [prngPrivPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0])) (fun _ => ?_)
  rw [eval_bind]
  refine PotOKInv.bindSupp (r := prngPrivPot qep (esE.eval ρ)) (Comp.queryBound_eval P_prng
    (fun _ => 1) (fun _ => 0) (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero _ _) (fun _ _ => ?_)
    (by simp [hooksPRNGC, prngRevealC_queries])
  refine potInv_caseOpt
    (fun _ => potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngPrivPot, esMk, Expr.eval]))
    (fun _ _ => potInv_ret
      (by simp only [esMk, esAbort, Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero, hab]
          exact fun _ => cAfterCorrE_gsInv L (esG (.fst .v2)) (.snd .v2) _
            (by simpa [esG, Expr.eval, Expr.v2] using hg0))
      (by simp [prngPrivPot, esMk, esAbort, esG, cAfterCorrE_st_prng, Expr.eval, Expr.v2]))
private theorem implEC_priv_potOKInv (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) (cfg :
    ConfigEC OO) (π : Policy) {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (qE : Expr OO Γ'
    (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ') (hInv : prngPrivInv (esE.eval ρ)) :
    PotOKInv P_prng (fun x => prngPrivInv x.2) (fun x => prngPrivPot qep x.2) ((implEC (hooksPRNGC
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK :=
    sampK) B ⟨false, tL, t⟩) L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ) (prngPrivPot qep
    (esE.eval ρ)) := by
  unfold implEC; rw [eval_bind_ret]
  refine potInv_caseSum (fun _ _ => potInv_caseSum (fun _ _ => potInv_caseSum
    (fun _ _ => potInv_caseSum (fun _ _ => ?_) (fun _ _ => ?_)) (fun _ _ => ?_)) (fun _ _ => ?_))
    (fun _ _ => ?_)
  · rw [eval_bind]; exact PotOKInv.bindPot (transmitEC_priv_potOKInv L B Δcka qep tL t π (.fst
      (Expr.v4 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v4] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInv.bindPot (challEC_priv_potOKInv L B Δcka qep tL t cfg π (.fst
      (Expr.v4 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v4] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInv.bindPot (deliverEC_priv_potOKInv L B maxSkip qep tL t cfg (.fst
      (Expr.v3 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v3] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInv.bindPot (injectEC_priv_potOKInv L B Δcka qep tL t cfg (.fst
      (Expr.v2 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v2] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInv.bindPot (corrEC_priv_potOKInv L B qep tL t π (.fst
      (Expr.v1 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v1] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
private theorem initPRNGEStateC_priv_potOKInv (qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)}
    (bE : Expr OO Γ' .bool) (ρ : Env Γ') : PotOKInv P_prng prngPrivInv (prngPrivPot qep)
    ((initPRNGEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI :=
    sampI) (sampK := sampK) ⟨false, tL, t⟩ bE).eval ρ) (2 * qep + 2) := by
  unfold initPRNGEStateC; rw [eval_bind_ret, eval_bind]
  refine PotOKInv.bindSupp (m := 0) (r := 2 * qep + 2) ((Comp.queryBound_eval P_prng (fun _ => 1)
    (fun _ => 0) (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero
    (Comp.sample (O := OO) (I := II) CKASamp.kc (.unit)) (.cons (bE.eval ρ) ρ)).mono
    (by simp [Comp.queries])) (fun kc _ => ?_) (Nat.zero_add _).le
  rw [eval_bind]
  refine PotOKInv.bindSupp (m := 2) (r := 2 * qep) ((Comp.queryBound_eval P_prng (fun _ => 1)
    (fun _ => 0) (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero
    (rootPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
      (sampK := sampK) ⟨false, tL, t⟩ (.nat 0) (Expr.op (O := OO) CKAOp.lamI .unit) .none)
    (.cons kc (.cons (bE.eval ρ) ρ))).mono (by simp [rootPRNGC_queries])) (fun _ _ => ?_) (by omega)
  refine potInv_caseOpt (fun _ => potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
    (by simp [prngPrivPot, esMk, Expr.eval])) (fun _ _ => potInv_ret ?_ ?_)
  · intro _
    simp only [esMk, cGsInitE, cGsMk, mkPartiesE, vpMk, partyEnc, Expr.eval, Expr.v0,
      Env.get_cons_zero]
    exact ⟨rfl, rfl, Nat.le_refl 0, Nat.le_refl 0, fun _ hr => by simp at hr⟩
  · have hSum := prngPrivPartyCount_zero_sum qep
    simp only [prngPrivPot, prngPrivVpPot, esMk, cGsInitE, cGsMk, mkPartiesE, vpMk,
      partyDec_partyEnc, Expr.eval, Bool.false_eq_true, ↓reduceIte]
    omega
/-- **Epoch-cap potential query bound (`2 * qep + 2`)** for `redPRNGPrivProg`
(`mo.auth = false`, `c = 0`): holds unconditionally for EVERY SM adversary `A`. -/
private theorem redPRNGPrivProg_queries_qep (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) (A :
    Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) : (((redPRNGPrivProg (ckaInitA :=
    ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit :=
    prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL t).eval (fun _ => A)
    ())).IsQueryBoundP (· matches .inr _) (2 * qep + 2) := by
  suffices hGame : (((redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend :=
      ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender :=
      fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK :=
      sampK) L B Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP P_prng (2 * qep + 2) by
    exact hGame.of_imp (fun x hx => by cases x <;> [cases hx; trivial])
  set R := redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender :=
    fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR
    := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B
    Δcka qep maxSkip tL t
  have hInit : PotOKInv P_prng (fun as : (Ty.prod .unit prngEsTy : Ty S).denote => prngPrivInv as.2)
      (fun as => prngPrivPot qep as.2) (R.init.eval (Env.cons (t := .unit) () .nil)) (2 * qep + 2)
      := by
    dsimp only [R, redPRNGPrivProg]; rw [eval_bind]
    refine PotOKInv.bindSupp (r := 2 * qep + 2)
      (Comp.queryBound_eval P_prng (fun _ => 1) (fun _ => 0)
        (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero _ _)
      (fun b0 _ => ?_) (by simp [Comp.queries])
    rw [eval_bind]
    exact PotOKInv.bindPot
      (initPRNGEStateC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        qep tL t .v0 (Env.cons (t := .bool) b0 (Env.cons (t := .unit) () .nil)))
      (fun _ hEs => potInv_ret (by simpa [Expr.eval, Expr.v0] using hEs)
        (by simp [Expr.eval, Expr.v0]))
  unfold CostedReduction.eval CostedReduction.impl
  refine hInit.run _ ?_; rintro ⟨_, s0⟩ hs0
  have hSim := potOKInv_simulateQ_handlerImpl_c0 prngPrivInv (prngPrivPot qep) (prngIface_fwdU_zero
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK :=
    sampK)) R.handle (fun qv sv hsv => implEC_priv_potOKInv L B Δcka qep maxSkip tL t (modeCfgEC OO
    ⟨false, tL, t⟩) (⟨false, tL, t⟩ : Mode).policy .v0 .v1 (.cons sv (.cons qv .nil)) hsv) A hs0
  refine hSim.run _ ?_; rintro ⟨bOut, sOut⟩ _
  exact (Comp.queryBound_eval P_prng (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero R.finish
    (.cons sOut (.cons bOut .nil))).mono (by simp [R, redPRNGPrivProg, privOutC, Comp.queries])
/-- **Combined syntactic + `c = 1` + `c = 0` PRF-PRNG query bound
(`min (2 + 2 * q) (min (q + 3) (2 * qep + 2))`)** for `redPRNGPrivProg`. -/
private theorem redPRNGPrivProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) (A :
    Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) (hA : MakesAtMostQueries A q) :
    (((redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender :=
    fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR
    := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B
    Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP (· matches .inr _) (min (2 + 2 * q)
    (min (q + 3) (2 * qep + 2))) := by
  have h12 := redPRNGPrivProg_makesAtMostQueries_q3 (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive
    := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE :=
    defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
    (sampK := sampK) L B Δcka qep maxSkip tL t q A hA
  have h3 := redPRNGPrivProg_queries_qep (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend :=
    ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender :=
    fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR
    := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B
    Δcka qep maxSkip tL t A
  have hMin := isQueryBoundP_min_prng h12 h3
  rwa [Nat.min_assoc] at hMin

end PrngPrivQepPotOK

namespace FSPotOK

set_option linter.unusedSimpArgs false

open _root_.ReductionDsl (Env GameCodec handlerImpl isGameQuery)

open _root_.CryptoGames.CKA (CKAOp CKASamp)
open _root_.CryptoGames.SM (Adversary MakesAtMostQueries posTy partyEnc partyDec partyDec_partyEnc
  sendsInE sendsInE_eval otherE orE pGet pSet letE_eval ite_eval some_eval)
open _root_.CryptoGames.SM.Engine (ConfigEC Policy modeCfgEC cRecTy cRecPos cGsTy esTy esG esH esAbort esMk
  esSetG esSetH esSetAbort cGsSt cGsMk cGsInitE cGsSetStP cGsSetWin cLeakE cEpMgmtE cDeleteE
  cAcceptE cRecordE cAfterCorrE mkPartiesE vpId vpRoot vpVS vpVR vpΓ vpTcur vpTcurNat vpMk
  vpSetVS vpSetVR vSendStep1C vSendC vRecvStep1C vRecvC commitEC transmitEC challEC deliverEC
  injectEC corrEC implEC eval_bind eval_bind_ret eval_ret tset_eval_eq_update)
open _root_.CryptoGames.SM.Construction (Header PartyState Mode fsCacheEntryTy fsTableEntryTy
  fsTransEntryTy fsExtTy fsHsTy fsVpTy fsEsTy fsHsMk fsHsSCorr fsHsExt fsHsEmptyE fsHsSetCache
  fsHsSetTable fsHsSetSessions fsHsSetTrans fsHsSetCountTrans fsHsSetSCorr fsHsSetExt isExtE
  extOfE lookupFC rootFSC fsStartSendC fsStartRecvC fsFsSendC fsFsRecvC fsCommitC rangeListC
  rangeListC_queries fsRevealC hooksFSC initFSEStateC redFsPolUni implUniEC redFSAuthProg
  redFSPrivUniProg redFSPrivUniCoinProg implEC_hooksFSC_queries fsRevealC_queries
  initFSEStateC_queries)

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_fs" => CryptoGames.PRFPRNG.prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_fs" =>
  CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "II_fs" =>
  CryptoGames.PRFPRNG.fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
local notation "hsTyFS" => fsHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpTyFS" => fsVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "esTyFS" => fsEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTyFS" => CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTyFS" => CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "P_fs" => isGameQuery (G := CryptoGames.FSAEAD.spec SS RS (Header T) M E)

private theorem isQueryBoundP_min_fs {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {oa : OracleComp spec α} {P : ι → Prop} [DecidablePred P] {a b : ℕ}
    (ha : oa.IsQueryBoundP P a) (hb : oa.IsQueryBoundP P b) :
    oa.IsQueryBoundP P (min a b) := by
  rcases Nat.le_total a b with h | h
  · simpa [Nat.min_eq_left h] using ha
  · simpa [Nat.min_eq_right h] using hb

private theorem fsIface_fwdU_zero (n : ℕ) :
    ((II_fs).fwdU n).IsQueryBoundP P_fs 0 := by
  change OracleComp.IsQueryBoundP
    (liftM (OracleSpec.query
      (spec := unifSpec + CryptoGames.FSAEAD.spec SS RS (Header T) M E) (.inl n))) P_fs 0
  rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [isGameQuery]), fun _ => by simp⟩

/-- Potential on `fsHsTy.denote` (`≤ 1`): `1` credit for the unique `cs` query inside `fsFsSendC`
when `fsSCorr = false` and `ext = none`, cleared as soon as `fsSCorr = true` or `ext.isSome`. -/
private def fsHPot (h : (hsTyFS).denote) : ℕ :=
  if h.2.2.2.2.2.1 || h.2.2.2.2.2.2.isSome then 0 else 1

private def fsPot (es : (esTyFS).denote) : ℕ :=
  fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) es.2.1



@[local simp] private theorem fsHPot_setCache {O' : Ops S_fs} {Γ'} (h : Expr O' Γ' hsTyFS)
    (c : Expr O' Γ' (.tbl (.opt (fsCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E))))
    (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetCache h c).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (h.eval ρ) := by
  simp [fsHsSetCache, fsHsMk, fsHsSCorr, fsHsExt, fsHPot, Expr.eval]

@[local simp] private theorem fsHPot_setTable {O' : Ops S_fs} {Γ'} (h : Expr O' Γ' hsTyFS)
    (tbl : Expr O' Γ' (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetTable h tbl).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (h.eval ρ) := by
  simp [fsHsSetTable, fsHsMk, fsHsSCorr, fsHsExt, fsHPot, Expr.eval]

@[local simp] private theorem fsHPot_setSessions {O' : Ops S_fs} {Γ'} (h : Expr O' Γ' hsTyFS)
    (ses : Expr O' Γ' (.list (.base .i))) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetSessions h ses).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (h.eval ρ) := by
  simp [fsHsSetSessions, fsHsMk, fsHsSCorr, fsHsExt, fsHPot, Expr.eval]

@[local simp] private theorem fsHPot_setTrans {O' : Ops S_fs} {Γ'} (h : Expr O' Γ' hsTyFS)
    (tr : Expr O' Γ' (.list (fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetTrans h tr).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (h.eval ρ) := by
  simp [fsHsSetTrans, fsHsMk, fsHsSCorr, fsHsExt, fsHPot, Expr.eval]

@[local simp] private theorem fsHPot_setCountTrans {O' : Ops S_fs} {Γ'} (h : Expr O' Γ' hsTyFS)
    (cnt : Expr O' Γ' .nat)
    (tr : Expr O' Γ' (.list (fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetCountTrans h cnt tr).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (h.eval ρ) := by
  simp [fsHsSetCountTrans, fsHsMk, fsHsSCorr, fsHsExt, fsHPot, Expr.eval]

@[local simp] private theorem fsHPot_setSCorr_true {O' : Ops S_fs} {Γ'} (h : Expr O' Γ' hsTyFS)
    (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetSCorr h (.bool true)).eval ρ) = 0 := by
  simp [fsHsSetSCorr, fsHsMk, fsHsExt, fsHPot, Expr.eval]

@[local simp] private theorem fsHPot_setExt_some {O' : Ops S_fs} {Γ'} (h : Expr O' Γ' hsTyFS)
    (e : Expr O' Γ' (.prod (.base .ss) (.base .rs))) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetExt h (.some e)).eval ρ) = 0 := by
  simp [fsHsSetExt, fsHsMk, fsHsSCorr, fsHPot, Expr.eval]

@[local simp] private theorem fsHPot_isExtE (L j : ℕ) {Γ'} (hE : Expr OO_fs Γ' hsTyFS)
    (ikE : Expr OO_fs Γ' (.base .i)) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      (((isExtE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L j hE ikE).eval ρ).2) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := by
  unfold isExtE
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero]
  split_ifs <;> simp [fsHsSetSessions, fsHsMk, fsHsSCorr, fsHsExt, fsHPot, Expr.eval]

@[local simp] private theorem fsHPot_extOfE (L j : ℕ) {Γ'} (hE : Expr OO_fs Γ' hsTyFS)
    (sidE : Expr OO_fs Γ' (.opt (.base .i))) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      (((extOfE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L j hE sidE).eval ρ).2) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := by
  unfold extOfE
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero]
  cases (sidE.eval ρ) <;>
    simp [fsHPot_isExtE, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]

@[local simp] private theorem fsPot_mk {g : (cGsTy vpTyFS).denote}
    {h : (hsTyFS).denote} {ab : Bool} :
    fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (g, h, ab) =
      fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) h := rfl

/-- Virtual-party invariant ensuring `vp.vS = some none` (external sender at `tStar`) and
`vp.vR tStar = some none` (external receiver at `tStar`) cannot hold simultaneously on the same
party, so `fsRevealC` makes at most `1` target query (`cs` xor `cr`). -/
private def fsVpInv (tStar : ℕ) (vp : (vpTyFS).denote) : Prop :=
  (vp.2.2.1 = some none → (partyDec vp.1).sendsIn tStar = true) ∧
  (vp.2.2.2.1 tStar = some none → (partyDec vp.1).sendsIn tStar = false)

private def fsGsInv (tStar : ℕ) (g : (cGsTy vpTyFS).denote) : Prop :=
  fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar g.1.1 ∧
  fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar g.1.2

private def fsEsInv (tStar : ℕ) (es : (esTyFS).denote) : Prop :=
  fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar es.1

private theorem fsGsInv_of_st_eq {tStar : ℕ} {g₁ g₂ : (cGsTy vpTyFS).denote}
    (hst : g₁.1 = g₂.1)
    (hg : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar g₂) :
    fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar g₁ :=
  ⟨by rw [hst]; exact hg.1, by rw [hst]; exact hg.2⟩

private theorem pGet_eval_st_fs {O' : Ops S_fs} {vpT : Ty S_fs} {Γ' : List (Ty S_fs)}
    (st : Expr O' Γ' (.prod vpT vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ') :
    (pGet st p).eval ρ = if p.eval ρ then (st.eval ρ).2 else (st.eval ρ).1 := by
  cases hp : (p.eval ρ : Bool) <;> simp [pGet, Expr.eval, Expr.v0, hp]

private theorem pSet_eval_st_fs {O' : Ops S_fs} {vpT : Ty S_fs} {Γ' : List (Ty S_fs)}
    (st : Expr O' Γ' (.prod vpT vpT)) (p : Expr O' Γ' .bool) (v : Expr O' Γ' vpT) (ρ : Env Γ') :
    (pSet st p v).eval ρ =
      if p.eval ρ then ((st.eval ρ).1, v.eval ρ) else (v.eval ρ, (st.eval ρ).2) := by
  cases hp : (p.eval ρ : Bool) <;> simp [pSet, Expr.eval, Expr.v0, hp]

private theorem fsVpInv_pGet {O' : Ops S_fs} {Γ' : List (Ty S_fs)} {tStar : ℕ}
    (s : Expr O' Γ' (cGsTy vpTyFS)) (p : Expr O' Γ' .bool) (ρ : Env Γ')
    (hg : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (s.eval ρ)) :
    fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar
      ((pGet (cGsSt s) p).eval ρ) := by
  rw [pGet_eval_st_fs]; simp only [cGsSt, Expr.eval]
  cases (p.eval ρ)
  · exact hg.1
  · exact hg.2

private theorem cLeakE_st_fs {O' : Ops S_fs} {vpT : Ty S_fs} {Γ' : List (Ty S_fs)}
    (s : Expr O' Γ' (cGsTy vpT)) (l : Expr O' Γ' .nat) (ρ : Env Γ') :
    ((cLeakE s l).eval ρ).1 = (s.eval ρ).1 := by
  simp [cLeakE, cGsMk, cGsSt, Expr.eval, Expr.v0]

private theorem cEpMgmtE_some_st_fs {O' : Ops S_fs} {vpT : Ty S_fs} {Γ' : List (Ty S_fs)}
    (Δ qep : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p bad : Expr O' Γ' .bool) (ρ : Env Γ')
    {s₁ : (cGsTy vpT).denote} (h : (cEpMgmtE Δ qep s p bad).eval ρ = some s₁) :
    s₁.1 = (s.eval ρ).1 :=
  Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.cEpMgmtE_some_st_prng Δ qep s p bad ρ h

private theorem cDeleteE_st_fs {O' : Ops S_fs} {vpT : Ty S_fs} {Γ' : List (Ty S_fs)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (pos : Expr O' Γ' posTy) (ρ : Env Γ') :
    ((cDeleteE L s pos).eval ρ).1 = (s.eval ρ).1 := by
  simp [cDeleteE, cGsMk, cGsSt, Expr.eval, Expr.v0]

private theorem cAcceptE_fsGsInv {O' : Ops S_fs} {Γ' : List (Ty S_fs)} {tStar : ℕ}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpTyFS)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpTyFS) (pos : Expr O' Γ' posTy) (ρ : Env Γ')
    (hg : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (s.eval ρ))
    (hv : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (st'.eval ρ)) :
    fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar
      ((cAcceptE L s p st' pos).eval ρ) := by
  have hst : ((cAcceptE L s p st' pos).eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
    cases hp : (p.eval ρ : Bool) <;>
      simp [cAcceptE, cGsMk, cGsSt, pSet_eval_st_fs, cDeleteE_st_fs, Expr.eval, Expr.v0, hp]
  unfold fsGsInv; rw [hst]
  cases (p.eval ρ) <;> exact ⟨by simp [hg.1, hv], by simp [hg.2, hv]⟩

private theorem cGsSetStP_fsGsInv {O' : Ops S_fs} {Γ' : List (Ty S_fs)} {tStar : ℕ}
    (s : Expr O' Γ' (cGsTy vpTyFS)) (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpTyFS) (ρ : Env Γ')
    (hg : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (s.eval ρ))
    (hv : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (st'.eval ρ)) :
    fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar
      ((cGsSetStP s p st').eval ρ) := by
  have hst : ((cGsSetStP s p st').eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
    cases hp : (p.eval ρ : Bool) <;>
      simp [cGsSetStP, cGsMk, cGsSt, pSet_eval_st_fs, Expr.eval, Expr.v0, hp]
  unfold fsGsInv; rw [hst]
  cases (p.eval ρ) <;> exact ⟨by simp [hg.1, hv], by simp [hg.2, hv]⟩

private theorem cGsSetWin_fsGsInv {O' : Ops S_fs} {Γ' : List (Ty S_fs)} {tStar : ℕ}
    (s : Expr O' Γ' (cGsTy vpTyFS)) (w : Expr O' Γ' .bool) (ρ : Env Γ')
    (hg : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (s.eval ρ)) :
    fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar
      ((cGsSetWin s w).eval ρ) :=
  fsGsInv_of_st_eq (by simp [cGsSetWin, cGsMk, cGsSt, Expr.eval, Expr.v0]) hg

private theorem fsGsInv_ite {tStar : ℕ} {b : Bool} {g₁ g₂ : (cGsTy vpTyFS).denote}
    (h₁ : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar g₁)
    (h₂ : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar g₂) :
    fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (if b then g₁ else g₂) := by
  cases b <;> assumption

private theorem cRecordE_fsGsInv {O' : Ops S_fs} {Γ' : List (Ty S_fs)} {tStar : ℕ}
    (L Δ : ℕ) (s : Expr O' Γ' (cGsTy vpTyFS)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpTyFS) (r : Expr O' Γ' cRecTy) (ch : Expr O' Γ' .bool) (ρ : Env Γ')
    (hg : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (s.eval ρ))
    (hv : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (st'.eval ρ)) :
    fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar
      ((cRecordE L Δ s p st' r ch).eval ρ) := by
  have hst : ((cRecordE L Δ s p st' r ch).eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
    cases hp : (p.eval ρ : Bool) <;>
      simp [cRecordE, cGsMk, cGsSt, pSet_eval_st_fs, Expr.eval, Expr.v0, hp]
  unfold fsGsInv; rw [hst]
  cases (p.eval ρ) <;> exact ⟨by simp [hg.1, hv], by simp [hg.2, hv]⟩

private theorem cAfterCorrE_fsGsInv {O' : Ops S_fs} {Γ' : List (Ty S_fs)} {tStar : ℕ}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpTyFS)) (p : Expr O' Γ' .bool) (ρ : Env Γ')
    (hg : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (s.eval ρ)) :
    fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar
      ((cAfterCorrE L s p).eval ρ) :=
  fsGsInv_of_st_eq (by simp [cAfterCorrE, cLeakE_st_fs, cGsMk, cGsSt, Expr.eval, Expr.v0]) hg

private structure PotOKInv {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α : Type}
    (P : ι' → Prop) [DecidablePred P] (Inv : α → Prop) (B : α → ℕ)
    (oa : OracleComp T' α) (n : ℕ) : Prop where
  run : ∀ {β : Type} (k : α → OracleComp T' β),
    (∀ a, Inv a → (k a).IsQueryBoundP P (B a)) → (oa >>= k).IsQueryBoundP P n

private theorem PotOKInv.bindPot {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type}
    {P : ι' → Prop} [DecidablePred P] {Inv₁ : α → Prop} {Inv₂ : γ → Prop}
    {B₁ : α → ℕ} {B₂ : γ → ℕ} {oa : OracleComp T' α} {f : α → OracleComp T' γ} {n : ℕ}
    (h1 : PotOKInv P Inv₁ B₁ oa n) (h2 : ∀ a, Inv₁ a → PotOKInv P Inv₂ B₂ (f a) (B₁ a)) :
    PotOKInv P Inv₂ B₂ (oa >>= f) n :=
  ⟨fun k hk => by rw [bind_assoc]; exact h1.run _ (fun a ha => (h2 a ha).run k hk)⟩

private theorem potInv_ret {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ : Ty S'} {Inv : τ.denote → Prop} {B : τ.denote → ℕ}
    {e : Expr O' Γ' τ} {ρ : Env Γ'} {n : ℕ}
    (hInv : Inv (e.eval ρ)) (hB : B (e.eval ρ) ≤ n) :
    PotOKInv P Inv B ((Comp.ret (I := I') e).eval ρ) n :=
  ⟨fun _ hk => by rw [eval_ret, pure_bind]; exact (hk (e.eval ρ) hInv).mono hB⟩

private theorem potInv_ite {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ : Ty S'} {Inv : τ.denote → Prop} {B : τ.denote → ℕ}
    {cond : Expr O' Γ' .bool} {t f : Comp O' I' Γ' τ} {ρ : Env Γ'} {n : ℕ}
    (ht : cond.eval ρ = true → PotOKInv P Inv B (t.eval ρ) n)
    (hf : cond.eval ρ = false → PotOKInv P Inv B (f.eval ρ) n) :
    PotOKInv P Inv B ((Comp.ite cond t f).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases hc : cond.eval ρ
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact (hf hc).run k hk
    · simp only [↓reduceIte]; exact (ht hc).run k hk⟩

private theorem potInv_caseOpt {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {α τ : Ty S'} {Inv : τ.denote → Prop} {B : τ.denote → ℕ}
    {scrut : Expr O' Γ' (.opt α)} {onNone : Comp O' I' Γ' τ} {onSome : Comp O' I' (α :: Γ') τ}
    {ρ : Env Γ'} {n : ℕ}
    (hNone : scrut.eval ρ = none → PotOKInv P Inv B (onNone.eval ρ) n)
    (hSome : ∀ v, scrut.eval ρ = some v → PotOKInv P Inv B (onSome.eval (.cons v ρ)) n) :
    PotOKInv P Inv B ((Comp.caseOpt scrut onNone onSome).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases h : scrut.eval ρ with
    | none => exact (hNone h).run k hk
    | some v => exact (hSome v h).run k hk⟩

private theorem potInv_caseSum {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {α β τ : Ty S'} {Inv : τ.denote → Prop} {B : τ.denote → ℕ}
    {scrut : Expr O' Γ' (.sum α β)} {onInl : Comp O' I' (α :: Γ') τ}
    {onInr : Comp O' I' (β :: Γ') τ} {ρ : Env Γ'} {n : ℕ}
    (hInl : ∀ v, scrut.eval ρ = .inl v → PotOKInv P Inv B (onInl.eval (.cons v ρ)) n)
    (hInr : ∀ v, scrut.eval ρ = .inr v → PotOKInv P Inv B (onInr.eval (.cons v ρ)) n) :
    PotOKInv P Inv B ((Comp.caseSum scrut onInl onInr).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases h : scrut.eval ρ with
    | inl v => exact (hInl v h).run k hk
    | inr v => exact (hInr v h).run k hk⟩

private theorem potInv_bind {Γ' : List (Ty S_fs)} {τ₁ τ₂ : Ty S_fs}
    {Inv : τ₂.denote → Prop} {B : τ₂.denote → ℕ}
    {m : Comp OO_fs II_fs Γ' τ₁} {k : Comp OO_fs II_fs (τ₁ :: Γ') τ₂}
    {ρ : Env Γ'} (r : ℕ) {n : ℕ}
    (hmn : m.queries (fun _ => 1) (fun _ => 0) + r ≤ n)
    (hk : ∀ x, PotOKInv P_fs Inv B (k.eval (.cons x ρ)) r) :
    PotOKInv P_fs Inv B ((Comp.bind m k).eval ρ) n :=
  ⟨fun k' hk' => by
    rw [eval_bind, bind_assoc]
    have hm := Comp.queryBound_eval P_fs (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) fsIface_fwdU_zero m ρ
    exact (isQueryBoundP_bind hm (fun x _ => (hk x).run k' hk')).mono hmn⟩

private theorem potOKInv_simulateQ_handlerImpl_step1
    {S' : Sig} {O' : Ops S'} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {I' : Iface S' T'}
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S' G} {σ : Ty S'} {α : Type}
    {P : ι' → Prop} [DecidablePred P]
    (Inv : σ.denote → Prop) (B : σ.denote → ℕ)
    (hU : ∀ n, (I'.fwdU n).IsQueryBoundP P 0)
    (h : Comp O' I' [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ (m : ℕ) q s, Inv s →
      PotOKInv P (fun x : C.R.denote × σ.denote => Inv x.2)
        (fun x : C.R.denote × σ.denote => m + B x.2)
        (h.eval (.cons s (.cons q .nil))) (1 + m + B s))
    {mx : OracleComp (unifSpec + G) α} {qAdv : ℕ}
    (hq : mx.IsQueryBoundP (isGameQuery (G := G)) qAdv) {st : σ.denote} (hst : Inv st) :
    PotOKInv P (fun x : α × σ.denote => Inv x.2) (fun _ => 0)
      ((simulateQ (handlerImpl (C := C) h) mx).run st) (qAdv + B st) := by
  induction mx using OracleComp.inductionOn generalizing qAdv st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact ⟨fun k hk => by simpa using (hk (a, st) hst).mono (Nat.zero_le (qAdv + B st))⟩
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change PotOKInv P _ _
        ((do let u ← I'.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2)
        (qAdv + B st)
      refine ⟨fun k' hk' => ?_⟩
      rw [bind_assoc, bind_assoc]
      refine (isQueryBoundP_bind (hU uq) (fun u _ => ?_)).mono (Nat.zero_add _).le
      rw [pure_bind]
      exact (ih u (by simpa [isGameQuery] using hq.2 u) hst).run k' hk'
    · have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      change PotOKInv P _ _
        ((do
            let p ← h.eval (.cons st (.cons (C.qenc gq) .nil))
            return (C.rdec gq p.1, p.2)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2)
        ((m + 1) + B st)
      rw [show (m + 1) + B st = 1 + m + B st by omega, bind_assoc]
      refine PotOKInv.bindPot (hStep m (C.qenc gq) st hst) (fun p hp => ?_)
      rw [pure_bind]
      exact ih (C.rdec gq p.1) (by simpa [isGameQuery] using hq.2 (C.rdec gq p.1)) hp

private theorem lookupFC_potInv (L : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ikE : Expr OO_fs Γ' (.base .i)) (ρ : Env Γ') (m : ℕ) :
    PotOKInv P_fs (fun _ => True)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((lookupFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE ikE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold lookupFC; rw [eval_bind_ret]
  refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
  · refine potInv_bind
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ))
      (by simp [Comp.queries]) (fun _ => ?_)
    exact potInv_ret trivial (by simp [Expr.eval, Expr.v1])
  · exact potInv_ret trivial (by simp [Expr.eval, Expr.v1])

private theorem rootFSC_potInv (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (tE : Expr OO_fs Γ' .nat) (ikE : Expr OO_fs Γ' (.base .i))
    (σE : Expr OO_fs Γ' (.base .sig)) (ρ : Env Γ') (m : ℕ) :
    PotOKInv P_fs (fun r => r.1.2.2.isSome = true → tE.eval ρ = mo.tStar)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((rootFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold rootFSC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => ?_) (fun _ => ?_)
  · exact potInv_ret (by simp [Expr.eval]) (by simp [Expr.eval, Expr.v0])
  · refine potInv_ite (fun hEq => ?_) (fun _ => ?_)
    · have htEq : tE.eval ρ = mo.tStar := by
        simpa [Expr.eval, Expr.v0] using hEq
      refine potInv_ite (fun _ => ?_) (fun _ => ?_)
      · refine potInv_bind
          (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ))
          (by simp [Comp.queries]) (fun _ => ?_)
        refine potInv_bind
          (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ))
          (by simp [Comp.queries]) (fun _ => ?_)
        exact potInv_ret (fun _ => htEq) (by simp [Expr.eval, Expr.v2])
      · rw [eval_bind]
        set ρ₁ := Env.cons ((hE.pair (tE.pair (ikE.pair σE))).eval ρ) ρ
        have hLk := lookupFC_potInv (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
          L (.fst (Expr.v0 (O := OO_fs))) (.fst (.snd (.snd .v0))) ρ₁ m
        refine PotOKInv.bindPot hLk (fun _ _ => ?_)
        exact potInv_ret (fun _ => htEq) (by simp [Expr.eval, Expr.v0])
    · refine potInv_ite (fun _ => ?_) (fun _ => ?_)
      · refine potInv_bind
          (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ))
          (by simp [Comp.queries]) (fun _ => ?_)
        exact potInv_ret (by simp [Expr.eval]) (by simp [Expr.eval, Expr.v1])
      · exact potInv_ret (by simp [Expr.eval]) (by simp [Expr.eval, Expr.v0])

private theorem extOfE_fst_true_imp_isSome (L j : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (sidE : Expr OO_fs Γ' (.opt (.base .i))) (ρ : Env Γ')
    (h : ((extOfE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) L j hE sidE).eval ρ).1 = true) :
    (sidE.eval ρ).isSome = true := by
  unfold extOfE at h
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at h
  cases hs : sidE.eval ρ with
  | none => simp [hs, Expr.eval] at h
  | some _ => rfl

private theorem initFSEStateC_potInv (L : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (bE : Expr OO_fs Γ' .bool) (ρ : Env Γ') (m : ℕ) :
    PotOKInv P_fs
      (fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar)
      (fun es => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) es)
      ((initFSEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j bE).eval ρ)
      (m + 1) := by
  unfold initFSEStateC; rw [eval_bind_ret]
  refine potInv_bind (m + 1) (by simp [Comp.queries]) (fun kr => ?_)
  refine potInv_bind (m + 1) (by simp [Comp.queries]) (fun kc => ?_)
  rw [eval_bind]
  set ρ₁ := Env.cons kc (Env.cons kr (Env.cons (bE.eval ρ) ρ))
  have hRt := rootFSC_potInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo
    fsHsEmptyE (.nat 0) (Expr.op (O := OO_fs) CKAOp.lamI .unit)
    (Expr.op (O := OO_fs) CKAOp.prngInit .v1) ρ₁ m
  have hEmpPot : fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsEmptyE (O' := OO_fs)).eval ρ₁) = 1 := rfl
  rw [hEmpPot] at hRt
  refine PotOKInv.bindPot hRt (fun rtOut hSid => ?_)
  refine potInv_ret ?_ (by simp [fsPot, esMk, Expr.eval, Expr.v0])
  set ρ₂ := Env.cons rtOut ρ₁
  have hExtImp : ∀ (hext : (Expr.eval (O := OO_fs) (extOfE L j (.snd .v0) (.snd (.snd (.fst .v0)))) ρ₂).1 = true),
      mo.tStar = 0 := by
    intro hext
    exact (hSid (extOfE_fst_true_imp_isSome L j _ _ ρ₂ hext)).symm
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hvS
    simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, Expr.eval, Expr.v0] at hvS
  · intro hvR
    simp only [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, tset_eval_eq_update,
      partyDec_partyEnc, Expr.eval, Expr.v0, Env.get_cons_zero] at hvR ⊢
    by_cases ht0 : mo.tStar = 0
    · rw [ht0]; rfl
    · simp [Function.update, ht0] at hvR
  · intro hvS
    simp only [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, partyDec_partyEnc,
      Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hvS ⊢
    by_cases hext : (Expr.eval (O := OO_fs) (extOfE L j (.snd .v0) (.snd (.snd (.fst .v0)))) ρ₂).1 = true
    · rw [hExtImp hext]; rfl
    · simp only [Expr.v0] at hext
      simp [hext, ite_eval, Expr.eval] at hvS
  · intro hvR
    simp [esMk, cGsInitE, cGsMk, mkPartiesE, letE_eval, vpMk, Expr.eval, Expr.v0] at hvR

private theorem fsStartSendC_potInv (L : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (tE : Expr OO_fs Γ' .nat) (γE : Expr OO_fs Γ' (.base .γ)) (σE : Expr OO_fs Γ' (.base .sig))
    (rE : Expr OO_fs Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m : ℕ) :
    PotOKInv P_fs
      (fun r => ∀ γ' T' σ' ssv, r.1 = some (γ', T', σ', ssv) → ssv = none → tE.eval ρ = mo.tStar)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((fsStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j hE ctxE pE tE γE σE rE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsStartSendC; rw [eval_bind_ret]
  refine potInv_bind
    (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ))
    (by simp [Comp.queries]) (fun coins => ?_)
  rw [eval_bind]
  set ρ₁ := Env.cons coins (Env.cons ((hE.pair (tE.pair (γE.pair (σE.pair rE)))).eval ρ) ρ)
  have hRt := rootFSC_potInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo
    (.fst .v1) (.fst (.snd .v1))
    (.snd (.snd (Expr.op (O := OO_fs) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
    (.fst (.snd (.snd (.snd .v1)))) ρ₁ m
  have hEq : fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((Expr.fst (Expr.v1 (O := OO_fs))).eval ρ₁) =
      fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := rfl
  rw [hEq] at hRt
  refine PotOKInv.bindPot hRt (fun rtOut hSid => ?_)
  refine potInv_ret ?_ (by simp [Expr.eval, Expr.v0])
  intro γ' T' σ' ssv hRes hSsv
  set ρ₂ := Env.cons rtOut ρ₁
  simp only [Expr.eval, Expr.v0, Option.some.injEq, Prod.mk.injEq] at hRes
  obtain ⟨_, _, _, hSsvEq⟩ := hRes
  rw [← hSsvEq] at hSsv
  by_cases hext : (Expr.eval (O := OO_fs) (extOfE L j (.snd .v0) (.snd (.snd (.fst .v0)))) ρ₂).1 = true
  · exact hSid (extOfE_fst_true_imp_isSome L j _ _ ρ₂ hext)
  · simp only [Expr.v0] at hext
    simp [hext, ite_eval, Expr.eval] at hSsv

private theorem fsStartRecvC_potInv (L : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (tE : Expr OO_fs Γ' .nat) (γE : Expr OO_fs Γ' (.base .γ)) (σE : Expr OO_fs Γ' (.base .sig))
    (tnE : Expr OO_fs Γ' (.base .t)) (ρ : Env Γ') (m : ℕ) :
    PotOKInv P_fs (fun _ => True)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((fsStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j hE ctxE pE tE γE σE tnE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsStartRecvC; rw [eval_bind_ret]
  refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
  · refine potInv_ite (fun _ => ?_) (fun _ => ?_)
    · refine potInv_ite (fun _ => ?_) (fun _ => ?_)
      · exact potInv_ret trivial (by simp [Expr.eval, Expr.v0])
      · rw [eval_bind]
        refine PotOKInv.bindPot (lookupFC_potInv L _ _ _ m) (fun _ _ => ?_)
        exact potInv_ret trivial (by simp [Expr.eval, Expr.v0])
    · exact potInv_ret trivial (by simp [Expr.eval, Expr.v0])
  · exact potInv_ret trivial (by simp [Expr.eval, Expr.v1])

private theorem fsCommitC_potInv {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (oldE newE : Expr OO_fs Γ' vpTyFS) (ρ : Env Γ') (m : ℕ) :
    PotOKInv P_fs (fun r => r.1 = some (newE.eval ρ))
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((fsCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE oldE newE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsCommitC
  exact potInv_ret (by simp [Expr.eval]) (by simp [Expr.eval])

private theorem fsFsRecvC_potInv (L B : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (tE : Expr OO_fs Γ' .nat) (rsvE : Expr OO_fs Γ' (.opt (.base .rs)))
    (hdrE : Expr OO_fs Γ' hdrTyFS) (eE : Expr OO_fs Γ' (.base .ct))
    (recE : Expr OO_fs Γ' (.opt cRecTy)) (ρ : Env Γ') (m : ℕ) :
    PotOKInv P_fs (fun _ => True)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((fsFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B hE ctxE pE tE rsvE hdrE eE recE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsFsRecvC; rw [eval_bind_ret]
  refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
  · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · refine potInv_bind
        (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ))
        (by simp [Comp.queries]; omega) (fun _ => ?_)
      refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInv_ret trivial (by simp [Expr.eval, Expr.v1])
      · refine potInv_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · exact potInv_ret trivial (by simp [Expr.eval, Expr.v3])
        · exact potInv_ret trivial (by simp [Expr.eval, Expr.v3])
    · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInv_ret trivial
          (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega)
      · exact potInv_ret trivial (by simp [Expr.eval]; omega)
  · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · exact potInv_ret trivial
        (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega)
    · exact potInv_ret trivial
        (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega)

private theorem fsFsSendC_potInv (Δcka : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (tE : Expr OO_fs Γ' .nat) (ssvE : Expr OO_fs Γ' (.opt (.base .ss)))
    (hdrE : Expr OO_fs Γ' hdrTyFS) (mE : Expr OO_fs Γ' (.base .msg))
    (pairE : Expr OO_fs Γ' (.opt (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ') (m : ℕ) :
    PotOKInv P_fs
      (fun r => ∀ v' ct, r.1 = some (v', ct) → v' = none → ssvE.eval ρ = none)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((fsFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka hE ctxE pE tE ssvE hdrE mE pairE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsFsSendC; rw [eval_bind_ret]
  refine potInv_caseOpt (fun hSsvNone => ?_) (fun _ _ => ?_)
  · have hSsv : ssvE.eval ρ = none := by
      simpa [Expr.eval, Expr.v0] using hSsvNone
    refine potInv_caseOpt (fun hExtNone => ?_) (fun _ _ => ?_)
    · have hExt : (hE.eval ρ).2.2.2.2.2.2 = none := by
        simpa [fsHsExt, Expr.eval, Expr.v0] using hExtNone
      rw [eval_bind]
      refine PotOKInv.bindPot
        (Inv₁ := fun _ => True)
        (B₁ := fun okH =>
          if okH.1 then
            1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) okH.2
          else
            m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) okH.2)
        ?_ (fun okH _ => ?_)
      · refine potInv_ite (fun hCond => ?_) (fun _ => ?_)
        · have hSCF : (hE.eval ρ).2.2.2.2.2.1 = false := by
            simp only [fsHsSCorr, Expr.eval, Expr.v0, Env.get_cons_zero,
              Bool.and_eq_true, Bool.not_eq_true'] at hCond
            exact hCond.2
          have hPot1 : fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
              (hE.eval ρ) = 1 := by
            simp [fsHPot, hExt, hSCF]
          refine potInv_bind (m + 1) (by simp [hPot1, Comp.queries]; omega) (fun _ => ?_)
          refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInv_ret trivial (by simp [hPot1, Expr.eval, Expr.v1])
          · exact potInv_ret trivial (by simp [Expr.eval]; omega)
        · exact potInv_ret trivial (by simp [Expr.eval, Expr.v0])
      · refine potInv_ite (fun hNotOk => ?_) (fun hNotOk => ?_)
        · have hOkF : okH.1 = false := by
            simpa [Expr.eval, Expr.v0] using hNotOk
          exact potInv_ret (fun _ _ h => by simp [Expr.eval] at h)
            (by simp [hOkF, Expr.eval, Expr.v0])
        · have hOkT : okH.1 = true := by
            cases hok : okH.1
            · simp [Expr.eval, Expr.v0, hok] at hNotOk
            · rfl
          refine potInv_bind
            (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) okH.2)
            (by simp [hOkT, Comp.queries]; omega) (fun _ => ?_)
          refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInv_ret (fun _ _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v1])
          · exact potInv_ret (fun _ _ _ _ => hSsv) (by simp [Expr.eval, Expr.v2])
    · exact potInv_ret (fun _ _ _ _ => hSsv) (by simp [Expr.eval]; omega)
  · refine potInv_ret (fun v' ct hEq hVNone => ?_)
      (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega)
    simp [Expr.eval, hVNone] at hEq

private theorem fsRevealC_potInv (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (vpE : Expr OO_fs Γ' vpTyFS) (ρ : Env Γ') (m : ℕ)
    (hv : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (vpE.eval ρ)) :
    PotOKInv P_fs (fun _ => True)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((fsRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo hE ctxE pE vpE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsRevealC; rw [eval_bind_ret, eval_bind]
  by_cases hVS : (vpE.eval ρ).2.2.1 = some none
  · have hNotVR : (vpE.eval ρ).2.2.2.1 mo.tStar ≠ some none := by
      intro hVR
      have hsT := hv.1 hVS
      have hsF := hv.2 hVR
      rw [hsT] at hsF; cases hsF
    refine PotOKInv.bindPot
      (Inv₁ := fun _ => True)
      (B₁ := fun sOut =>
        m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) sOut.2)
      ?_ (fun sOut _ => ?_)
    · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInv_ret trivial (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
      · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · refine potInv_bind
              (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ))
              (by simp [Comp.queries]; omega) (fun _ => ?_)
            refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
            · exact potInv_ret trivial (by simp [Expr.eval, Expr.v2])
            · exact potInv_ret trivial (by simp [Expr.eval])
          · exact potInv_ret trivial
              (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega)
        · exact potInv_ret trivial
            (by simp only [Expr.eval, Expr.v1, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega)
    · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInv_ret trivial (by simp [Expr.eval, Expr.v0])
      · rw [eval_bind]
        refine PotOKInv.bindPot
          (Inv₁ := fun _ => True)
          (B₁ := fun rOut =>
            m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) rOut.2)
          ?_ (fun rOut _ => ?_)
        · refine potInv_caseOpt (fun _ => ?_) (fun rsv hRsv => ?_)
          · exact potInv_ret trivial (by simp [Expr.eval, Expr.v1])
          · refine potInv_caseOpt (fun hRsvNone => ?_) (fun _ _ => ?_)
            · exfalso
              simp only [vpVR, Expr.eval, Expr.v0, Expr.v2,
                Env.get_cons_zero, Env.get_cons_succ] at hRsv hRsvNone
              subst hRsvNone
              exact hNotVR hRsv
            · exact potInv_ret trivial (by simp [Expr.eval, Expr.v3])
        · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInv_ret trivial (by simp [Expr.eval, Expr.v0])
          · refine potInv_bind
              (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) rOut.2)
              (by simp [rangeListC_queries]) (fun _ => ?_)
            exact potInv_ret trivial (by simp [Expr.eval, Expr.v2])
  · refine PotOKInv.bindPot
      (Inv₁ := fun _ => True)
      (B₁ := fun sOut =>
        1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) sOut.2)
      ?_ (fun sOut _ => ?_)
    · refine potInv_caseOpt (fun _ => ?_) (fun ssv hSsv => ?_)
      · exact potInv_ret trivial (by simp [Expr.eval, Expr.v0])
      · refine potInv_caseOpt (fun hSsvNone => ?_) (fun _ _ => ?_)
        · exfalso
          simp only [vpVS, Expr.eval, Expr.v0, Env.get_cons_zero] at hSsv hSsvNone
          subst hSsvNone
          exact hVS hSsv
        · exact potInv_ret trivial (by simp [Expr.eval, Expr.v2])
    · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInv_ret trivial
          (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
      · rw [eval_bind]
        refine PotOKInv.bindPot
          (Inv₁ := fun _ => True)
          (B₁ := fun rOut =>
            m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) rOut.2)
          ?_ (fun rOut _ => ?_)
        · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInv_ret trivial
              (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega)
          · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
            · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
              · refine potInv_ite (fun _ => ?_) (fun _ => ?_)
                · exact potInv_ret trivial
                    (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega)
                · refine potInv_bind
                    (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) sOut.2)
                    (by simp [Comp.queries]; omega) (fun _ => ?_)
                  refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
                  · exact potInv_ret trivial (by simp [Expr.eval, Expr.v3])
                  · exact potInv_ret trivial (by simp [Expr.eval])
              · exact potInv_ret trivial
                  (by simp only [Expr.eval, Expr.v3, Env.get_cons_succ, Env.get_cons_zero]; omega)
            · exact potInv_ret trivial
                (by simp only [Expr.eval, Expr.v3, Env.get_cons_succ, Env.get_cons_zero]; omega)
        · refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInv_ret trivial (by simp [Expr.eval, Expr.v0])
          · refine potInv_bind
              (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) rOut.2)
              (by simp [rangeListC_queries]) (fun _ => ?_)
            exact potInv_ret trivial (by simp [Expr.eval, Expr.v2])

private theorem vSendStep1C_hooksFSC_potInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (sE : Expr OO_fs Γ' vpTyFS) (rE : Expr OO_fs Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m : ℕ)
    (hs : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (sE.eval ρ)) :
    PotOKInv P_fs
      (fun r => ∀ s1, r.1 = some s1 →
        fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar s1)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((vSendStep1C (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) hE ctxE pE sE rE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold vSendStep1C; rw [eval_bind_ret]
  refine potInv_ite (fun hSends => ?_) (fun _ => ?_)
  · rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at hSends
    simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hSends
    dsimp only [hooksFSC]; rw [eval_bind]
    refine PotOKInv.bindPot (fsStartSendC_potInv L mo j _ _ _ _ _ _ _ _ m) (fun stOut hSt => ?_)
    refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
      (fun tup hTup => potInv_ret ?_ (by simp [Expr.eval, Expr.v1]))
    intro s1 hs1
    simp only [Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
      Option.some.injEq] at hTup hs1
    subst hs1
    refine ⟨?_, ?_⟩
    · intro hvS
      simp only [vpMk, vpId, Expr.eval, Option.some.injEq] at hvS ⊢
      have htEq : (sE.eval ρ).2.2.2.2.2.2 + 1 = mo.tStar :=
        hSt tup.1 tup.2.1 tup.2.2.1 tup.2.2.2 hTup hvS
      simpa [htEq] using hSends
    · intro hvR
      exact hs.2 hvR
  · exact potInv_ret
      (fun s1 hs1 => by
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hs1
        subst hs1; exact hs)
      (by simp [Expr.eval, Expr.v0])

private theorem vSendC_hooksFSC_potInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (sE : Expr OO_fs Γ' vpTyFS) (mE : Expr OO_fs Γ' (.base .msg))
    (pairE : Expr OO_fs Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (rE : Expr OO_fs Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m : ℕ)
    (hs : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (sE.eval ρ)) :
    PotOKInv P_fs
      (fun r => ∀ vp' ct, r.1 = some (vp', ct) →
        fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar vp')
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((vSendC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) hE ctxE pE sE mE pairE rE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  refine PotOKInv.bindPot
    (vSendStep1C_hooksFSC_potInv L B Δcka mo j _ _ _ _ _ _ (1 + m) hs)
    (fun stepOut hStep => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret (fun _ _ h => by simp [Expr.eval] at h)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun s1 hs1 => ?_)
  have hs1Inv : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar s1 :=
    hStep s1 (by simpa [Expr.eval, Expr.v0] using hs1)
  refine potInv_caseOpt (fun _ => ?_) (fun v hvEq => ?_)
  · refine potInv_ret ?_
      (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega)
    intro vp' ct hEq
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq, Prod.mk.injEq] at hEq
    rcases hEq with ⟨rfl, _⟩; exact hs1Inv
  · dsimp only [hooksFSC]; rw [eval_bind]
    refine PotOKInv.bindPot (fsFsSendC_potInv Δcka _ _ _ _ _ _ _ _ _ m) (fun fsOut hFs => ?_)
    refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
      (fun vct hVct => potInv_ret ?_ (by simp [Expr.eval, Expr.v1]))
    intro vp' ct hEq
    simp only [vpSetVS, letE_eval, vpMk, vpId, vpRoot, vpVR, vpΓ, vpTcur, vpTcurNat,
      Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
      Option.some.injEq, Prod.mk.injEq] at hVct hEq hvEq
    rcases hEq with ⟨rfl, _⟩
    refine ⟨?_, hs1Inv.2⟩
    intro hvNone
    simp only [Option.some.injEq] at hvNone
    have hvIsNone : v = none := hFs vct.1 vct.2 hVct hvNone
    subst hvIsNone
    exact hs1Inv.1 hvEq

private theorem vRecvStep1C_hooksFSC_potInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (sE : Expr OO_fs Γ' vpTyFS) (cE : Expr OO_fs Γ' hdrCtTyFS) (ρ : Env Γ') (m : ℕ)
    (hs : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (sE.eval ρ))
    (hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false) :
    PotOKInv P_fs
      (fun r => ∀ s1, r.1 = some (some s1) →
        s1.1 = (sE.eval ρ).1 ∧
        fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar s1)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((vRecvStep1C (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) hE ctxE pE sE cE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold vRecvStep1C; rw [eval_bind_ret]
  refine potInv_ite (fun _ => ?_) (fun _ => ?_)
  · refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
      (fun _ _ => ?_)
    dsimp only [hooksFSC]; rw [eval_bind]
    refine PotOKInv.bindPot (fsStartRecvC_potInv L mo j _ _ _ _ _ _ _ _ m) (fun _ _ => ?_)
    refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
      (fun _ _ => potInv_caseOpt
        (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v1]))
        (fun _ _ => potInv_ret ?_ (by simp [Expr.eval, Expr.v2])))
    intro s1 hs1
    simp only [vpMk, vpId, vpVS, vpVR, tset_eval_eq_update, Expr.eval, Expr.v0, Expr.v4,
      Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq] at hs1
    subst hs1
    refine ⟨rfl, hs.1, ?_⟩
    intro hvR
    by_cases ht : mo.tStar = (cE.eval ρ).1.1
    · simpa [ht] using hNotSends
    · simp only [Function.update, ht, ↓reduceIte] at hvR
      exact hs.2 hvR
  · exact potInv_ret
      (fun s1 hs1 => by
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hs1
        subst hs1; exact ⟨rfl, hs⟩)
      (by simp [Expr.eval, Expr.v0])

private theorem vRecvC_hooksFSC_potInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (hE : Expr OO_fs Γ' hsTyFS) (ctxE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (sE : Expr OO_fs Γ' vpTyFS) (cE : Expr OO_fs Γ' hdrCtTyFS) (recE : Expr OO_fs Γ' (.opt cRecTy))
    (ρ : Env Γ') (m : ℕ)
    (hs : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (sE.eval ρ)) :
    PotOKInv P_fs
      (fun r => ∀ s2 t0 idx mOut, r.1 = some (some (s2, t0, idx, mOut)) →
        fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar s2)
      (fun r => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) r.2)
      ((vRecvC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) hE ctxE pE sE cE recE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold vRecvC; rw [eval_bind_ret]
  refine potInv_ite
    (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun hOrF => ?_)
  have hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false := by
    simp only [orE, ite_eval] at hOrF
    rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at hOrF
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hOrF
    cases hsnd : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1
    · rfl
    · simp [hsnd] at hOrF
  rw [eval_bind]
  refine PotOKInv.bindPot
    (vRecvStep1C_hooksFSC_potInv L B Δcka mo j _ _ _ _ _ _ (1 + m) hs hNotSends)
    (fun stepOut hStep => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun stepInner hIn => potInv_caseOpt
      (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
        (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
      (fun s1 hs1 => ?_))
  obtain ⟨hs1Id, hs1Inv⟩ := hStep s1 (by
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hIn hs1
    rw [hIn, hs1])
  refine potInv_caseOpt
    (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
      (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega))
    (fun _ _ => ?_)
  dsimp only [hooksFSC]; rw [eval_bind]
  refine PotOKInv.bindPot (fsFsRecvC_potInv L B _ _ _ _ _ _ _ _ _ m) (fun _ _ => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
    (fun _ _ => potInv_caseOpt
      (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v1]))
      (fun _ _ => potInv_ret ?_ (by simp [Expr.eval, Expr.v2])))
  intro s2 t0 idx mOut hEq
  simp only [vpSetVR, letE_eval, vpMk, vpId, vpRoot, vpVS, vpVR, vpΓ, vpTcur, vpTcurNat,
    tset_eval_eq_update, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
    Expr.v7, Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq, Prod.mk.injEq] at hEq
  rcases hEq with ⟨rfl, _⟩
  refine ⟨hs1Inv.1, ?_⟩
  intro hvR
  by_cases ht : mo.tStar = (cE.eval ρ).1.1
  · rw [hs1Id, ht]; exact hNotSends
  · simp only [Function.update, ht, ↓reduceIte] at hvR
    exact hs1Inv.2 hvR

private theorem commitEC_hooksFSC_potInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (esE : Expr OO_fs Γ' esTyFS) (sE : Expr OO_fs Γ' (cGsTy vpTyFS)) (pE : Expr OO_fs Γ' .bool)
    (oldE newE : Expr OO_fs Γ' vpTyFS) (posE : Expr OO_fs Γ' posTy) (ρ : Env Γ') (m : ℕ)
    (hes : fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (esE.eval ρ))
    (hg : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (sE.eval ρ))
    (hnew : fsVpInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (newE.eval ρ)) :
    PotOKInv P_fs
      (fun r =>
        fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar r.2 ∧
        (∀ g', r.1 = some g' →
          fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar g'))
      (fun r => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) r.2)
      ((commitEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) L esE sE pE oldE newE posE).eval ρ)
      (m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (esE.eval ρ)) := by
  unfold commitEC; dsimp only [hooksFSC]; rw [eval_bind_ret, eval_bind]
  refine PotOKInv.bindPot (fsCommitC_potInv _ _ _ _ _ _ m) (fun cOut hcEq => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret ⟨hes, fun _ h => by simp [Expr.eval] at h⟩
      (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun new' hSome => potInv_ret ?_ (by simp [fsPot, esMk, Expr.eval, Expr.v1]))
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hcEq hSome
  rw [hcEq] at hSome; injection hSome with hNewEq; subst hNewEq
  refine ⟨hes, fun g' hgEq => ?_⟩
  simp only [Expr.eval, Option.some.injEq] at hgEq
  subst hgEq
  exact cGsSetStP_fsGsInv _ _ _ _
    (cAcceptE_fsGsInv L sE pE newE posE ρ hg hnew) hnew

private theorem transmitEC_hooksFSC_potInv (L B Δcka qep : ℕ) (mo : Mode) (j : ℕ) (π : Policy) {Γ'}
    (esE : Expr OO_fs Γ' esTyFS)
    (argE : Expr OO_fs Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))))
    (ρ : Env Γ') (m : ℕ)
    (hes : fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (esE.eval ρ)) :
    PotOKInv P_fs
      (fun r => fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar r.2)
      (fun r => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) r.2)
      ((transmitEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep π esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (esE.eval ρ)) := by
  unfold transmitEC; rw [eval_bind_ret]
  refine potInv_ite
    (fun _ => potInv_ret hes (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => potInv_caseOpt
      (fun _ => potInv_ret hes (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
      (fun s1 hs1 => ?_))
  have hs1Inv : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar s1 :=
    fsGsInv_of_st_eq (cEpMgmtE_some_st_fs _ _ _ _ _ _ hs1) hes
  refine potInv_ite
    (fun _ => potInv_ret hes
      (by simp only [fsPot, esSetAbort, esMk, esG, esH, Expr.eval, Expr.v0, Expr.v1,
        Env.get_cons_succ, Env.get_cons_zero]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  refine PotOKInv.bindPot
    (vSendC_hooksFSC_potInv L B Δcka mo j _ _ _ _ _ _ _ _ m (fsVpInv_pGet _ _ _ hs1Inv))
    (fun _ hSend => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret hes (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun vct hVct => potInv_ret ?_ (by simp [fsPot, esMk, Expr.eval, Expr.v1]))
  have hvp' := hSend vct.1 vct.2 (by simpa [Expr.eval, Expr.v0] using hVct)
  exact cRecordE_fsGsInv _ _ _ _ _ _ _ _ hs1Inv hvp'

private theorem challEC_hooksFSC_potInv (L B Δcka qep : ℕ) (mo : Mode) (j : ℕ) (cfg : ConfigEC OO_fs)
    (π : Policy) {Γ'} (esE : Expr OO_fs Γ' esTyFS)
    (argE : Expr OO_fs Γ' (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))))
    (ρ : Env Γ') (m : ℕ)
    (hes : fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (esE.eval ρ)) :
    PotOKInv P_fs
      (fun r => fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar r.2)
      (fun r => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) r.2)
      ((challEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep cfg π esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (esE.eval ρ)) := by
  unfold challEC; rw [eval_bind_ret]
  refine potInv_ite
    (fun _ => potInv_ret hes (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => potInv_caseOpt
      (fun _ => potInv_ret hes (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
      (fun s1 hs1 => ?_))
  have hs1Inv : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar s1 :=
    fsGsInv_of_st_eq (cEpMgmtE_some_st_fs _ _ _ _ _ _ hs1) hes
  refine potInv_ite
    (fun _ => potInv_ret hes
      (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
    (fun _ => potInv_ite
      (fun _ => potInv_ret hes
        (by simp only [fsPot, esSetAbort, esMk, esG, esH, Expr.eval, Expr.v0, Expr.v1,
          Env.get_cons_succ, Env.get_cons_zero]; omega))
      (fun _ => ?_))
  rw [eval_bind]
  refine PotOKInv.bindPot
    (vSendC_hooksFSC_potInv L B Δcka mo j _ _ _ _ _ _ _ _ m (fsVpInv_pGet _ _ _ hs1Inv))
    (fun _ hSend => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret hes (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun vct hVct => potInv_ret ?_ (by simp [fsPot, esMk, Expr.eval, Expr.v1]))
  have hvp' := hSend vct.1 vct.2 (by simpa [Expr.eval, Expr.v0] using hVct)
  exact cRecordE_fsGsInv _ _ _ _ _ _ _ _ hs1Inv hvp'

private theorem deliverEC_hooksFSC_potInv (L B Δcka maxSkip : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO_fs) {Γ'} (esE : Expr OO_fs Γ' esTyFS)
    (argE : Expr OO_fs Γ' (.prod .bool hdrCtTyFS)) (ρ : Env Γ') (m : ℕ)
    (hes : fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (esE.eval ρ)) :
    PotOKInv P_fs
      (fun r => fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar r.2)
      (fun r => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) r.2)
      ((deliverEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) L maxSkip cfg esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (esE.eval ρ)) := by
  unfold deliverEC; rw [eval_bind_ret]
  have hg0 : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (esE.eval ρ).1 := hes
  refine potInv_ite
    (fun _ => potInv_ret hes (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => potInv_caseOpt
      (fun _ => potInv_ret hes (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
      (fun r1 _ => ?_))
  rw [eval_bind]
  have hRecv := vRecvC_hooksFSC_potInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (esH (.fst (Expr.v1 (O := OO_fs)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
    (fsVpInv_pGet _ _ _ hg0)
  simp only [esH, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hRecv
  refine PotOKInv.bindPot hRecv (fun recvOut hRecvInv => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret hes (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun resInner hIn => potInv_caseOpt
      (fun _ => potInv_ret
        (by
          simp only [fsEsInv, esMk, esG, Expr.eval, Expr.v1, Expr.v2, Expr.v3,
            Env.get_cons_zero, Env.get_cons_succ]
          exact fsGsInv_ite (cGsSetWin_fsGsInv _ _ _ (by simpa [esG, Expr.eval, Expr.v3] using hg0)) hg0)
        (by simp [fsPot, esMk, Expr.eval, Expr.v1]))
      (fun stTim hSt => ?_))
  have hvp' := hRecvInv stTim.1 stTim.2.1 stTim.2.2.1 stTim.2.2.2 (by
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hIn hSt
    rw [hIn, hSt])
  rw [eval_bind]
  have hCom := commitEC_hooksFSC_potInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (esSetH (.fst (Expr.v4 (O := OO_fs))) (.snd .v2))
    (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (cRecPos .v3)
    (.cons stTim (.cons resInner (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
    (by simpa [fsEsInv, esSetH, letE_eval, esMk, esG, Expr.eval, Expr.v0, Expr.v2, Expr.v4] using hg0)
    (by simpa [esG, Expr.eval, Expr.v4] using hg0)
    (by simpa [Expr.eval, Expr.v0] using hvp')
  simp only [fsPot, esSetH, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v2, Expr.v4,
    Env.get_cons_zero, Env.get_cons_succ] at hCom
  refine PotOKInv.bindPot hCom (fun cOut hComInv => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret hComInv.1 (by simp [fsPot, Expr.eval, Expr.v0]))
    (fun g' hg' => potInv_ret ?_
      (by simp [fsPot, esSetG, letE_eval, esMk, esH, esAbort, Expr.eval, Expr.v0, Expr.v1]))
  have hgInv := hComInv.2 g' (by simpa [Expr.eval, Expr.v0] using hg')
  simp only [fsEsInv, esSetG, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ]
  exact fsGsInv_ite (cGsSetWin_fsGsInv _ _ _ hgInv) hgInv

private theorem injectEC_hooksFSC_potInv (L B Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO_fs) {Γ'} (esE : Expr OO_fs Γ' esTyFS)
    (argE : Expr OO_fs Γ' (.prod .bool hdrCtTyFS)) (ρ : Env Γ') (m : ℕ)
    (hes : fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (esE.eval ρ)) :
    PotOKInv P_fs
      (fun r => fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar r.2)
      (fun r => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) r.2)
      ((injectEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep cfg esE argE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (esE.eval ρ)) := by
  unfold injectEC; rw [eval_bind_ret]
  have hg0 : fsGsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (esE.eval ρ).1 := hes
  refine potInv_ite
    (fun _ => potInv_ret hes (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hRecv := vRecvC_hooksFSC_potInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (esH (.fst (Expr.v0 (O := OO_fs)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
    (.cons (esE.eval ρ, argE.eval ρ) ρ) m
    (fsVpInv_pGet _ _ _ hg0)
  simp only [esH, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  refine PotOKInv.bindPot hRecv (fun recvOut hRecvInv => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret hes (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun resInner hIn => potInv_caseOpt
      (fun _ => potInv_ret
        (by simpa [fsEsInv, esSetH, letE_eval, esMk, esG, Expr.eval, Expr.v0, Expr.v1, Expr.v2] using hg0)
        (by simp [fsPot, esSetH, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1, Expr.v2]))
      (fun stTim hSt => ?_))
  have hvp' := hRecvInv stTim.1 stTim.2.1 stTim.2.2.1 stTim.2.2.2 (by
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hIn hSt
    rw [hIn, hSt])
  refine potInv_ite
    (fun _ => potInv_ret
      (by simpa [fsEsInv, esSetH, letE_eval, esMk, esG, Expr.eval, Expr.v0, Expr.v2, Expr.v3] using hg0)
      (by simp [fsPot, esSetH, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v2, Expr.v3]))
    (fun _ => potInv_ite (fun _ => ?_) (fun _ => ?_))
  · rw [eval_bind]
    have hCom := commitEC_hooksFSC_potInv (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka mo j (esSetH (.fst (Expr.v3 (O := OO_fs))) (.snd .v2))
      (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)))
      (.fst .v0) (.pair (otherE (.fst (.snd .v3)))
        (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
      (.cons stTim (.cons resInner (.cons recvOut (.cons (esE.eval ρ, argE.eval ρ) ρ)))) m
      (by simpa [fsEsInv, esSetH, letE_eval, esMk, esG, Expr.eval, Expr.v0, Expr.v2, Expr.v3] using hg0)
      (by simpa [esG, Expr.eval, Expr.v3] using hg0)
      (by simpa [Expr.eval, Expr.v0] using hvp')
    simp only [fsPot, esSetH, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v2, Expr.v3,
      Env.get_cons_zero, Env.get_cons_succ] at hCom
    refine PotOKInv.bindPot hCom (fun cOut hComInv => ?_)
    refine potInv_caseOpt
      (fun _ => potInv_ret hComInv.1 (by simp [fsPot, Expr.eval, Expr.v0]))
      (fun g' hg' => potInv_ret ?_
        (by simp [fsPot, esSetG, letE_eval, esMk, esH, esAbort, Expr.eval, Expr.v0, Expr.v1]))
    have hgInv := hComInv.2 g' (by simpa [Expr.eval, Expr.v0] using hg')
    simpa [fsEsInv, esSetG, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1] using hgInv
  · refine potInv_ret ?_
      (by simp [fsPot, esSetG, esSetH, letE_eval, esMk, esG, esH, esAbort, Expr.eval, Expr.v0, Expr.v2, Expr.v3])
    simp only [fsEsInv, esSetG, esSetH, letE_eval, esMk, esG, Expr.eval, Expr.v0, Expr.v2, Expr.v3,
      Env.get_cons_zero, Env.get_cons_succ]
    exact fsGsInv_ite (cGsSetWin_fsGsInv _ _ _ (by simpa [esG, Expr.eval, Expr.v3] using hg0)) hg0

private theorem corrEC_hooksFSC_potInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ) (π : Policy)
    {Γ'} (esE : Expr OO_fs Γ' esTyFS) (pE : Expr OO_fs Γ' .bool) (ρ : Env Γ') (m : ℕ)
    (hes : fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (esE.eval ρ)) :
    PotOKInv P_fs
      (fun r => fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar r.2)
      (fun r => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) r.2)
      ((corrEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j) L π esE pE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (esE.eval ρ)) := by
  unfold corrEC; rw [eval_bind_ret]
  refine potInv_ite
    (fun _ => potInv_ret hes (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => potInv_ite
      (fun _ => potInv_ret
        (by simpa [fsEsInv, esSetAbort, letE_eval, esMk, esG, Expr.eval, Expr.v0] using hes)
        (by simp only [fsPot, esSetAbort, esMk, esG, esH, Expr.eval, Expr.v0,
          Env.get_cons_zero]; omega))
      (fun _ => ?_))
  dsimp only [hooksFSC]; rw [eval_bind]
  refine PotOKInv.bindPot
    (fsRevealC_potInv L mo _ _ _ _ _ m (fsVpInv_pGet _ _ _ hes))
    (fun _ _ => ?_)
  refine potInv_caseOpt
    (fun _ => potInv_ret hes (by simp [fsPot, esMk, Expr.eval, Expr.v0]))
    (fun _ _ => potInv_ret
      (cAfterCorrE_fsGsInv L _ _ _ hes)
      (by simp [fsPot, esMk, Expr.eval, Expr.v1]))

private theorem implEC_hooksFSC_potInv (L B Δcka qep maxSkip : ℕ) (mo : Mode) (j : ℕ)
    (cfg : ConfigEC OO_fs) (π : Policy) {Γ'}
    (esE : Expr OO_fs Γ' esTyFS)
    (qE : Expr OO_fs Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ)
    (hes : fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar (esE.eval ρ)) :
    PotOKInv P_fs
      (fun r => fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) mo.tStar r.2)
      (fun r => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) r.2)
      ((implEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (esE.eval ρ)) := by
  unfold implEC; rw [eval_bind_ret]
  refine potInv_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · refine potInv_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potInv_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potInv_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · rw [eval_bind]
          refine PotOKInv.bindPot (transmitEC_hooksFSC_potInv L B Δcka qep mo j π _ _ _ m hes)
            (fun _ h' => potInv_ret h' (by simp [Expr.eval, Expr.v0]))
        · rw [eval_bind]
          refine PotOKInv.bindPot (challEC_hooksFSC_potInv L B Δcka qep mo j cfg π _ _ _ m hes)
            (fun _ h' => potInv_ret h' (by simp [Expr.eval, Expr.v0]))
      · rw [eval_bind]
        refine PotOKInv.bindPot (deliverEC_hooksFSC_potInv L B Δcka maxSkip mo j cfg _ _ _ m hes)
          (fun _ h' => potInv_ret h' (by simp [Expr.eval, Expr.v0]))
    · rw [eval_bind]
      refine PotOKInv.bindPot (injectEC_hooksFSC_potInv L B Δcka qep mo j cfg _ _ _ m hes)
        (fun _ h' => potInv_ret h' (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    refine PotOKInv.bindPot (corrEC_hooksFSC_potInv L B Δcka mo j π _ _ _ m hes)
      (fun _ h' => potInv_ret h' (by simp [Expr.eval, Expr.v0]))

private theorem implUniEC_hooksFSC_potInv (L B Δcka qep maxSkip t : ℕ) {Γ'}
    (esE : Expr OO_fs Γ' esTyFS)
    (qE : Expr OO_fs Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ)
    (hes : fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) t (esE.eval ρ)) :
    PotOKInv P_fs
      (fun r => fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) t r.2)
      (fun r => m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) r.2)
      ((implUniEC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip t esE qE).eval ρ)
      (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (esE.eval ρ)) :=
  implEC_hooksFSC_potInv L B Δcka qep maxSkip ⟨false, none, t⟩ 0
    (modeCfgEC OO_fs ⟨false, none, t⟩) (redFsPolUni Δcka t) esE qE ρ m hes

private theorem costedReduction_makesAtMostQueries_fs_inv
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S_fs G}
    (tStar : ℕ)
    (R : CostedReduction OO_fs II_fs G C .unit .unit .bool .bool)
    (hσ : R.σ = esTyFS)
    (hTotalQ : ∀ q, R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q)
    (hFinishQ : R.finish.queries (fun _ => 1) (fun _ => 0) = 0)
    (hInit : ∀ (q : ℕ),
      PotOKInv P_fs
        (fun x : Unit × R.σ.denote =>
          fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (hσ ▸ x.2))
        (fun x : Unit × R.σ.denote =>
          q + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
            (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (hσ ▸ x.2))
        (R.init.eval (.cons () .nil)) (q + 1))
    (hStep : ∀ (m : ℕ) q (s : R.σ.denote),
      fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (hσ ▸ s) →
      PotOKInv P_fs
        (fun x : C.R.denote × R.σ.denote =>
          fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (hσ ▸ x.2))
        (fun x : C.R.denote × R.σ.denote =>
          m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
            (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (hσ ▸ x.2))
        (R.handle.eval (.cons s (.cons q .nil)))
        (1 + m + fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
          (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (hσ ▸ s)))
    (A : OracleComp (unifSpec + G) Bool) (q : ℕ)
    (hA : A.IsQueryBoundP (isGameQuery (G := G)) q) :
    CryptoGames.FSAEAD.MakesAtMostQueries (R.eval (fun _ => A) ()) (min (2 * q) (q + 2)) := by
  have h2q : (R.eval (fun _ => A) ()).IsQueryBoundP P_fs (2 * q) :=
    (CostedReduction.queryBound_eval R P_fs (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) fsIface_fwdU_zero (fun _ => A) q (fun _ => hA) ()).mono
      (hTotalQ q)
  have hq2 : (R.eval (fun _ => A) ()).IsQueryBoundP P_fs (q + 2) := by
    unfold CostedReduction.eval CostedReduction.impl
    dsimp only
    refine ((hInit q).run _ (fun ⟨_, s₀⟩ hs₀ => ?_)).mono (by omega)
    refine (potOKInv_simulateQ_handlerImpl_step1
      (fun s : R.σ.denote =>
        fsEsInv (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) tStar (hσ ▸ s))
      (fun s : R.σ.denote =>
        fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
          (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (hσ ▸ s))
      fsIface_fwdU_zero R.handle hStep hA hs₀).run _ (fun bs _ => ?_)
    have hf := Comp.queryBound_eval P_fs (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) fsIface_fwdU_zero R.finish (.cons bs.2 (.cons bs.1 .nil))
    rwa [hFinishQ] at hf
  refine (isQueryBoundP_min_fs h2q hq2).of_imp (fun x hx => ?_)
  rcases x with _ | _ <;> simp_all [isGameQuery]


private theorem redFSPrivUniProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ)
    (t q : ℕ)
    (A : Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSPrivUniProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) q :=
    hA.of_imp (fun x hx => by rcases x with _ | _ <;> simp_all [isGameQuery])
  refine costedReduction_makesAtMostQueries_fs_inv t _ rfl
    (fun q' => by
      simp [CostedReduction.totalQueries, redFSPrivUniProg, implUniEC,
        implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
        vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSC, Comp.queries]
      omega)
    (by simp [redFSPrivUniProg, Comp.queries])
    (fun q' => ?_) (fun m qv s hs => ?_) A q hA'
  · dsimp only [redFSPrivUniProg]; rw [eval_bind]
    refine PotOKInv.bindPot
      (initFSEStateC_potInv L ⟨false, none, t⟩ 0 (.bool false) (Env.cons (t := .unit) () .nil) q')
      (fun es hes => ?_)
    exact ⟨fun _ hk => by rw [eval_ret, pure_bind]; exact hk ((), es) hes⟩
  · exact implUniEC_hooksFSC_potInv L B Δcka qep maxSkip t .v0 .v1 (.cons s (.cons qv .nil)) m hs

private theorem redFSPrivUniCoinProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ)
    (t q : ℕ)
    (A : Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSPrivUniCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) q :=
    hA.of_imp (fun x hx => by rcases x with _ | _ <;> simp_all [isGameQuery])
  refine costedReduction_makesAtMostQueries_fs_inv t _ rfl
    (fun q' => by
      simp [CostedReduction.totalQueries, redFSPrivUniCoinProg, implUniEC,
        implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
        vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSC, Comp.queries]
      omega)
    (by simp [redFSPrivUniCoinProg, Comp.queries])
    (fun q' => ?_) (fun m qv s hs => ?_) A q hA'
  · dsimp only [redFSPrivUniCoinProg]; rw [eval_bind]
    refine PotOKInv.bindPot
      (initFSEStateC_potInv L ⟨false, none, t⟩ 0 (.bool false) (Env.cons (t := .unit) () .nil) q')
      (fun es hes => ?_)
    exact ⟨fun _ hk => by rw [eval_ret, pure_bind]; exact hk ((), es) hes⟩
  · exact implUniEC_hooksFSC_potInv L B Δcka qep maxSkip t .v0 .v1 (.cons s (.cons qv .nil)) m hs


end FSPotOK

section EngineInstance

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem fig8RedsInst_redCKAAuth_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) (qep + 1))
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAAuth tL)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileCkaAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redCKAAuthBucketProg_parts_le q qep tL htL)
    (redCKAAuthBucketProg_size_le q qep tL htL hqep)
    (redCKAAuthBucketProg_totalQueries_le _ _ _ _ _ _ _)

theorem fig8RedsInst_redCKAPriv_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPriv tL i)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileCkaAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redCKAPrivProg_parts_le q qep i tL (by omega) htL)
    (redCKAPrivProg_size_le q qep i tL (by omega) htL hqep)
    (by rw [CryptoGames.SM.Construction.redCKAPrivProg_totalQueries]; omega)

theorem fig8RedsInst_redCKAPrivU_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPrivU tL i)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileCkaAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redCKAPrivUProg_parts_le q qep i tL (by omega) htL)
    (redCKAPrivUProg_size_le q qep i tL (by omega) htL hqep)
    (redCKAPrivUProg_totalQueries_le _ _ _ _ _ _ _ _)

theorem fig8RedsInst_redPRNGPriv_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1) (tL : Option ℕ)
    (htL : tL ∈ CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) i)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGPriv tL i)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compilePrngAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redPRNGPrivProg_parts_le q qep i tL (by omega) htL)
    (redPRNGPrivProg_size_le q qep i tL (by omega) htL hqep)
    (by rw [CryptoGames.SM.Construction.redPRNGPrivProg_totalQueries]; omega)

theorem fig8RedsInst_redFSPriv_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv i)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileFsAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redFSPrivUniProg_parts_le q qep i (by omega))
    (redFSPrivUniProg_size_le q qep i (by omega) hqep)
    (redFSPrivUniProg_totalQueries_le _ _ _ _ _ _ _)

theorem fig8RedsInst_redFSPrivCoin_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ) (hi : i < qep + 1)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded ((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin i)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  dsimp only [Bundles.fig8RedsInst]
  exact compileFsAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep _
    (redFSPrivUniCoinProg_parts_le q qep i (by omega))
    (redFSPrivUniCoinProg_size_le q qep i (by omega) hqep)
    (redFSPrivUniCoinProg_totalQueries_le _ _ _ _ _ _ _)

local instance : Inhabited Pt := ⟨0⟩

private theorem fig8RedsInst_redCKAAuth_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.CKA.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAAuth tL).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileCkaAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedCKAPotOK.redCKAAuthBucketProg_makesAtMostQueries
      (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL q A hA)

private theorem fig8RedsInst_redCKAPriv_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.CKA.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPriv tL i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileCkaAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedCKAPotOK.redCKAPrivProg_makesAtMostQueries
      (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL i q A hA)

private theorem fig8RedsInst_redCKAPrivU_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.CKA.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPrivU tL i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileCkaAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.ReductionDsl.SM.RedCKAPotOK.redCKAPrivUProg_makesAtMostQueries
      (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL i q A hA)

private theorem fig8RedsInst_redPRNGPriv_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.PRFPRNG.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGPriv tL i).eval
        (fun _ => A) ())
      (min (2 + 2 * q) (min (q + 3) (2 * qep + 2))) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compilePrngAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (PrngPrivQepPotOK.redPRNGPrivProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps tL i q A hA)

private theorem fig8RedsInst_redFSPriv_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileFsAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (FSPotOK.redFSPrivUniProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps i q A hA)

private theorem fig8RedsInst_redFSPrivCoin_makesAtMostQueries (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Bundles.fig8RedsInst]
  refine compileFsAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam _ _ _ A ?_
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (FSPotOK.redFSPrivUniCoinProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1)) 1 qep
      CryptoGames.LibsignalSession.maxForwardJumps i q A hA)

theorem fig8RedsInst_redCKAAuth_queries_stage2 (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.CKA.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAAuth tL).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) :=
  fig8RedsInst_redCKAAuth_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL A hA

theorem fig8RedsInst_redCKAPriv_queries_stage2 (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.CKA.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPriv tL i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) :=
  fig8RedsInst_redCKAPriv_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL i A hA

theorem fig8RedsInst_redCKAPrivU_queries_stage2 (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.CKA.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPrivU tL i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) :=
  fig8RedsInst_redCKAPrivU_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL i A hA

theorem fig8RedsInst_redPRNGPriv_queries_stage2 (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.PRFPRNG.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGPriv tL i).eval
        (fun _ => A) ())
      (min (2 + 2 * q) (min (q + 3) (2 * qep + 2))) :=
  fig8RedsInst_redPRNGPriv_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q tL i A hA

theorem fig8RedsInst_redFSPriv_queries_stage2 (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) :=
  fig8RedsInst_redFSPriv_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q i A hA

theorem fig8RedsInst_redFSPrivCoin_queries_stage2 (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) (qep q : ℕ)
    (i : ℕ)
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      (((Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin i).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) :=
  fig8RedsInst_redFSPrivCoin_makesAtMostQueries Dh encPt C codec ℓ encT idOf lam qep q i A hA

end EngineInstance

end Computational.Proofs.SessionCostedFig8.ProgBounds

-- AUTO-BRIDGE BEGIN
export Computational.Proofs.SessionCostedFig8.ProgBoundsDefs (
  const_le_fig8AtomicStepBound
  linear_le_fig8AtomicStepBound
  compiled_totalCost_le_ratchetCostBudget
  compiled_le_ratchetCostBudget
  dummy_le_ratchetCostBudget
  ckaOpMacro_cost_le
)
-- AUTO-BRIDGE END

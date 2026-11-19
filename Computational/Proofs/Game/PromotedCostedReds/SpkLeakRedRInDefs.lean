/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SessionCostExactDefs -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.DrSessionSim
public import Computational.Proofs.E2E.SpkLeakRedModel -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.E2E.ComposedPrefixHelpers
public import Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSimRecv -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.SpqrSimChain
public import Computational.Proofs.E2E.Dsl.StartAndExtSmAux -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SM.GameCosted

/-!
# Promoted `CostedReduction` Witnesses for `spkLeakRed` and `spkLeakRedU`

Constructs the uniform-scalar wrapper `spkLeakRedU` over `atomicPureOps` and the leaked-signed-pre-key
PRF reduction `spkLeakRed` over `atomicSessionOps` and `e2eSessionCodec`, proving `GRedBounded` and
exact `.eval` agreement with `CryptoVerification.E2E.spkLeakRedU` and `spkLeakRed`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInDefs

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp CostedReduction
  UniformSamplerTag AtomicBaseUnif bits bits_mono reductionSizeBudget handlerImpl
  bind_congr_of_mem_support' atomicSig atomicPureOps atomicSessionOps atomicSamplers atomicPrfIface
  extractPtPrfBaseIface extractPtPrfIface extractPtPrfCodec e2eSessionCodec
  BV256 BV512 PtT PK GhostStT PlainT B ghostPartsT smQT smRT)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec PRFAdversary)
open CryptoGames.Ratchet (expandPRG padOrTruncatePlain keyToBytesVec32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (Pos Record RecvResult GameState transmitR challR corrR oracleImplR
  MakesAtMostQueries partyEnc posTy posEnc orE boolEq isSomeE otherE pGet
  pair_eval some_eval ite_eval orE_eval boolEq_eval isSomeE_eval otherE_eval pGet_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey KeyPair SessionState GhostState
  currentVersion maxReceiverChains maxMessageKeys rootCreateChain)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (topStateTight_init)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr paramsV1 sessionSchemeFixedSpk
  configRefuseEarlyBobCorr SpkLeakRed liftSpkGameM initAOracle receiveB0 receiveSpk
  deliverSpk injectSpk spkOracleImpl spkTier1Budget)
open CryptoVerification.E2E.Costed (e2eSig e2eOps E2EPureOp E2ECryptoOp recvResultEnc
  gRedBounded_of_bounds)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCurveOp e2eCryptoOp eval_e2ePureOp
  cost_e2ePureOp eval_e2eCryptoOp cost_e2eCryptoOp
  size_e2ePureOp size_e2eCurveOp size_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (spqrV1InitOp_eval_lossless)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv partyReachInv_fixedSpk_initB
  partyReachInv_fixedSpk_receive)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp_filter GameReachInv SmListBounded
  SmReachBounded smReachBounded_transmitR smReachBounded_challR smReachBounded_corrR)
open Computational.Proofs.E2E.Dsl.StartAndExtSmAux (initFixedSpkBobE eval_initFixedSpkBobE
  cost_initFixedSpkBobE)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (keyVec_bytesToKey32_vec)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvOutT drReceiveC)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (ratchetKeyAdmissibleE
  eval_ratchetKeyAdmissibleE cost_ratchetKeyAdmissibleE partyToBool_eq_partyEnc smRenc
  recvResultRejE recvResultAccE smRRecvE smRCorrE eval_recvResultRejE cost_recvResultRejE
  eval_recvResultAccE cost_recvResultAccE eval_smRRecvE cost_smRRecvE
  e2eRecTy e2eRecEncWith e2eRecPos e2eGsTy e2eGsEnc e2eGsSt e2eGsB e2eGsWin
  e2eGsSetWin eval_e2eGsSetWin cost_e2eGsSetWin_le
  e2eSafeInjE eval_e2eSafeInjE cost_e2eSafeInjE_le
  e2eChallContainsE eval_e2eChallContainsE cost_e2eChallContainsE_le
  e2eAcceptE eval_e2eAcceptE cost_e2eAcceptE_le
  e2eTrivialE eval_e2eTrivialE cost_e2eTrivialE_le
  e2eCorrAllowedE e2eAfterCorrAllowedE e2eInWindowE e2eCorrOKE
  e2eInTransitE eval_e2eInTransitE cost_e2eInTransitE_le)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drTrArmC drChArmC drCrArmC
  drTrArmC_queries_zero drChArmC_queries_zero drCrArmC_queries
  drTrArmC_cost drChArmC_cost drCrArmC_cost
  drTrArmC_eval drChArmC_eval drCrArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicPureOps_sizeHonest
  atomicBaseSamplers_sizeHonest atomicSessionOps_sizeHonest atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  sessPureOp sessSymOp sessGroupOp sessPtDecOp sessCurveOp
  eval_sessPureOp cost_sessPureOp eval_sessSymOp cost_sessSymOp eval_sessGroupOp cost_sessGroupOp
  eval_sessPtDecOp cost_sessPtDecOp eval_sessCurveOp cost_sessCurveOp
  atomicDraw256 atomicDraw256_eval atomicDraw256_cost
  liftTy liftVal liftEnv liftExpr liftExpr_cost liftExpr_eval
  wk1Expr wk1Expr_cost wk1Expr_eval wk1Comp wk1Comp_queries wk1Comp_cost wk1Comp_eval
  emptyE2EIface liftCompEmpty coinE2EIface coinE2ESamplers liftCompCoins liftCompCoins_queries_zero
  liftCompCoins_cost liftCompCoins_eval
  drRecvAtomicOutT drReceiveAtomicC drReceiveAtomicC_queries drReceiveAtomicC_cost
  drReceiveAtomicC_eval_params)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (letE_eval comp_eval_ret
  comp_eval_bind comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt comp_eval_caseSum
  eval_eq_simulateQ_of_enc
  isQueryBoundP_of_makesAtMostQueries liftVal_smQenc e2eSessionCodec_rdec_liftVal_smRenc
  liftExpr_size_le liftCompEmpty_size_le liftCompCoins_size_le
  idKeyPairLitE eval_idKeyPairLitE cost_idKeyPairLitE size_idKeyPairLitE
  wk1Expr_size wk1Comp_size
  bits_succ_le session_cost_le_ratchetCostBudget
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  dummyBoolSessionRed_size_le)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (size_le_budget_of_log_cost)
open Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg (size_drReceiveC_le
  size_recvResultRejE size_recvResultAccE size_smRRecvE size_smRCorrE
  size_e2eGsSetWin_le size_e2eSafeInjE_le size_e2eChallContainsE_le
  size_e2eAcceptE_le size_e2eTrivialE_le
  size_e2eCorrAllowedE_le size_e2eAfterCorrAllowedE_le size_e2eInWindowE_le size_e2eCorrOKE_le
  size_e2eInTransitE_le size_drTrArmC_le size_drChArmC_le)

/-! ## Coin-lifting and pair-sampling helpers -/

open Computational.Proofs.Game.PromotedCostedReds.SessionCostExactDefs (BoxEq box_le exprAllOps compAllOps exprAllOps_renExpr exprAllOps_wk1Expr compAllOps_renComp compAllOps_wk1Comp sessionCostExactCryptoOp sessionCostExactOp NoKemKeyGenExpr NoKemKeyGenComp liftExpr_cost_exact liftCompEmpty_cost_exact liftCompCoins_cost_exact noKemKeyGenExpr_renExpr noKemKeyGenExpr_wk1Expr noKemKeyGenComp_renComp noKemKeyGenComp_wk1Comp noKemKeyGenComp_ret noKemKeyGenComp_bind noKemKeyGenComp_ite noKemKeyGenComp_caseOpt noKemKeyGenComp_caseSum noKemKeyGenComp_sample noKemKeyGenComp_query noKemKeyGenComp_iter noKemKeyGenComp_findM noKemKeyGenComp_anyM noKemKeyGenComp_mapM noKemKeyGenComp_consumeFirstM noKemKeyGenComp_foldM noKemKeyGenExpr_optBytes32LitE noKemKeyGenExpr_var noKemKeyGenExpr_v0 noKemKeyGenExpr_v1 noKemKeyGenExpr_v2 noKemKeyGenExpr_v3 noKemKeyGenExpr_v4 noKemKeyGenExpr_v5 noKemKeyGenExpr_v6 noKemKeyGenExpr_unit noKemKeyGenExpr_bool noKemKeyGenExpr_nat noKemKeyGenExpr_none noKemKeyGenExpr_nil noKemKeyGenExpr_add noKemKeyGenExpr_sub noKemKeyGenExpr_mulK noKemKeyGenExpr_divK noKemKeyGenExpr_modK noKemKeyGenExpr_lt noKemKeyGenExpr_eqN noKemKeyGenExpr_not noKemKeyGenExpr_and noKemKeyGenExpr_ite noKemKeyGenExpr_pair noKemKeyGenExpr_fst noKemKeyGenExpr_snd noKemKeyGenExpr_inl noKemKeyGenExpr_inr noKemKeyGenExpr_some noKemKeyGenExpr_caseOpt noKemKeyGenExpr_caseSum noKemKeyGenExpr_letE noKemKeyGenExpr_cons noKemKeyGenExpr_len noKemKeyGenExpr_take noKemKeyGenExpr_appendL noKemKeyGenExpr_findB noKemKeyGenExpr_anyB noKemKeyGenExpr_mapB noKemKeyGenExpr_foldrB noKemKeyGenExpr_tconst noKemKeyGenExpr_tget noKemKeyGenExpr_tset noKemKeyGenExpr_e2ePureOp noKemKeyGenExpr_e2eCurveOp noKemKeyGenExpr_e2eCryptoOp noKemKeyGenExpr_orE noKemKeyGenExpr_boolEq noKemKeyGenExpr_isSomeE noKemKeyGenExpr_otherE noKemKeyGenExpr_pGet noKemKeyGenExpr_sendAddrsE noKemKeyGenExpr_expectedAddrsE noKemKeyGenComp_spqrSendComp noKemKeyGenComp_spqrRecvComp noKemKeyGenExpr_drSendPostE noKemKeyGenComp_drSendC noKemKeyGenExpr_drRecvFinishE noKemKeyGenComp_drReceiveC noKemKeyGenComp_drTrArmC noKemKeyGenComp_drChArmC noKemKeyGenComp_drCrArmC drSendAtomicC_cost_exact drReceiveAtomicC_cost_exact)

private theorem liftM_unif_query_bind {κ : Type} {G : OracleSpec κ} {α : Type}
    (t : unifSpec.Domain) (mx : unifSpec.Range t → ProbComp α) :
    (liftM (liftM (unifSpec.query t) >>= mx) : OracleComp (unifSpec + G) α) =
      (liftM ((unifSpec + G).query (.inl t)) >>=
        fun u => (liftM (mx u) : OracleComp (unifSpec + G) α)) := by
  rw [← liftComp_eq_liftM, liftComp_bind, liftComp_liftM_query,
    liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query]
  rfl

@[simp] theorem atomicPrfIface_liftP {ℓ : ℕ} {Pt : Type}
    (inpT tagT : Ty (atomicSig ℓ Pt)) (qCost : ℕ) (smp : Samplers (atomicSig ℓ Pt))
    {α : Type} (p : ProbComp α) :
    (atomicPrfIface inpT tagT qCost smp).liftP p =
      (liftM p : OracleComp (unifSpec + prfSpec inpT.denote tagT.denote) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [Iface.liftP]
  | query_bind t mx ih =>
    rw [Iface.liftP, simulateQ_query_bind, liftM_unif_query_bind]
    exact bind_congr ih

private theorem liftM_pure_prf {Pt : Type} {α : Type} (a : α) :
    (liftM (pure a : ProbComp α) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) = pure a := by
  simp [← liftComp_eq_liftM]

private theorem liftM_bind_prf {Pt : Type} {α β : Type} (p : ProbComp α) (k : α → ProbComp β) :
    (liftM (p >>= k) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β) =
      ((liftM p : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) >>=
        fun a => (liftM (k a) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β)) := by
  simp [← liftComp_eq_liftM, liftComp_bind]

private theorem liftM_sample_prod_bind_bv256 {Pt : Type} {γ : Type}
    (f : BitVec 256 × BitVec 256 → OracleComp (unifSpec + prfSpec Pt (BitVec 256)) γ) :
    ((liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256)) >>= f) =
      ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun a =>
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun b => f (a, b)) := by
  rw [SampleableType.uniformSample_prod_eq_bind (BitVec 256) (BitVec 256)]
  simp [← liftComp_eq_liftM, liftComp_bind, bind_assoc]

/-! ## Uniform-scalar wrapper `spkLeakRedU` -/

/-- Uniform-scalar wrapper `spkLeakRedU` over `atomicPureOps` and `extractPtPrfBaseIface`. -/
@[expose, reducible] def spkLeakRedU (Pt : Type) (ℓ : ℕ := 0) :
    CostedReduction
      (atomicPureOps ℓ Pt)
      (extractPtPrfBaseIface ℓ Pt)
      (prfSpec Pt (BitVec 256))
      (extractPtPrfCodec ℓ Pt)
      .unit BV256 .bool .bool where
  σ := .unit
  init := .bind
    (Comp.sample (I := extractPtPrfBaseIface ℓ Pt)
      (UniformSamplerTag.base AtomicBaseUnif.bv256) .unit)
    (.ret (.pair .v0 .unit))
  handle := .bind
    (Comp.query (I := extractPtPrfBaseIface ℓ Pt) () .v1)
    (.ret (.pair .v0 .unit))
  finish := .ret .v1

theorem spkLeakRedU_totalQueries (Pt : Type) (ℓ n : ℕ) :
    (spkLeakRedU Pt ℓ).totalQueries (fun _ => 1) (fun _ => 0) n = n := by
  simp [CostedReduction.totalQueries, Comp.queries]

theorem spkLeakRedU_totalCost (Pt : Type) (ℓ n : ℕ) :
    (spkLeakRedU Pt ℓ).totalCost n = 9 + n * 11 := by
  simp [spkLeakRedU, CostedReduction.totalCost, extractPtPrfBaseIface, atomicPrfIface,
    extractPtPrfCodec, ReductionDsl.atomicPrfCodec, ReductionDsl.atomicBaseSamplers,
    ReductionDsl.unifSamplers, AtomicBaseUnif.cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem spkLeakRedU_totalCost_le (Pt : Type) (ℓ q qep : ℕ) :
    (spkLeakRedU Pt ℓ).totalCost (q + 1) ≤ ratchetCostBudget q qep := by
  rw [spkLeakRedU_totalCost]
  have h20 : 9 + (q + 1) * 11 = 20 + q * 11 := by omega
  rw [h20]
  simpa using session_cost_le_ratchetCostBudget q qep 20 0 11 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)

theorem spkLeakRedU_totalCost_q_le (Pt : Type) (ℓ q qep : ℕ) :
    (spkLeakRedU Pt ℓ).totalCost q ≤ ratchetCostBudget q qep := by
  rw [spkLeakRedU_totalCost]
  simpa using session_cost_le_ratchetCostBudget q qep 9 0 11 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)

theorem spkLeakRedU_size_le (Pt : Type) (ℓ : ℕ) :
    (spkLeakRedU Pt ℓ).size ≤ reductionSizeBudget := by
  simp [spkLeakRedU, CostedReduction.size, Comp.size, Expr.size, Expr.v0, Expr.v1,
    reductionSizeBudget]

/-- Unconditional `GRedBounded` for `spkLeakRedU` at `q + 1` PRF queries. -/
theorem spkLeakRedU_gRedBounded (Pt : Type) (ℓ q qep : ℕ) :
    GRedBounded (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
      (q + 1) (q + 1) (ratchetCostBudget q qep) := by
  refine gRedBounded_of_bounds (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
    (q + 1) (q + 1) (ratchetCostBudget q qep)
    (spkLeakRedU_totalCost_le Pt ℓ q qep)
    ((spkLeakRedU_size_le Pt ℓ).trans (Nat.le_add_right _ _)) ?_
    (atomicPureOps_sizeHonest ℓ Pt) (atomicBaseSamplers_sizeHonest ℓ Pt)
  rw [spkLeakRedU_totalQueries]

theorem spkLeakRedU_gRedBounded_q (Pt : Type) (ℓ q qep : ℕ) :
    GRedBounded (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
      q q (ratchetCostBudget q qep) := by
  refine gRedBounded_of_bounds (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
    q q (ratchetCostBudget q qep)
    (spkLeakRedU_totalCost_q_le Pt ℓ q qep)
    ((spkLeakRedU_size_le Pt ℓ).trans (Nat.le_add_right _ _)) ?_
    (atomicPureOps_sizeHonest ℓ Pt) (atomicBaseSamplers_sizeHonest ℓ Pt)
  rw [spkLeakRedU_totalQueries]

private theorem spkLeakRedU_impl_run (Pt : Type) (ℓ : ℕ)
    (t : (unifSpec + prfSpec Pt (BitVec 256)).Domain) (s : Unit) :
    ((spkLeakRedU Pt ℓ).impl t).run s =
      (fun u => (u, s)) <$> liftM ((unifSpec + prfSpec Pt (BitVec 256)).query t) := by
  rcases t with n | q
  · simp [CostedReduction.impl, handlerImpl, spkLeakRedU, extractPtPrfBaseIface, atomicPrfIface,
      StateT.run_lift, map_eq_bind_pure_comp, OracleSpec.query]
  · simp [CostedReduction.impl, handlerImpl, spkLeakRedU, extractPtPrfCodec,
      ReductionDsl.atomicPrfCodec, extractPtPrfBaseIface, atomicPrfIface,
      Comp.eval, Expr.eval, Expr.v0, Expr.v1, map_eq_bind_pure_comp, OracleSpec.query]

private theorem simulateQ_run_StateT_of_step {κ : Type} {spec : OracleSpec κ} {m : Type → Type}
    [Monad m] [LawfulMonad m] {σ α : Type}
    {impl : QueryImpl spec (StateT σ m)} {qi : QueryImpl spec m}
    (hstep : ∀ t s, (impl t).run s = (fun x => (x, s)) <$> qi t)
    (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl oa).run s = (fun x => (x, s)) <$> simulateQ qi oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind]
    change ((impl t).run s >>= fun p => (simulateQ impl (mx p.1)).run p.2) =
      (fun x => (x, s)) <$> (qi t >>= fun u => simulateQ qi (mx u))
    rw [hstep, bind_map_left, map_bind]
    exact bind_congr fun u => ih u s

@[simp] private theorem simulateQ_query_id {κ : Type} {spec : OracleSpec κ} {α : Type}
    (oa : OracleComp spec α) :
    simulateQ (fun t => (liftM (spec.query t) : OracleComp spec (spec.Range t))) oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
    rw [simulateQ_query_bind]
    exact bind_congr ih

theorem spkLeakRedU_eval_family (Pt : Type) (ℓ : ℕ)
    (D : BitVec 256 → PRFAdversary Pt (BitVec 256)) :
    (spkLeakRedU Pt ℓ).eval D () = (do
      let x ← (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256))
      D x) := by
  dsimp only [CostedReduction.eval, extractPtPrfBaseIface,
    ReductionDsl.atomicBaseSamplers, ReductionDsl.unifSamplers,
    AtomicBaseUnif.sort, ReductionDsl.AtomicSort.den, Ty.denote]
  have hinit :
      (spkLeakRedU Pt ℓ).init.eval (.cons () .nil) =
        (fun x => (x, ())) <$>
          (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) := by
    dsimp only [spkLeakRedU, extractPtPrfBaseIface, ReductionDsl.atomicBaseSamplers,
      ReductionDsl.unifSamplers, AtomicBaseUnif.sort, ReductionDsl.AtomicSort.den,
      Comp.eval, Expr.eval, Expr.v0, Env.get]
    rw [atomicPrfIface_liftP]
    simp [map_eq_bind_pure_comp]
  change (do
    let p : BitVec 256 × Unit ← (spkLeakRedU Pt ℓ).init.eval (.cons () .nil)
    let q : Bool × Unit ← (simulateQ (spkLeakRedU Pt ℓ).impl (D p.1)).run p.2
    (spkLeakRedU Pt ℓ).finish.eval (.cons q.2 (.cons q.1 .nil))) = _
  rw [hinit, bind_map_left]
  refine bind_congr fun x => ?_
  rw [simulateQ_run_StateT_of_step (spkLeakRedU_impl_run Pt ℓ), simulateQ_query_id]
  simp [spkLeakRedU, Comp.eval, Expr.eval, Expr.v1]

/-- Exact `.eval` agreement of `spkLeakRedU` with `CryptoVerification.E2E.spkLeakRedU`. -/
theorem spkLeakRedU_eval (Pt : Type) (ℓ : ℕ) {PQC : Type}
    (D : SpkLeakRed Pt ℓ PQC) (P : CryptoGames.LibsignalSession.Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) PQC Bytes) :
    (spkLeakRedU Pt ℓ).eval (fun x => D P Dh encPt encT decT qep x A) () =
      CryptoVerification.E2E.spkLeakRedU D P Dh encPt encT decT qep A :=
  spkLeakRedU_eval_family Pt ℓ (fun x => D P Dh encPt encT decT qep x A)

/-! ## Initialization and pre/post-check expressions -/

section E2EHelpers

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

/-- Input tuple `(b, (s, ((rk1, ck1), (ck0, (alice, pqr)))))` for `spkInitGsE2EE`. -/
@[expose, reducible] def spkInitArgT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod .bool
    (.prod CryptoVerification.E2E.Costed.BV256
      (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))

@[expose] def spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))) :
    Expr EOps Γ CryptoVerification.E2E.Costed.GhostStT :=
  .letE (.pair idsE keysE)
    (let p0 : Expr EOps _ _ := .v0
     let idALit := Expr.fst (.fst p0)
     let idBLit := Expr.snd (.fst p0)
     let sE := Expr.fst (.snd p0)
     let rk1E := Expr.fst (.fst (.snd (.snd p0)))
     let ck1E := Expr.snd (.fst (.snd (.snd p0)))
     let ck0E := Expr.fst (.snd (.snd (.snd p0)))
     let aliceE := Expr.fst (.snd (.snd (.snd (.snd p0))))
     let pqrE := Expr.snd (.snd (.snd (.snd (.snd p0))))
     let spkPk := Expr.fst (e2eCryptoOp .sessionKeyPairGen sE)
     let kpA := e2eCryptoOp .sessionKeyPairGen aliceE
     let pqA := e2eCryptoOp .spqrV1InitOp (.pair (.bool true) pqrE)
     e2ePureOp .ghostStateJoin
       (.pair (.bool false)
         (.pair (e2ePureOp (.u32Lit (BitVec.ofNat 32 currentVersion.toNat)) .unit)
           (.pair idALit
             (.pair (.some idBLit)
               (.pair rk1E
                 (.pair (e2ePureOp (.u32Lit 0#32) .unit)
                   (.pair (.bool true)
                     (.pair (.nat 0)
                       (.pair (.cons (.nat 0) .nil)
                         (.pair (.some (.pair kpA (.pair ck1E (e2ePureOp (.u32Lit 0#32) .unit))))
                           (.pair
                             (.cons
                               (.pair spkPk
                                 (.pair (.some (.pair ck0E (e2ePureOp (.u32Lit 0#32) .unit))) .nil))
                               .nil)
                             pqA))))))))))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)))))
    (ρ : Env Γ) :
    let (idA, idB) := idsE.eval ρ
    let (s, ((rk1, ck1), (ck0, (alice, pqr)))) := keysE.eval ρ
    (spkInitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).eval ρ =
      let spk := (KeyPair.generate C s).publicKey
      let sendingRatchetKey := KeyPair.generate C alice
      let sess := ((SessionState.new currentVersion idA idB rk1
        (spqrV1Init C.F K .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
        sendingRatchetKey ⟨ck1, 0⟩
      (⟨.A, sess.setUnacknowledgedPreKeyMessage, 0, [0]⟩ : GhostState Bytes) := by
  rcases hids : idsE.eval ρ with ⟨idA, idB⟩
  rcases hkeys : keysE.eval ρ with ⟨s, ⟨⟨rk1, ck1⟩, ⟨ck0, ⟨alice, pqr⟩⟩⟩⟩
  simp only [spkInitAliceE2EE, Expr.eval, Expr.v0, Env.get, hids, hkeys,
    eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval]
  have hspqr : E2ECryptoOp.eval ℓ zeroPqxdhPrims C K .spqrV1InitOp (true, pqr) =
      spqrV1Init C.F K .a2b pqr :=
    spqrV1InitOp_eval_lossless ℓ zeroPqxdhPrims C K true pqr
  rw [hspqr]
  dsimp only [E2ECryptoOp.eval, CryptoVerification.E2E.Costed.ghostJoinEval,
    CryptoVerification.E2E.Costed.boolToParty, Option.map, List.take, List.map,
    SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
    SessionState.setUnacknowledgedPreKeyMessage]
  have h5 : ¬ (maxReceiverChains < 1) := by decide
  simp [h5]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))) :
    (spkInitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).cost ≤
      idsE.cost + keysE.cost + 31500 := by
  simp only [spkInitAliceE2EE, Expr.cost, Expr.v0, cost_e2eCryptoOp, E2ECryptoOp.cost,
    cost_e2ePureOp, E2EPureOp.cost, bits, show Nat.log 2 0 = 0 from rfl]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))) :
    (spkInitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).size ≤
      idsE.size + keysE.size + 150 := by
  simp only [spkInitAliceE2EE, Expr.size, Expr.v0, size_e2eCryptoOp, size_e2ePureOp,
    E2EPureOp.opSize, show bits 0 = 1 from rfl]
  omega

@[expose] def spkInitGsE2EE (idA idB : IdentityKey) :
    Expr EOps [spkInitArgT ℓ] (e2eGsTy ℓ) :=
  let bE : Expr EOps [spkInitArgT ℓ] .bool := .fst .v0
  let keysE :
      Expr EOps [spkInitArgT ℓ]
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
            (.prod CryptoVerification.E2E.Costed.BV256
              (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)))) :=
    .snd .v0
  let sE : Expr EOps [spkInitArgT ℓ] CryptoVerification.E2E.Costed.BV256 := .fst keysE
  let ck0E : Expr EOps [spkInitArgT ℓ] CryptoVerification.E2E.Costed.BV256 :=
    .fst (.snd (.snd keysE))
  let pqrE : Expr EOps [spkInitArgT ℓ] CryptoVerification.E2E.Costed.BV256 :=
    .snd (.snd (.snd (.snd keysE)))
  let idsE := idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  let bobKeysE :
      Expr EOps [spkInitArgT ℓ]
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
            CryptoVerification.E2E.Costed.BV256)) :=
    .pair sE (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) ck0E) pqrE)
  .pair
    (.pair (spkInitAliceE2EE idsE keysE) (initFixedSpkBobE idsE bobKeysE))
    (.pair bE
      (.pair (.bool false)
        (.pair (.pair (.nat 0) (.nat 0))
          (.pair (.pair (.nat 0) (.nat 0))
            (.pair .none
              (.pair .nil
                (.pair .nil
                  (.pair .nil
                    (.pair (.pair (.tconst (.nat 0)) (.tconst (.nat 0)))
                      (.pair .nil .nil))))))))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_spkInitGsE2EE (idA idB : IdentityKey)
    (b : Bool) (s rk1 ck1 ck0 alice pqr : BitVec 256) :
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).eval
      (.cons (b, (s, ((rk1, ck1), (ck0, (alice, pqr))))) .nil) =
      let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
      let spk := (KeyPair.generate C s).publicKey
      let sendingRatchetKey := KeyPair.generate C alice
      let sess := ((SessionState.new currentVersion idA idB rk1
        (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
        sendingRatchetKey ⟨ck1, 0⟩
      let stA : GhostState Bytes := ⟨.A, sess.setUnacknowledgedPreKeyMessage, 0, [0]⟩
      let stB : GhostState Bytes := P.initB ⟨0, ck0, s, alice, pqr⟩
      e2eGsEnc ({ st := fun Q => match Q with | .A => stA | .B => stB, b := b } :
        GameState (GhostState Bytes) (Plain ℓ) Bytes) := by
  let ρ : Env [spkInitArgT ℓ] := .cons (b, (s, ((rk1, ck1), (ck0, (alice, pqr))))) .nil
  have ha := eval_spkInitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB) (.snd .v0) ρ
  have hb := eval_initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (idKeyPairLitE idA idB)
    (.pair (.fst (.snd .v0))
      (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.snd .v0))))))) ρ alice
  simp only [ρ, Expr.eval, Expr.v0, Env.get, eval_idKeyPairLitE, eval_e2ePureOp,
    E2EPureOp.eval] at ha hb
  dsimp only [spkInitGsE2EE]
  simp only [Expr.eval, Expr.v0, Env.get, ha, hb]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_spkInitGsE2EE (idA idB : IdentityKey) :
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).cost ≤
      63800 := by
  have hids := cost_idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [spkInitArgT ℓ]) idA idB
  have ha := cost_spkInitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [spkInitArgT ℓ]) (idKeyPairLitE idA idB) (.snd .v0)
  have hb := cost_initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [spkInitArgT ℓ]) (idKeyPairLitE idA idB)
    (.pair (.fst (.snd .v0))
      (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.snd .v0)))))))
  simp only [spkInitGsE2EE, Expr.cost, Expr.v0, cost_e2ePureOp, E2EPureOp.cost, bits,
    show Nat.log 2 0 = 0 from rfl] at ha hb ⊢
  omega

open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v eLet) in
omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem size_initFixedSpkBobE_le {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          CryptoVerification.E2E.Costed.BV256))) :
    (initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) idsE keysE).size ≤
      idsE.size + keysE.size + 130 := by
  unfold initFixedSpkBobE
  dsimp only [v, Ext.wk]
  simp only [eLet, size_e2eCryptoOp, size_e2ePureOp, E2EPureOp.opSize, Expr.size,
    show bits 0 = 1 from rfl]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_spkInitGsE2EE (idA idB : IdentityKey) :
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).size ≤
      550 := by
  have ha := size_spkInitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [spkInitArgT ℓ]) (idKeyPairLitE idA idB) (.snd .v0)
  have hb := size_initFixedSpkBobE_le (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [spkInitArgT ℓ]) (idKeyPairLitE idA idB)
    (.pair (.fst (.snd .v0))
      (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.snd .v0)))))))
  simp only [spkInitGsE2EE, Expr.size, Expr.v0, size_idKeyPairLitE, size_e2ePureOp,
    E2EPureOp.opSize, show bits 0 = 1 from rfl] at ha hb ⊢
  omega

@[expose] def dlPreE2EE (q : ℕ) :
    Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]
      (.sum
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ))
        (.prod CryptoVerification.E2E.Costed.GhostStT posTy)) :=
  .ite (e2eGsWin (.fst .v0))
    (.inl (.pair (smRRecvE .none) (.fst .v0)))
    (.caseOpt (e2eInTransitE q (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)))
      (.inl (.pair (smRRecvE .none) (.fst .v0)))
      (.inr (.pair (pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1))) (e2eRecPos .v0))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_dlPreE2EE (q : ℕ) :
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).cost ≤
      300 + 215 * q := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := cost_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  simp only [dlPreE2EE, otherE, pGet, e2eGsSt, e2eGsWin, e2eRecPos, cost_smRRecvE,
    Expr.cost, Expr.v0, Expr.v1] at htr ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_dlPreE2EE (q : ℕ) :
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).size ≤
      150 + bits q := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := size_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  simp only [dlPreE2EE, otherE, pGet, e2eGsSt, e2eGsWin, e2eRecPos, size_smRRecvE,
    Expr.size, Expr.v0, Expr.v1] at htr ⊢
  omega

@[expose] def dlPostE2EE (q : ℕ) :
    Expr EOps
      [.prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
        (.prod posTy (drRecvOutT ℓ))]
      (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
        (e2eGsTy ℓ)) :=
  .caseOpt (.snd (.snd .v0))
    (.pair (smRRecvE (.some recvResultRejE)) (.fst (.fst .v0)))
    (let st' : Expr EOps _ CryptoVerification.E2E.Costed.GhostStT := .fst .v0
     let t' : Expr EOps _ .nat := .fst (.snd .v0)
     let i' : Expr EOps _ .nat := .fst (.snd (.snd .v0))
     let m' : Expr EOps _ CryptoVerification.E2E.Costed.PlainT := .snd (.snd (.snd .v0))
     let rPos : Expr EOps _ posTy := .fst (.snd .v1)
     let gs1 : Expr EOps _ (e2eGsTy ℓ) := .fst (.fst .v1)
     let p1 : Expr EOps _ .bool := .fst (.snd (.fst .v1))
     let mOut : Expr EOps _ (.opt CryptoVerification.E2E.Costed.PlainT) :=
       .ite (e2eChallContainsE q gs1 rPos) .none (.some m')
     .pair (smRRecvE (.some (recvResultAccE t' i' mOut)))
       (e2eAcceptE q gs1 p1 st' rPos))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_dlPostE2EE (q : ℕ) :
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).cost ≤
      900 + 250 * q := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
      (.prod posTy (drRecvOutT ℓ))
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have hch := cost_e2eChallContainsE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.fst (.snd .v1))
  have hacc := cost_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0) (.fst (.snd .v1))
  simp only [dlPostE2EE, cost_smRRecvE, cost_recvResultRejE, cost_recvResultAccE,
    Expr.cost, Expr.v0, Expr.v1] at hch hacc ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_dlPostE2EE (q : ℕ) :
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).size ≤
      1050 + 4 * bits q := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
      (.prod posTy (drRecvOutT ℓ))
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have hch := size_e2eChallContainsE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.fst (.snd .v1))
  have hacc := size_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0) (.fst (.snd .v1))
  simp only [dlPostE2EE, size_smRRecvE, size_recvResultRejE, size_recvResultAccE,
    Expr.size, Expr.v0, Expr.v1] at hch hacc ⊢
  omega

@[expose] def ijPreE2EE (q Δ : ℕ) :
    Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]
      (.sum
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ))
        CryptoVerification.E2E.Costed.GhostStT) :=
  let gs0 : Expr EOps _ (e2eGsTy ℓ) := .fst .v0
  let p0 : Expr EOps _ .bool := .fst (.snd .v0)
  let c0 : Expr EOps _ (CryptoVerification.E2E.Costed.B 32) := .snd (.snd .v0)
  let refuseCond : Expr EOps _ .bool :=
    orE (e2eGsWin gs0)
      (orE (isSomeE (e2eInTransitE q gs0 (otherE p0) c0))
        (orE (.not (e2eSafeInjE Δ gs0)) (.not (ratchetKeyAdmissibleE c0))))
  .ite refuseCond
    (.inl (.pair (smRRecvE .none) gs0))
    (.inr (pGet (e2eGsSt gs0) p0))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_ijPreE2EE (q Δ : ℕ) :
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ).cost ≤
      400 + (ℓ / 32 + 1) + 215 * q + bits Δ := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := cost_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsinj := cost_e2eSafeInjE_le (ℓ := ℓ) (O' := EOps) Δ
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ))
  simp only [ijPreE2EE, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin,
    cost_ratchetKeyAdmissibleE, cost_smRRecvE, Expr.cost, Expr.v0] at htr hsinj ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_ijPreE2EE (q Δ : ℕ) :
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ).size ≤
      200 + bits q + bits Δ := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := size_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsinj := size_e2eSafeInjE_le (ℓ := ℓ) (O' := EOps) Δ
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ))
  simp only [ijPreE2EE, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin,
    ratchetKeyAdmissibleE, size_e2eCurveOp, size_smRRecvE, Expr.size, Expr.v0] at htr hsinj ⊢
  omega

@[expose] def ijPostE2EE (q Δ qep : ℕ) :
    Expr EOps
      [.prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
        (drRecvOutT ℓ)]
      (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
        (e2eGsTy ℓ)) :=
  .caseOpt (.snd .v0)
    (.pair (smRRecvE (.some recvResultRejE)) (.fst (.fst .v0)))
    (let st' : Expr EOps _ CryptoVerification.E2E.Costed.GhostStT := .fst .v0
     let t' : Expr EOps _ .nat := .fst (.snd .v0)
     let i' : Expr EOps _ .nat := .fst (.snd (.snd .v0))
     let m' : Expr EOps _ CryptoVerification.E2E.Costed.PlainT := .snd (.snd (.snd .v0))
     let gs1 : Expr EOps _ (e2eGsTy ℓ) := .fst (.fst .v1)
     let p1 : Expr EOps _ .bool := .fst (.snd (.fst .v1))
     .ite (.lt (.nat (qep + 1)) t')
       (.pair (smRRecvE (.some recvResultRejE)) gs1)
       (let posE : Expr EOps _ posTy := .pair (otherE p1) (.pair t' i')
        .ite (e2eTrivialE q Δ gs1 posE)
          (.pair (smRRecvE (.some (recvResultAccE t' i' (.some m'))))
            (e2eAcceptE q gs1 p1 st' posE))
          (.pair (smRRecvE (.some recvResultRejE))
            (e2eGsSetWin gs1 (.bool true)))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_ijPostE2EE (q Δ qep : ℕ) :
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).cost ≤
      1000 + 300 * q + bits Δ + bits (qep + 1) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))) (drRecvOutT ℓ)
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have htriv := cost_e2eTrivialE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hacc := cost_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0)
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hwin := cost_e2eGsSetWin_le (ℓ := ℓ) (O' := EOps)
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.bool true)
  simp only [ijPostE2EE, otherE, cost_smRRecvE, cost_recvResultRejE, cost_recvResultAccE,
    Expr.cost, Expr.v0, Expr.v1] at htriv hacc hwin ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_ijPostE2EE (q Δ qep : ℕ) :
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).size ≤
      1400 + 5 * bits q + bits Δ + bits (qep + 1) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))) (drRecvOutT ℓ)
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have htriv := size_e2eTrivialE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hacc := size_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0)
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hwin := size_e2eGsSetWin_le (ℓ := ℓ) (O' := EOps)
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.bool true)
  simp only [ijPostE2EE, otherE, size_smRRecvE, size_recvResultRejE, size_recvResultAccE,
    Expr.size, Expr.v0, Expr.v1] at htriv hacc hwin ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem not_partyEnc (p : Party) : (!partyEnc p) = partyEnc p.other := by
  cases p <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_dlPreE2EE (q : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (htr : st.trans.length ≤ q) :
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
      (.cons (e2eGsEnc st, (partyEnc party, c)) .nil) =
      if st.win then
        .inl ((none, (none, none)), e2eGsEnc st)
      else
        match st.inTransit party.other c with
        | none => .inl ((none, (none, none)), e2eGsEnc st)
        | some rec_ => .inr (st.st party, posEnc rec_.pos) := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  let ρ₁ : Env [t0] := .cons (e2eGsEnc st, (partyEnc party, c)) .nil
  dsimp only [dlPreE2EE]
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := EOps)))).eval ρ₁ = st.win := rfl
  rw [ite_eval, hWin]
  by_cases hwin : st.win
  · simp [hwin, Expr.eval, Expr.v0, eval_smRRecvE]
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    have hOther : (otherE (.fst (.snd (Expr.v0 (O := EOps))))).eval ρ₁ = partyEnc party.other := by
      rw [otherE_eval]; exact not_partyEnc party
    have hInTr := eval_e2eInTransitE (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q
      (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) ρ₁ st party.other htr rfl hOther
    have hc1 : (Expr.snd (.snd (Expr.v0 (O := EOps)))).eval ρ₁ = c := rfl
    rw [hc1] at hInTr
    dsimp only [Expr.eval]
    rw [hInTr]
    cases st.inTransit party.other c with
    | none => rfl
    | some rec_ =>
      let ρ₂ : Env [e2eRecTy ℓ, t0] := .cons (e2eRecEncWith st.comp rec_) ρ₁
      have hpGet := pGet_eval (e2eGsSt (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1))
        ρ₂ st.st party rfl rfl
      change Sum.inr ((pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1))).eval ρ₂,
          (e2eRecPos .v0).eval ρ₂) = _
      rw [hpGet]
      rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_dlPostE2EE (q : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (rpos : Pos) (out : Option (GhostState Bytes × (ℕ × (ℕ × Plain ℓ))))
    (h : SmListBounded q st) :
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
      (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rpos, out)) .nil) =
      match out with
      | none =>
        ((none, (some (recvResultEnc .rejected), none)), e2eGsEnc st)
      | some (st', (t', (i', m'))) =>
        let mOut := if st.chall.contains rpos then none else some m'
        ((none, (some (recvResultEnc (.accepted t' i' mOut)), none)),
          e2eGsEnc (st.accept party st' rpos)) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
      (.prod posTy (drRecvOutT ℓ))
  let ρ₁ : Env [tIn] := .cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rpos, out)) .nil
  dsimp only [dlPostE2EE]
  rcases out with _ | ⟨st', t', i', m'⟩
  · rfl
  · let tQuad : Ty ESig :=
      .prod CryptoVerification.E2E.Costed.GhostStT
        (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
    let ρ₂ : Env [tQuad, tIn] := .cons (st', (t', (i', m'))) ρ₁
    have hChall := eval_e2eChallContainsE (O' := EOps) q (.fst (.fst .v1)) (.fst (.snd .v1))
      ρ₂ st rpos h.chall_le rfl rfl
    have hAcc := eval_e2eAcceptE (O' := EOps) q (.fst (.fst .v1)) (.fst (.snd (.fst .v1)))
      (.fst .v0) (.fst (.snd .v1)) ρ₂ st party rpos h rfl rfl rfl
    change ((smRRecvE (.some (recvResultAccE (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
          (.ite (e2eChallContainsE q (.fst (.fst .v1)) (.fst (.snd .v1)))
            .none (.some (.snd (.snd (.snd .v0)))))))).eval ρ₂,
        (e2eAcceptE q (.fst (.fst .v1)) (.fst (.snd (.fst .v1)))
          (.fst .v0) (.fst (.snd .v1))).eval ρ₂) = _
    simp only [eval_smRRecvE, some_eval, eval_recvResultAccE, ite_eval, hChall, hAcc]
    cases st.chall.contains rpos <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_ijPreE2EE (q Δ : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (htr : st.trans.length ≤ q) :
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ).eval
      (.cons (e2eGsEnc st, (partyEnc party, c)) .nil) =
      if st.win || (st.inTransit party.other c).isSome || !(st.safeInj Δ) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c) then
        .inl ((none, (none, none)), e2eGsEnc st)
      else
        .inr (st.st party) := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  let ρ₁ : Env [t0] := .cons (e2eGsEnc st, (partyEnc party, c)) .nil
  dsimp only [ijPreE2EE]
  have hOther : (otherE (.fst (.snd (Expr.v0 (O := EOps))))).eval ρ₁ = partyEnc party.other := by
    rw [otherE_eval]; exact not_partyEnc party
  have hInTr := eval_e2eInTransitE (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) ρ₁ st party.other htr rfl hOther
  have hc1 : (Expr.snd (.snd (Expr.v0 (O := EOps)))).eval ρ₁ = c := rfl
  rw [hc1] at hInTr
  have hSafeInj : (e2eSafeInjE Δ (.fst (Expr.v0 (O := EOps)))).eval ρ₁ = st.safeInj Δ :=
    eval_e2eSafeInjE Δ (.fst .v0) ρ₁ st rfl
  have hAdm :
      (ratchetKeyAdmissibleE (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
        (.snd (.snd .v0))).eval ρ₁ =
      ratchetKeyAdmissible protoSignalCodec decT encT c := by
    rw [eval_ratchetKeyAdmissibleE, hc1]
  have hRefuse :
      (orE (e2eGsWin (.fst (Expr.v0 (O := EOps))))
        (orE (isSomeE (e2eInTransitE q (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))))
          (orE (.not (e2eSafeInjE Δ (.fst .v0)))
            (.not (ratchetKeyAdmissibleE (.snd (.snd .v0))))))).eval ρ₁ =
      (st.win || (st.inTransit party.other c).isSome || !(st.safeInj Δ) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := by
    simp only [orE_eval, isSomeE_eval, Expr.eval, hInTr, hSafeInj, hAdm, Option.isSome_map]
    simp [ρ₁, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [ite_eval, hRefuse]
  by_cases href :
      st.win || (st.inTransit party.other c).isSome || !(st.safeInj Δ) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp [href, Expr.eval, Expr.v0, eval_smRRecvE]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    have hpGet := pGet_eval (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.fst (.snd .v0))
      ρ₁ st.st party rfl rfl
    exact congrArg Sum.inr hpGet

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_ijPostE2EE (q Δ qep : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (out : Option (GhostState Bytes × (ℕ × (ℕ × Plain ℓ))))
    (h : SmListBounded q st) :
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).eval
      (.cons ((e2eGsEnc st, (partyEnc party, c)), out) .nil) =
      match out with
      | none =>
        ((none, (some (recvResultEnc .rejected), none)), e2eGsEnc st)
      | some (st', (t', (i', m'))) =>
        if qep + 1 < t' then
          ((none, (some (recvResultEnc .rejected), none)), e2eGsEnc st)
        else
          let pos : Pos := ⟨party.other, t', i'⟩
          if st.trivial Δ pos then
            ((none, (some (recvResultEnc (.accepted t' i' (some m'))), none)),
              e2eGsEnc (st.accept party st' pos))
          else
            ((none, (some (recvResultEnc .rejected), none)),
              e2eGsEnc { st with win := true }) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))) (drRecvOutT ℓ)
  let ρ₁ : Env [tIn] := .cons ((e2eGsEnc st, (partyEnc party, c)), out) .nil
  dsimp only [ijPostE2EE]
  rcases out with _ | ⟨st', t', i', m'⟩
  · rfl
  · let tQuad : Ty ESig :=
      .prod CryptoVerification.E2E.Costed.GhostStT
        (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
    let ρ₂ : Env [tQuad, tIn] := .cons (st', (t', (i', m'))) ρ₁
    have hlt : (Expr.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := EOps))))).eval ρ₂ =
        decide (qep + 1 < t') := rfl
    change (if (Expr.lt (.nat (qep + 1)) (.fst (.snd .v0))).eval ρ₂ then _ else _) = _
    rw [hlt]
    by_cases hqep : qep + 1 < t'
    · simp [hqep, Expr.eval, Expr.v1, eval_smRRecvE, eval_recvResultRejE]
    · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hpos2 :
          (Expr.pair (otherE (.fst (.snd (.fst (Expr.v1 (O := EOps))))))
            (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval ρ₂ =
          posEnc ⟨party.other, t', i'⟩ := by
        have ho2 : (otherE (.fst (.snd (.fst (Expr.v1 (O := EOps)))))).eval ρ₂ =
            partyEnc party.other := by
          rw [otherE_eval]; exact not_partyEnc party
        simp only [Expr.eval, ho2]
        rfl
      have hTriv := eval_e2eTrivialE (O' := EOps) q Δ (.fst (.fst .v1))
        (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
        ρ₂ st ⟨party.other, t', i'⟩ h rfl hpos2
      change (if (e2eTrivialE q Δ (.fst (.fst .v1))
          (.pair (otherE (.fst (.snd (.fst .v1))))
            (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₂ then _ else _) = _
      rw [hTriv]
      by_cases htriv : st.trivial Δ ⟨party.other, t', i'⟩
      · simp only [htriv, ↓reduceIte]
        have hAcc := eval_e2eAcceptE (O' := EOps) q (.fst (.fst .v1)) (.fst (.snd (.fst .v1)))
          (.fst .v0)
          (.pair (otherE (.fst (.snd (.fst .v1))))
            (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
          ρ₂ st party ⟨party.other, t', i'⟩ h rfl rfl hpos2
        change ((smRRecvE (.some (recvResultAccE (.fst (.snd .v0))
              (.fst (.snd (.snd .v0))) (.some (.snd (.snd (.snd .v0))))))).eval ρ₂,
            (e2eAcceptE q (.fst (.fst .v1)) (.fst (.snd (.fst .v1))) (.fst .v0)
              (.pair (otherE (.fst (.snd (.fst .v1))))
                (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₂) = _
        simp only [eval_smRRecvE, some_eval, eval_recvResultAccE, hAcc]
        rfl
      · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
        have hSetWin := eval_e2eGsSetWin (O' := EOps) (.fst (.fst .v1)) (.bool true) ρ₂ st rfl
        change ((smRRecvE (.some recvResultRejE)).eval ρ₂,
            (e2eGsSetWin (.fst (.fst .v1)) (.bool true)).eval ρ₂) = _
        simp only [eval_smRRecvE, some_eval, eval_recvResultRejE, hSetWin]
        rfl

end E2EHelpers

/-! ## Atomic `receiveSpk` computation -/

section SessionOpWrappers

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose] def sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessPureOp o a

@[expose] def sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessSymOp o a

@[expose] def sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessGroupOp o a

@[expose] def sPtDecOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPtDecOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicPtDecOps ℓ decT).dom o)) :
    Expr AOps Γ ((ReductionDsl.atomicPtDecOps ℓ decT).cod o) :=
  sessPtDecOp o a

@[expose] def sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) :
    Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).cod o) :=
  sessCurveOp o a

@[simp] theorem eval_sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt (a.eval ρ) := rfl

@[simp] theorem cost_sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem eval_sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C (a.eval ρ) := rfl

@[simp] theorem cost_sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem eval_sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C Dh encPt lam (a.eval ρ) := rfl

@[simp] theorem cost_sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

@[simp] theorem eval_sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (sPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).eval ρ = decT (a.eval ρ) := rfl

@[simp] theorem cost_sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) :
    (sPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).cost = a.cost + 8 := rfl

@[simp] theorem eval_sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) (ρ : Env Γ) :
    (sCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ =
      (ReductionDsl.atomicCurveCheckOps ℓ decT encT).eval o (a.eval ρ) := rfl

@[simp] theorem cost_sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) :
    (sCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost =
      a.cost + (ReductionDsl.atomicCurveCheckOps ℓ decT encT).cost o := rfl

@[simp] theorem size_sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + o.opSize + 1 := rfl

@[simp] theorem size_sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + 1 := rfl

@[simp] theorem size_sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + 1 := rfl

@[simp] theorem size_sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) :
    (sPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).size = a.size + 1 := rfl

@[simp] theorem size_sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) :
    (sCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + 1 := rfl

end SessionOpWrappers

section ReceiveSpkAtomic

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "PrfI" => extractPtPrfIface ℓ Pt

@[expose] def senderKeyPtAtomicE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    Expr AOps Γ (.opt (.prod PK PtT)) :=
  .caseOpt (sPureOp .signalMsgParse cE)
    .none
    (.letE (.fst (.snd (.fst .v0)))
      (.ite (sCurveOp .decEncCheck .v0)
        (.caseOpt (sPtDecOp .ptDecPk .v0)
          .none
          (.ite (sGroupOp .ptIsZero .v0) .none (.some (.pair .v1 .v0))))
        .none))

theorem cost_senderKeyPtAtomicE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    (senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).cost ≤ cE.cost + (ℓ / 32 + 1) + 80 := by
  simp only [senderKeyPtAtomicE, Expr.cost, Expr.v0, Expr.v1,
    cost_sPureOp, cost_sCurveOp, cost_sPtDecOp, cost_sGroupOp,
    ReductionDsl.AtomicPureOp.cost, ReductionDsl.AtomicGroupOp.cost]
  omega

theorem size_senderKeyPtAtomicE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    (senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).size ≤ cE.size + 35 := by
  simp only [senderKeyPtAtomicE, Expr.size, Expr.v0, Expr.v1,
    size_sPureOp, ReductionDsl.AtomicPureOp.opSize, size_sCurveOp, size_sPtDecOp, size_sGroupOp]
  omega

theorem eval_senderKeyPtAtomicE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) (ρ : Env Γ) :
    (senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).eval ρ =
      match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec (cE.eval ρ) with
      | .error _ => none
      | .ok msg =>
        match decT msg.senderRatchetKey with
        | none => none
        | some T =>
          if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none
          else some (msg.senderRatchetKey, T) := by
  simp only [senderKeyPtAtomicE, Expr.eval, Expr.v0, Expr.v1, Env.get,
    eval_sPureOp, eval_sCurveOp, eval_sPtDecOp, eval_sGroupOp]
  dsimp only [ReductionDsl.atomicCurveCheckOps, ReductionDsl.AtomicPureOp.eval,
    ReductionDsl.AtomicGroupOp.eval]
  cases CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec (cE.eval ρ) with
  | error _ => rfl
  | ok msg =>
    dsimp only [Env.get]
    cases hdec : decT msg.senderRatchetKey with
    | none => simp
    | some T =>
      dsimp only [Env.get]
      by_cases henc : encT T = msg.senderRatchetKey
      · by_cases h0 : T = 0 <;> simp [henc, h0]
      · simp [henc]

@[expose] def prepRecvB0StateAtomicE {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) :
    Expr AOps Γ (.opt GhostStT) :=
  .letE inpE
    (.letE (sPureOp .ghostStateSplit (.fst .v0))
      (.letE (sGroupOp .rootExpandPrg (.snd (.snd (.snd .v1))))
        (.letE (sSymOp .sessionKeyPairGen (.fst (.snd (.snd .v2))))
          (.caseOpt
            (sSymOp .sessionRootCreateChain
              (.pair (.fst .v1) (.pair (.fst (.snd .v3)) (.snd .v0))))
            .none
            (let parts : Expr AOps _ ghostPartsT := .v3
             let srk : Expr AOps _ PK := .fst (.snd .v4)
             let ck1 : Expr AOps _ BV256 := .snd .v2
             let kpRc : Expr AOps _ (.prod PK BV256) := .v1
             let rk2 : Expr AOps _ BV256 := .fst .v0
             let ck2 : Expr AOps _ BV256 := .snd .v0
             let z32 : Expr AOps _ _ := sPureOp (.u32Lit 0#32) .unit
             let isB := Expr.fst parts
             let ver := Expr.fst (.snd parts)
             let locId := Expr.fst (.snd (.snd parts))
             let remId? := Expr.fst (.snd (.snd (.snd parts)))
             let pend := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd parts))))))
             let pqTail := Expr.snd (.snd (.snd (.snd (.snd (.snd parts)))))
             let pqSt := Expr.snd (.snd (.snd (.snd (.snd pqTail))))
             .some
               (sPureOp .ghostStateJoin
                 (.pair isB
                   (.pair ver
                     (.pair locId
                       (.pair remId?
                         (.pair rk2
                           (.pair z32
                             (.pair pend
                               (.pair (.nat 1)
                                 (.pair (.cons (.nat 1) .nil)
                                   (.pair (.some (.pair kpRc (.pair ck2 z32)))
                                     (.pair
                                       (.cons (.pair srk (.pair (.some (.pair ck1 z32)) .nil)) .nil)
                                       pqSt)))))))))))))))))

theorem cost_prepRecvB0StateAtomicE {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) :
    (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).cost ≤ inpE.cost + 200 := by
  have hb1 : bits 1 = 1 := by decide
  simp only [prepRecvB0StateAtomicE, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    cost_sPureOp, cost_sGroupOp, cost_sSymOp,
    ReductionDsl.AtomicPureOp.cost, ReductionDsl.AtomicSymOp.cost, ReductionDsl.AtomicGroupOp.cost]
  omega

theorem size_prepRecvB0StateAtomicE {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) :
    (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).size ≤ inpE.size + 160 := by
  have hb1 : bits 1 = 1 := by decide
  simp only [prepRecvB0StateAtomicE, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    size_sPureOp, ReductionDsl.AtomicPureOp.opSize, size_sGroupOp, size_sSymOp]
  omega

theorem eval_prepRecvB0StateAtomicE {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) (ρ : Env Γ) :
    let (g, (srk, (rc, prk))) := inpE.eval ρ
    (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).eval ρ =
      let (rk1, ck1) := (expandPRG C.F).gen prk
      match rootCreateChain C rk1 srk (KeyPair.generate C rc).privateKey with
      | .error _ => none
      | .ok (rk2, ck2) =>
        let sess' : SessionState Bytes :=
          { g.session with
            previousCounter := 0
            rootKey := rk2
            receiverChains := [⟨srk, some ⟨ck1, 0⟩, []⟩]
            senderChain := some ⟨KeyPair.generate C rc, ck2⟩ }
        some { g with session := sess', epoch := 1, chainEpochs := [1] } := by
  rcases hinp : inpE.eval ρ with ⟨g, ⟨srk, ⟨rc, prk⟩⟩⟩
  simp only [prepRecvB0StateAtomicE, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    Env.get, hinp, eval_sPureOp, eval_sGroupOp, eval_sSymOp,
    ReductionDsl.AtomicSymOp.eval, ReductionDsl.AtomicGroupOp.eval]
  dsimp only [ReductionDsl.AtomicPureOp.eval]
  have hpriv : CryptoGames.LibsignalSession.PrivateKey.mk
      (keyToBytesVec32 (bytesToKey32 (KeyPair.generate C rc).privateKey.bytes.toList)) =
      (KeyPair.generate C rc).privateKey := by
    cases hp : (KeyPair.generate C rc).privateKey with
    | mk bs => simp [keyVec_bytesToKey32_vec]
  have hkp : KeyPair.mk (KeyPair.generate C rc).publicKey
      ⟨keyToBytesVec32 (bytesToKey32 (KeyPair.generate C rc).privateKey.bytes.toList)⟩ =
      KeyPair.generate C rc := by
    cases hgen : KeyPair.generate C rc with
    | mk pub priv =>
      cases priv with
      | mk bs => simp [keyVec_bytesToKey32_vec]
  rw [hpriv]
  cases hrc : rootCreateChain C ((expandPRG C.F).gen prk).1 srk
      (KeyPair.generate C rc).privateKey with
  | error _ => rfl
  | ok pair =>
    rcases pair with ⟨rk2, ck2⟩
    cases ck2 with
    | mk ck2Key ck2Idx =>
      have hidx : ck2Idx = 0#32 := by
        unfold rootCreateChain at hrc
        split at hrc <;> simp_all
      subst hidx
      dsimp only [Env.get, ReductionDsl.ghostSplitEval, ReductionDsl.ghostJoinEval, Option.map,
        List.take, List.map]
      have hpty : ReductionDsl.boolToParty (ReductionDsl.partyToBool g.party) = g.party := by
        cases g.party <;> rfl
      rw [hpty, hkp]
      cases g with
      | mk party session epoch chainEpochs =>
        cases session
        rfl

/-- Oracle-ised `receiveSpk` computation over `atomicSessionOps` and `extractPtPrfIface ℓ Pt`. -/
@[expose] def receiveSpkAtomicC {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    Comp AOps PrfI Γ (drRecvAtomicOutT ℓ Pt) :=
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  let Γ₀ : List (Ty ASig) := t0 :: Γ
  let g0 : Expr AOps Γ₀ GhostStT := .fst (.snd .v0)
  let c0 : Expr AOps Γ₀ (B 32) := .fst (.snd (.snd .v0))
  let rc0 : Expr AOps Γ₀ BV256 := .snd (.snd (.snd .v0))
  let parts0 : Expr AOps Γ₀ ghostPartsT := sPureOp .ghostStateSplit g0
  let isBob0 : Expr AOps Γ₀ .bool :=
    .and (.fst parts0)
      (.eqN (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd parts0)))))))) (.nat 0))
  .bind (.ret (.pair sE (.pair gE (.pair cE rcE))))
    (.ite isBob0
      (.caseOpt (senderKeyPtAtomicE c0)
        (.ret .none)
        (.bind
          (Comp.query (I := PrfI) ()
            (sGroupOp .ptDh (.pair (.fst .v1) (.snd .v0))))
          (.caseOpt
            (prepRecvB0StateAtomicE
              (.pair (.fst (.snd .v2))
                (.pair (.fst .v1)
                  (.pair (.snd (.snd (.snd .v2))) .v0))))
            (.ret .none)
            (drReceiveAtomicC PrfI
              (.pair .v0
                (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))))))
      (drReceiveAtomicC PrfI (.pair g0 (.pair c0 rc0))))

theorem receiveSpkAtomicC_queries {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [receiveSpkAtomicC, Comp.queries, drReceiveAtomicC_queries]


private theorem drReceiveAtomicC_size_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).size ≤
      inpE.size + 370000 := by
  let tInp : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod (CryptoVerification.E2E.Costed.B 32) CryptoVerification.E2E.Costed.BV256)
  let cE2E := drReceiveC (spqrDslHooks ℓ (Pt := Pt) zeroPqxdhPrims C K decT encT)
    (emptyE2EIface I') (Γ := [tInp]) .v0
  have h1 := liftCompEmpty_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I') cE2E
  have h2 := size_drReceiveC_le (Pt := Pt) (emptyE2EIface I')
    (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [tInp] tInp)
  dsimp only [cE2E] at h1
  simp only [Expr.size, Expr.v0] at h2
  simp only [drReceiveAtomicC, Comp.size, wk1Comp_size, Expr.v0] at h1 h2 ⊢
  omega

theorem receiveSpkAtomicC_size_le {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).size ≤
      sE.size + gE.size + cE.size + rcE.size + 741000 := by
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  have hsk := size_senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst (.snd (.snd .v0)) : Expr AOps (t0 :: Γ) (B 32))
  have hprep := size_prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0)) :
      Expr AOps (BV256 :: .prod PK PtT :: t0 :: Γ) (.prod GhostStT (.prod PK (.prod BV256 BV256))))
  have hdr1 := drReceiveAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))) :
      Expr AOps (GhostStT :: BV256 :: .prod PK PtT :: t0 :: Γ)
        (.prod GhostStT (.prod (B 32) BV256)))
  have hdr2 := drReceiveAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))) :
      Expr AOps (t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  have hb0 : bits 0 = 1 := by decide
  simp only [receiveSpkAtomicC, size_sPureOp, ReductionDsl.AtomicPureOp.opSize, size_sGroupOp,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hsk hprep hdr1 hdr2 ⊢
  omega


theorem receiveSpkAtomicC_cost_tier1 {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).cost ≤
      sE.cost + gE.cost + cE.cost + rcE.cost + 5105000 + 9 * (ℓ / 32 + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  have hsk := cost_senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst (.snd (.snd .v0)) : Expr AOps (t0 :: Γ) (B 32))
  have hprep := cost_prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0)) :
      Expr AOps (BV256 :: .prod PK PtT :: t0 :: Γ) (.prod GhostStT (.prod PK (.prod BV256 BV256))))
  have hdr1 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))) :
      Expr AOps (GhostStT :: BV256 :: .prod PK PtT :: t0 :: Γ)
        (.prod GhostStT (.prod (B 32) BV256)))
  have hdr2 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))) :
      Expr AOps (t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  obtain ⟨nSk, ⟨eSk⟩, hsk'⟩ := box_le hsk
  obtain ⟨nPrep, ⟨ePrep⟩, hprep'⟩ := box_le hprep
  obtain ⟨nDr1, ⟨eDr1⟩, hdr1'⟩ := box_le hdr1
  obtain ⟨nDr2, ⟨eDr2⟩, hdr2'⟩ := box_le hdr2
  clear hsk hprep hdr1 hdr2
  have hb0 : bits 0 = 1 := by decide
  dsimp only [receiveSpkAtomicC]
  simp only [Comp.cost, eSk, ePrep, eDr1, eDr2]
  simp only [cost_sPureOp, cost_sGroupOp, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    ReductionDsl.AtomicPureOp.cost, ReductionDsl.AtomicGroupOp.cost] at hsk' hprep' hdr1' hdr2' ⊢
  omega


theorem receiveSpkAtomicC_cost {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).cost ≤
      sE.cost + gE.cost + cE.cost + rcE.cost + 32 * 5104040 + 257 * (ℓ / 32 + 1) := by
  have h := receiveSpkAtomicC_cost_tier1 (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) sE gE cE rcE
  omega

end ReceiveSpkAtomic

section SpkLeakRed

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt := 0)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "PrfI" => extractPtPrfIface ℓ Pt

@[simp] theorem r_partyToBool_eq_partyEnc (p : Party) :
    ReductionDsl.partyToBool p = partyEnc p := by
  cases p <;> rfl

@[expose] def spkInitC :
    Comp AOps PrfI [BV256] (.prod .unit (.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)))) :=
  .bind (Comp.sample (I := PrfI) UniformSamplerTag.bool .unit)
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind (atomicDraw256 (I := PrfI) rfl)
        (.bind (atomicDraw256 (I := PrfI) rfl)
          (.bind
            (Comp.query (I := PrfI) ()
              (sGroupOp .ptDh
                (.pair .v4
                  (sGroupOp .ptDh (.pair .v1 (sGroupOp .ptBase .unit))))))
            (.ret
              (.pair .unit
                (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
                  (.letE
                    (.pair .v4
                      (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
                        (.pair (sGroupOp .rootExpandPrg .v0)
                          (.pair .v3 (.pair .v2 .v1)))))
                    (wk1Expr
                      (liftExpr
                        (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K)
                          (decT := decT) (encT := encT) idA idB)))))))))))

theorem spkInitC_queries :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkInitC, atomicDraw256, Comp.queries]


theorem atomicDraw256_size {O0 : Ops (atomicSig ℓ Pt)} {ι : Type}
    {T : OracleSpec ι} {I0 : Iface (atomicSig ℓ Pt) T} (h : I0.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDraw256 (O := O0) (I := I0) h (Γ := Γ)).size = 2 := by
  rcases I0 with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

theorem spkInitC_size_le :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).size ≤ 5500 := by
  have hl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs := size_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  simp only [spkInitC, size_sGroupOp, atomicDraw256_size, wk1Expr_size,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hl ⊢
  omega

theorem smReachBounded_accept {q : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K q gs)
    (party : Party) {st' : GhostState Bytes} (hst' : PartyReachInv C K st') (pos : Pos) :
    SmReachBounded C K (q + 1) (gs.accept party st' pos) := by
  have hreach' : GameReachInv C K (gs.accept party st' pos) := by
    cases party <;> exact ⟨by simp [GameState.accept, GameState.delete, Function.update,
      h.reach.alice, hst'], by simp [GameState.accept, GameState.delete, Function.update,
      h.reach.bob, hst']⟩
  refine ⟨hreach', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [GameState.accept, GameState.delete]
    exact List.length_filter_le _ _ |>.trans (h.lists.trans_le.trans (Nat.le_succ q))
  · simp only [GameState.accept, GameState.delete]
    exact List.length_filter_le _ _ |>.trans (h.lists.chall_le.trans (Nat.le_succ q))
  · simp only [GameState.accept, GameState.delete, dedupComp_filter]
    exact List.length_filter_le _ _ |>.trans (h.lists.dedupComp_le.trans (Nat.le_succ q))
  · simp only [GameState.accept, GameState.delete]
    exact List.length_filter_le _ _ |>.trans
      (h.lists.comp_le.trans (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q)))
  · exact h.lists.leaks_le.trans (Nat.le_succ q)
  · exact h.lists.corrs_le.trans (Nat.le_succ q)

@[expose] def spkDlArmC (q : ℕ) :
    Comp AOps PrfI
      [.prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))]
      (.prod (smRT GhostStT) (.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)))) :=
  .caseSum
    (.letE (.snd .v0)
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q))))
    (.ret (.pair (.fst .v0) (.pair (.fst .v1) (.snd .v0))))
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind
        (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.fst .v2) (.fst .v1) (.snd (.snd (.snd .v2))) .v0)
        (.ret
          (.letE (.pair (.snd .v3) (.pair (.snd .v2) .v0))
            (.letE
              (wk1Expr
                (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))
              (.pair (.fst .v0) (.pair (.fst .v5) (.snd .v0))))))))

theorem spkDlArmC_queries (q : ℕ) :
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkDlArmC, atomicDraw256, receiveSpkAtomicC_queries, Comp.queries]


theorem spkDlArmC_size_le (q : ℕ) :
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).size ≤
      753000 + 45 * bits q := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpre2 := size_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpost2 := size_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hrecv := receiveSpkAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst .v2 : Expr AOps [BV256, .prod GhostStT posTy, t0] BV256)
    (.fst .v1) (.snd (.snd (.snd .v2))) .v0
  simp only [spkDlArmC, atomicDraw256_size, wk1Expr_size, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpre1 hpost1 hrecv ⊢
  omega


@[expose] def spkIjArmC (q qep : ℕ) :
    Comp AOps PrfI
      [.prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))]
      (.prod (smRT GhostStT) (.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)))) :=
  .caseSum
    (.letE (.snd .v0)
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)))))
    (.ret (.pair (.fst .v0) (.pair (.fst .v1) (.snd .v0))))
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind
        (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.fst .v2) .v1 (.snd (.snd (.snd .v2))) .v0)
        (.ret
          (.letE (.pair (.snd .v3) .v0)
            (.letE
              (wk1Expr
                (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
                    q (2 + 1) qep)))
              (.pair (.fst .v0) (.pair (.fst .v5) (.snd .v0))))))))

theorem spkIjArmC_queries (q qep : ℕ) :
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkIjArmC, atomicDraw256, receiveSpkAtomicC_queries, Comp.queries]


theorem spkIjArmC_size_le (q qep : ℕ) :
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size ≤
      757000 + 54 * bits q + 9 * bits (qep + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
  have hpre2 := size_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)
  have hpost1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep)
  have hpost2 := size_ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    q (2 + 1) qep
  have hrecv := receiveSpkAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst .v2 : Expr AOps [BV256, GhostStT, t0] BV256)
    .v1 (.snd (.snd (.snd .v2))) .v0
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [spkIjArmC, atomicDraw256_size, wk1Expr_size, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpre1 hpost1 hrecv ⊢
  omega


/-- Combined 5-arm `spkOracleImpl` handler over `atomicSessionOps` and `extractPtPrfIface ℓ Pt`. -/
@[expose] def spkStepC (q qep : ℕ) :
    Comp AOps PrfI
      [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), smQT]
      (.prod (smRT GhostStT) (.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)))) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  let trBody :
      Comp EOps (coinE2EIface PrfI)
        [.prod (e2eGsTy ℓ)
          (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
            (.opt CryptoVerification.E2E.Costed.BV512)))]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drTrArmC hooks coins q (2 + 1) qep (.fst .v0) (.snd .v0)
  let chBody :
      Comp EOps (coinE2EIface PrfI)
        [.prod (e2eGsTy ℓ)
          (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
            (.prod CryptoVerification.E2E.Costed.PlainT
              (.opt CryptoVerification.E2E.Costed.BV512))))]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drChArmC hooks coins q (2 + 1) qep (.fst .v0) (.snd .v0)
  let crBody :
      Comp EOps (coinE2EIface PrfI)
        [.prod (e2eGsTy ℓ) .bool]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drCrArmC q (.fst .v0) (.snd .v0)
  .caseSum .v1
    (.bind (.ret (.pair (.snd .v1) .v0))
      (.bind (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (I' := PrfI) rfl trBody))
        (.ret (.pair (.fst .v0) (.pair (.fst .v3) (.snd .v0))))))
    (.caseSum .v0
      (.bind (.ret (.pair (.snd .v2) .v0))
        (.bind (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (I' := PrfI) rfl chBody))
          (.ret (.pair (.fst .v0) (.pair (.fst .v4) (.snd .v0))))))
      (.caseSum .v0
        (.bind (.ret (.pair (.fst .v3) (.pair (.snd .v3) .v0)))
          (wk1Comp (spkDlArmC C K Dh encPt encT decT lam q)))
        (.caseSum .v0
          (.bind (.ret (.pair (.fst .v4) (.pair (.snd .v4) .v0)))
            (wk1Comp (spkIjArmC C K Dh encPt encT decT lam q qep)))
          (.bind (.ret (.pair (.snd .v4) .v0))
            (.bind (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl crBody))
              (.ret (.pair (.fst .v0) (.pair (.fst .v6) (.snd .v0)))))))))

theorem spkStepC_queries (q qep : ℕ) :
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkStepC, wk1Comp_queries, liftCompCoins_queries_zero,
    spkDlArmC_queries, spkIjArmC_queries, Comp.queries]


private theorem size_drCrArmC_le {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    (drCrArmC (I := I) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q gsE crArg).size ≤
      gsE.size + crArg.size + 720 + 2 * bits q := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have hallow := size_e2eCorrAllowedE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hwin := size_e2eInWindowE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hcorrOK := size_e2eCorrOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hafter := size_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  simp only [drCrArmC, orE, pGet, e2eGsSt, e2eGsWin, size_smRCorrE, Comp.size, Expr.size,
    Expr.v0] at hallow hwin hcorrOK hafter ⊢
  omega

theorem spkStepC_size_le (q qep : ℕ) :
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size ≤
      1730000 + 153 * bits q + 36 * bits qep + 9 * bits (qep + 1) := by
  let tTr : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let tCh : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drTrArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
      (coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI)
      q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))
  have htr2 := size_drTrArmC_le (C := C) (K := K) (decT := decT) (encT := encT)
    PrfI q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)
  have hch1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drChArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
      (coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI)
      q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))
  have hch2 := size_drChArmC_le (C := C) (K := K) (decT := decT) (encT := encT)
    PrfI q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)
  have hcr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
  have hcr2 := size_drCrArmC_le (I := coinE2EIface PrfI) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  have hdl := spkDlArmC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  have hij := spkIjArmC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [Expr.size, Expr.v0, hb3] at htr2 hch2 hcr2
  have htr := htr1.trans (Nat.mul_le_mul_left 9 htr2)
  have hch := hch1.trans (Nat.mul_le_mul_left 9 hch2)
  have hcr := hcr1.trans (Nat.mul_le_mul_left 9 hcr2)
  clear htr1 htr2 hch1 hch2 hcr1 hcr2
  dsimp only [tTr, tCh, tCr] at htr hch hcr
  simp only [Expr.v0] at htr hch hcr
  dsimp only [spkStepC]
  simp only [wk1Comp_size, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega


@[expose] def spkInitImpl (s : BitVec 256) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      (Unit × GameState (GhostState Bytes) (Plain ℓ) Bytes) := do
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool)
  let ck0 ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256))
  let rest ← (liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256))
  let stA ← initAOracle (Pt := Pt) P Dh ck0 s rest.1 rest.2
  let stB := P.initB ⟨0, ck0, s, rest.1, rest.2⟩
  return ((), { st := fun Q => match Q with | .A => stA | .B => stB, b := b })

private theorem spkInitC_cost_tier1 :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost ≤ 65000 := by
  have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB) rfl
  have hgs := cost_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  simp only [spkInitC, cost_sGroupOp, extractPtPrfIface, atomicPrfIface, atomicSamplers,
    ReductionDsl.unifSamplers, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    ReductionDsl.AtomicGroupOp.cost, atomicDraw256_cost, wk1Expr_cost] at hl ⊢
  omega

private theorem spkDlArmC_cost_tier1 (q : ℕ) :
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).cost ≤
      5107000 + 9 * (ℓ / 32 + 1) + 500 * q := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) rfl
  have hpre2 := cost_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) rfl
  have hpost2 := cost_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hrecv := receiveSpkAtomicC_cost_tier1 (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (.fst .v2 : Expr AOps [BV256, .prod GhostStT posTy, t0] BV256)
    (.fst .v1) (.snd (.snd (.snd .v2))) .v0
  obtain ⟨nPre, ⟨ePre⟩, hpre⟩ := box_le (hpre1.trans hpre2)
  obtain ⟨nPost, ⟨ePost⟩, hpost⟩ := box_le (hpost1.trans hpost2)
  obtain ⟨nRecv, ⟨eRecv⟩, hrecv'⟩ := box_le hrecv
  clear hpre1 hpre2 hpost1 hpost2 hrecv
  dsimp only [spkDlArmC]
  simp only [Comp.cost, atomicDraw256_cost, eRecv]
  simp only [ePre, ePost, wk1Expr_cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hrecv' ⊢
  omega

private theorem spkIjArmC_cost_tier1 (q qep : ℕ) :
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      5107000 + 10 * (ℓ / 32 + 1) + 530 * q + bits (qep + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)) rfl
  have hpre2 := cost_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)
  have hpost1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep) rfl
  have hpost2 := cost_ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    q (2 + 1) qep
  have hrecv := receiveSpkAtomicC_cost_tier1 (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (.fst .v2 : Expr AOps [BV256, GhostStT, t0] BV256)
    .v1 (.snd (.snd (.snd .v2))) .v0
  have hb3 : bits (2 + 1) = 2 := by decide
  obtain ⟨nPre, ⟨ePre⟩, hpre⟩ := box_le (hpre1.trans hpre2)
  obtain ⟨nPost, ⟨ePost⟩, hpost⟩ := box_le (hpost1.trans hpost2)
  obtain ⟨nRecv, ⟨eRecv⟩, hrecv'⟩ := box_le hrecv
  clear hpre1 hpre2 hpost1 hpost2 hrecv
  dsimp only [spkIjArmC]
  simp only [Comp.cost, atomicDraw256_cost, eRecv]
  simp only [ePre, ePost, wk1Expr_cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpost hrecv' ⊢
  omega

private theorem spkStepC_cost_tier1 (q qep : ℕ) :
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      5110000 + 10 * (ℓ / 32 + 1) + 550 * q + bits qep + bits (qep + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  let tTr : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let tCh : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drTrArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))
    (by dsimp only [hooks, coins]; rw [noKemKeyGenComp_drTrArmC]; rfl)
  have htr2 := drTrArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)
  have hch1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drChArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))
    (by dsimp only [hooks, coins]; rw [noKemKeyGenComp_drChArmC]; rfl)
  have hch2 := drChArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)
  have hcr1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
    (by rw [noKemKeyGenComp_drCrArmC]; rfl)
  have hcr2 := drCrArmC_cost (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  have hdl := spkDlArmC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  have hij := spkIjArmC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [Expr.cost, Expr.v0, hb3] at htr2 hch2 hcr2
  have htr := htr1.trans htr2
  have hch := hch1.trans hch2
  have hcr := hcr1.trans hcr2
  clear htr1 htr2 hch1 hch2 hcr1 hcr2
  dsimp only [hooks, coins, tTr, tCh, tCr] at htr hch hcr
  obtain ⟨nTr, ⟨eTr⟩, htr'⟩ := box_le htr
  obtain ⟨nCh, ⟨eCh⟩, hch'⟩ := box_le hch
  obtain ⟨nCr, ⟨eCr⟩, hcr'⟩ := box_le hcr
  obtain ⟨nDl, ⟨eDl⟩, hdl'⟩ := box_le hdl
  obtain ⟨nIj, ⟨eIj⟩, hij'⟩ := box_le hij
  clear htr hch hcr hdl hij
  dsimp only [spkStepC]
  simp only [Comp.cost, wk1Comp_cost, eTr, eCh, eCr, eDl, eIj]
  simp only [Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega


theorem spkInitC_cost :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost ≤ 2100000 := by
  have h := spkInitC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
  omega

theorem spkDlArmC_cost (q : ℕ) :
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).cost ≤
      10212000 + 18 * (ℓ / 32 + 1) + 1000 * q := by
  have h := spkDlArmC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  omega

theorem spkIjArmC_cost (q qep : ℕ) :
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      10212000 + 20 * (ℓ / 32 + 1) + 1050 * q + 2 * bits (qep + 1) := by
  have h := spkIjArmC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  omega

theorem spkStepC_cost (q qep : ℕ) :
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      174636000 + 38 * (ℓ / 32 + 1) + 35600 * q + 2 * bits qep + 6 * bits (qep + 1) := by
  have h := spkStepC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  omega

@[expose] def spkLeakRedReal (ℓ q qep : ℕ) :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (extractPtPrfIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) BV256 .unit .bool .bool where
  σ := .prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ))
  init := spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
  handle := spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  finish := .ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1) (.fst (.snd (.snd (.snd .v0)))))

/-- Promoted `CostedReduction` witness for `CryptoVerification.E2E.spkLeakRed`. -/
@[expose] def spkLeakRed (ℓ q qep : ℕ) :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (extractPtPrfIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) BV256 .unit .bool .bool :=
  if ℓ < 10 ^ 6 then
    spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep
  else
    dummyBoolSessionRed (extractPtPrfIface ℓ Pt) BV256

theorem spkLeakRed_totalQueries_le (ℓ q qep : ℕ) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q + 1 := by
  unfold spkLeakRed
  split_ifs with hℓ
  · simp only [spkLeakRedReal, CostedReduction.totalQueries, spkInitC_queries,
      spkStepC_queries, Comp.queries]
    omega
  · rw [dummyBoolSessionRed_totalQueries]
    omega

theorem spkLeakRedReal_init_cost (ℓ q qep : ℕ) :
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost =
      (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost := rfl

theorem spkLeakRedReal_handle_cost (ℓ q qep : ℕ) :
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost =
      (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost := rfl

theorem spkLeakRed_totalCost_le (ℓ q qep : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold spkLeakRed
  split_ifs with hℓ
  · have hinit := spkInitC_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepC_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
      (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hhandle :
        max 1
          ((spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ 176000000 + 36000 * q + 64 * bits qep' := by
      rw [spkLeakRedReal_handle_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      generalize (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost = cStep
        at hstep ⊢
      omega
    have hmul :
        q * max 1
          ((spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ q * (176000000 + 36000 * q + 64 * bits qep') :=
      Nat.mul_le_mul_left q hhandle
    have hinit_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost ≤
          2100000 := by
      rw [spkLeakRedReal_init_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact le_trans hinit (by decide)
    have hfin_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1)
        (.fst (.snd (.snd (.snd .v0)))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), .bool] .bool)).cost ≤ 100
      dsimp only [orE, boolEq, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
      decide
    have htot :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
          2100000 + q * (176000000 + 36000 * q + 64 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface, e2eSessionCodec]
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost =
        ci at hinit_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost =
        ch at hhandle hmul ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost =
        cf at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q qep' 2100000 100 176000000 36000 64
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

private theorem q_add_eleven_le_ratchetCostBudget (q' qep' : ℕ) :
    q' + 11 ≤ ratchetCostBudget q' qep' := by
  have h := session_cost_le_ratchetCostBudget q' qep' 100 (400 * q') 0 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem spkLeakRedReal_init_size (ℓ q qep : ℕ) :
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size =
      (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).size := rfl

theorem spkLeakRedReal_handle_size (ℓ q qep : ℕ) :
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size =
      (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size := rfl

theorem spkLeakRed_size_le_of_clamp (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  unfold spkLeakRed
  split_ifs with hℓ
  · have hinit := spkInitC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
    have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
    have hinit_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size ≤
          5500 := by
      rw [spkLeakRedReal_init_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact hinit
    have hhandle_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size ≤
          1730000 + 198 * bits (ratchetCostBudget q qep') := by
      rw [spkLeakRedReal_handle_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      omega
    have hfin_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1)
        (.fst (.snd (.snd (.snd .v0)))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), .bool] .bool)).size ≤ 100
      dsimp only [orE, boolEq, Comp.size, Expr.size, Expr.v0, Expr.v1]
      decide
    have hsz :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
          1737000 + 198 * bits (ratchetCostBudget q qep') := by
      dsimp only [CostedReduction.size]
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size =
        si at hinit_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size =
        sh at hhandle_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size =
        sf at hfin_le ⊢
      omega
    exact size_le_budget_of_log_cost (by decide) (by decide) hsz
  · exact (dummyBoolSessionRed_size_le (extractPtPrfIface ℓ Pt) BV256).trans
      (Nat.le_add_right _ _)

theorem spkLeakRed_size_le (ℓ q qep : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact spkLeakRed_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep (by omega)

theorem spkLeakRed_gRedBounded_of_clamp (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep')
    (spkLeakRed_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRed_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep hqep_B)
    (spkLeakRed_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem spkLeakRed_gRedBounded_of_le (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep')
    (spkLeakRed_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRed_size_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep_q)
    (spkLeakRed_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

/-- `GRedBounded` for `spkLeakRed` at `ratchetCostBudget q qep` under `qep ≤ q + 10`. -/
theorem spkLeakRed_gRedBounded (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep) :=
  spkLeakRed_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_refl qep)

theorem spkLeakRed_gRedBounded_succ (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q (qep + 1)) :=
  spkLeakRed_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_succ qep)

/-! ### Exact static cost preservation for `spkTier1Budget` -/

private theorem session_cost_le_spkTier1Budget
    (q qep cInit cFin cStepBase cStepQ cStepQep : ℕ)
    (hInit : cInit ≤ 1000000)
    (hFin : cFin ≤ 1000000)
    (hBase : cStepBase ≤ 12800000)
    (hQ : cStepQ ≤ 1024)
    (hQep : cStepQep ≤ 256) :
    cInit + q * (cStepBase + cStepQ * q + cStepQep * bits qep) + cFin ≤
      spkTier1Budget q qep := by
  have h1 : q * cStepBase ≤ q * 12800000 := Nat.mul_le_mul_left q hBase
  have h2 : q * (cStepQ * q) ≤ q * (1024 * q) :=
    Nat.mul_le_mul_left q (Nat.mul_le_mul_right q hQ)
  have h3 : q * (cStepQep * bits qep) ≤ q * (256 * bits qep) :=
    Nat.mul_le_mul_left q (Nat.mul_le_mul_right (bits qep) hQep)
  have hlhs : q * (cStepBase + cStepQ * q + cStepQep * bits qep) =
      q * cStepBase + q * (cStepQ * q) + q * (cStepQep * bits qep) := by ring
  have hmfj : CryptoGames.LibsignalSession.maxForwardJumps = 25000 := rfl
  simp only [spkTier1Budget, hmfj]
  have hrhs : 2 ^ 10 * (q + 1) ^ 2 + 2 ^ 9 * 25000 * (q + 1) + 2 ^ 8 * (q + 1) * bits qep =
      12801024 + 12802048 * q + 1024 * (q * q) + 256 * bits qep + 256 * (q * bits qep) := by ring
  have hm1 : q * 12800000 = 12800000 * q := by ring
  have hm2 : q * (1024 * q) = 1024 * (q * q) := by ring
  have hm3 : q * (256 * bits qep) = 256 * (q * bits qep) := by ring
  rw [hlhs, hrhs]
  rw [hm1] at h1
  rw [hm2] at h2
  rw [hm3] at h3
  omega

private theorem q_add_eleven_le_spkTier1Budget (q' qep' : ℕ) :
    q' + 11 ≤ spkTier1Budget q' qep' := by
  have h := session_cost_le_spkTier1Budget q' qep' 100 0 400 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

private theorem spkLeakRed_totalCost_le_tier1 (ℓ q qep : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
      spkTier1Budget q qep' := by
  unfold spkLeakRed
  split_ifs with hℓ
  · have hinit := spkInitC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
      (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hhandle :
        max 1
          ((spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ 5430000 + 550 * q + 2 * bits qep' := by
      rw [spkLeakRedReal_handle_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      generalize (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost = cStep
        at hstep ⊢
      omega
    have hmul :
        q * max 1
          ((spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ q * (5430000 + 550 * q + 2 * bits qep') :=
      Nat.mul_le_mul_left q hhandle
    have hinit_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost ≤
          65000 := by
      rw [spkLeakRedReal_init_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact hinit
    have hfin_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1)
        (.fst (.snd (.snd (.snd .v0)))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), .bool] .bool)).cost ≤ 100
      dsimp only [orE, boolEq, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
      decide
    have htot :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
          65000 + q * (5430000 + 550 * q + 2 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface, e2eSessionCodec]
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost =
        ci at hinit_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost =
        ch at hhandle hmul ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost =
        cf at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_spkTier1Budget q qep' 65000 100 5430000 550 2
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · have hcost :
        (dummyBoolSessionRed
          (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (extractPtPrfIface ℓ Pt) BV256).totalCost q = 6 + q * 24 := by
      simp [dummyBoolSessionRed, CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface,
        e2eSessionCodec, Comp.cost, Expr.cost]
      omega
    rw [hcost]
    simpa using session_cost_le_spkTier1Budget q qep' 6 0 24 0 0
      (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem spkLeakRed_size_le_tier1 (ℓ q qep : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (spkTier1Budget q qep') := by
  unfold spkLeakRed
  split_ifs with hℓ
  · have hinit := spkInitC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hqB : q + 11 ≤ spkTier1Budget q qep' := q_add_eleven_le_spkTier1Budget q qep'
    have hbq : bits q ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hbqep : bits qep ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hbqep1 : bits (qep + 1) ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hinit_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size ≤
          5500 := by
      rw [spkLeakRedReal_init_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact hinit
    have hhandle_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size ≤
          1730000 + 198 * bits (spkTier1Budget q qep') := by
      rw [spkLeakRedReal_handle_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      omega
    have hfin_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1)
        (.fst (.snd (.snd (.snd .v0)))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), .bool] .bool)).size ≤ 100
      dsimp only [orE, boolEq, Comp.size, Expr.size, Expr.v0, Expr.v1]
      decide
    have hsz :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
          1737000 + 198 * bits (spkTier1Budget q qep') := by
      dsimp only [CostedReduction.size]
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size =
        si at hinit_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size =
        sh at hhandle_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size =
        sf at hfin_le ⊢
      omega
    exact size_le_budget_of_log_cost (by decide) (by decide) hsz
  · exact (dummyBoolSessionRed_size_le (extractPtPrfIface ℓ Pt) BV256).trans
      (Nat.le_add_right _ _)

/-- `GRedBounded` for `spkLeakRed` at `spkTier1Budget q qep` under `qep ≤ q + 10`. -/
theorem spkLeakRed_gRedBounded_tier1 (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier1Budget q qep) :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier1Budget q qep)
    (spkLeakRed_totalCost_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep (Nat.le_refl qep))
    (spkLeakRed_size_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRed_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

end SpkLeakRed
end Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInDefs

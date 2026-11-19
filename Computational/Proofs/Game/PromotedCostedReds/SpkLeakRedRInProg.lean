/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SessionCostExactDefs -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInDefs
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

namespace Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg

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
open Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInDefs (atomicPrfIface_liftP spkLeakRedU spkLeakRedU_totalQueries spkLeakRedU_totalCost spkLeakRedU_totalCost_le spkLeakRedU_totalCost_q_le spkLeakRedU_size_le spkLeakRedU_gRedBounded spkLeakRedU_gRedBounded_q spkLeakRedU_eval_family spkLeakRedU_eval spkInitArgT spkInitAliceE2EE eval_spkInitAliceE2EE cost_spkInitAliceE2EE size_spkInitAliceE2EE spkInitGsE2EE eval_spkInitGsE2EE cost_spkInitGsE2EE size_spkInitGsE2EE dlPreE2EE cost_dlPreE2EE size_dlPreE2EE dlPostE2EE cost_dlPostE2EE size_dlPostE2EE ijPreE2EE cost_ijPreE2EE size_ijPreE2EE ijPostE2EE cost_ijPostE2EE size_ijPostE2EE eval_dlPreE2EE eval_dlPostE2EE eval_ijPreE2EE eval_ijPostE2EE sPureOp sSymOp sGroupOp sPtDecOp sCurveOp eval_sPureOp cost_sPureOp eval_sSymOp cost_sSymOp eval_sGroupOp cost_sGroupOp eval_sPtDecOp cost_sPtDecOp eval_sCurveOp cost_sCurveOp size_sPureOp size_sSymOp size_sGroupOp size_sPtDecOp size_sCurveOp senderKeyPtAtomicE cost_senderKeyPtAtomicE size_senderKeyPtAtomicE eval_senderKeyPtAtomicE prepRecvB0StateAtomicE cost_prepRecvB0StateAtomicE size_prepRecvB0StateAtomicE eval_prepRecvB0StateAtomicE receiveSpkAtomicC receiveSpkAtomicC_queries receiveSpkAtomicC_size_le receiveSpkAtomicC_cost_tier1 receiveSpkAtomicC_cost r_partyToBool_eq_partyEnc spkInitC spkInitC_queries atomicDraw256_size spkInitC_size_le smReachBounded_accept spkDlArmC spkDlArmC_queries spkDlArmC_size_le spkIjArmC spkIjArmC_queries spkIjArmC_size_le spkStepC spkStepC_queries spkStepC_size_le spkInitImpl spkInitC_cost spkDlArmC_cost spkIjArmC_cost spkStepC_cost spkLeakRedReal spkLeakRed spkLeakRed_totalQueries_le spkLeakRedReal_init_cost spkLeakRedReal_handle_cost spkLeakRed_totalCost_le spkLeakRedReal_init_size spkLeakRedReal_handle_size spkLeakRed_size_le_of_clamp spkLeakRed_size_le spkLeakRed_gRedBounded_of_clamp spkLeakRed_gRedBounded_of_le spkLeakRed_gRedBounded spkLeakRed_gRedBounded_succ spkLeakRed_gRedBounded_tier1)

export Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInDefs
  (spkLeakRedU spkLeakRedU_totalCost spkLeakRedU_size_le spkLeakRedU_totalQueries)

section ReceiveSpkAtomic

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "PrfI" => extractPtPrfIface ℓ Pt


theorem receiveSpkAtomicC_eval_and_inv {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (hg : PartyReachInv C K (gE.eval ρ)) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).eval ρ =
      (Option.map (fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
          (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) <$>
        (receiveSpk P ℓ Dh encT decT (sE.eval ρ) (gE.eval ρ) (cE.eval ρ) (rcE.eval ρ))) ∧
    (∀ r ∈ support (receiveSpk P ℓ Dh encT decT (sE.eval ρ) (gE.eval ρ) (cE.eval ρ) (rcE.eval ρ)),
      ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st') := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set s := sE.eval ρ
  set g := gE.eval ρ
  set c := cE.eval ρ
  set rc := rcE.eval ρ
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  set ρ₁ := Env.cons (t := t0) (s, (g, (c, rc))) ρ
  have hisBob :
      (Expr.and (.fst (sPureOp .ghostStateSplit (.fst (.snd (Expr.v0 (O := AOps))))))
        (.eqN (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
          (sPureOp .ghostStateSplit (.fst (.snd .v0))))))))))) (.nat 0))).eval ρ₁ =
      (g.party == .B && g.epoch == 0) := by
    simp only [ρ₁, Expr.eval, Expr.v0, Env.get, eval_sPureOp]
    dsimp only [ReductionDsl.AtomicPureOp.eval, ReductionDsl.ghostSplitEval]
    (cases g.party <;> simp [ReductionDsl.partyToBool]); rfl
  have hlhs_ite :
      (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) sE gE cE rcE).eval ρ =
      if (g.party == .B && g.epoch == 0) = true then
        (Comp.caseOpt (O := AOps)
          (senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (.fst (.snd (.snd .v0))))
          (.ret .none)
          (.bind
            (Comp.query (I := PrfI) ()
              (sGroupOp .ptDh (.pair (.fst .v1) (.snd .v0))))
            (.caseOpt
              (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (.pair (.fst (.snd .v2))
                  (.pair (.fst .v1)
                    (.pair (.snd (.snd (.snd .v2))) .v0))))
              (.ret .none)
              (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                (decT := decT) (lam := lam) PrfI
                (.pair .v0
                  (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3))))))))).eval ρ₁
      else
        (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) PrfI
          (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))).eval ρ₁ := by
    unfold receiveSpkAtomicC
    rw [comp_eval_bind_ret]
    have hp : (Expr.pair sE (.pair gE (.pair cE rcE))).eval ρ = (s, (g, (c, rc))) := rfl
    rw [hp, comp_eval_ite, hisBob]
  rw [hlhs_ite]
  unfold receiveSpk
  by_cases hb0 : g.party == .B && g.epoch == 0
  · obtain ⟨hpB_beq, hep0_beq⟩ := Bool.and_eq_true_iff.mp hb0
    have hpB : g.party = .B := by cases hp : g.party <;> simp_all
    simp only [hb0, ↓reduceIte]
    unfold receiveB0
    rw [comp_eval_caseOpt]
    have hsk := eval_senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (.fst (.snd (.snd .v0))) ρ₁
    have hc1 : (Expr.fst (.snd (.snd (Expr.v0 (O := AOps))))).eval ρ₁ = c := rfl
    rw [hc1] at hsk
    rw [hsk]
    have hcodec : P.codec = protoSignalCodec := rfl
    rw [hcodec]
    cases htry : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec c with
    | error _ =>
      simp [comp_eval_ret, Expr.eval]
    | ok msg =>
      dsimp only
      cases hdec : decT msg.senderRatchetKey with
      | none =>
        simp [comp_eval_ret, Expr.eval]
      | some T =>
        dsimp only
        by_cases hbad : T = 0 ∨ encT T ≠ msg.senderRatchetKey
        · simp [hbad, comp_eval_ret, Expr.eval]
        · simp only [hbad, ↓reduceIte, map_bind]
          have hqlhs :
              (Comp.query (O := AOps) (I := PrfI) ()
                (sGroupOp .ptDh (.pair (.fst .v1) (.snd .v0)))).eval
                (Env.cons (t := .prod PK PtT) (msg.senderRatchetKey, T) ρ₁) =
              (CryptoGames.MACScheme.evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh s T) :
                OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) := by
            dsimp only [Comp.eval, extractPtPrfIface, atomicPrfIface]
            have hdh :
                (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) .ptDh (.pair (.fst .v1) (.snd .v0))).eval
                  (Env.cons (t := .prod PK PtT) (msg.senderRatchetKey, T) ρ₁) = Dh.dh s T := rfl
            rw [hdh]
            simp only [map_eq_bind_pure_comp, Function.comp_def, bind_pure]
            rfl
          rw [comp_eval_bind, hqlhs]
          have hbranch : ∀ prk : BitVec 256,
              (let ρ₂ := Env.cons (t := BV256) prk
                  (Env.cons (t := .prod PK PtT) (msg.senderRatchetKey, T) ρ₁)
               (Comp.caseOpt (O := AOps) (I := PrfI)
                 (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam)
                   (.pair (.fst (.snd .v2))
                     (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0))))
                 (.ret .none)
                 (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam) PrfI
                   (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3))))))).eval
                 ρ₂) =
                Option.map
                  (fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
                    (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) <$>
                (let (rk1, ck1) := (expandPRG P.C.F).gen prk
                 match rootCreateChain P.C rk1 msg.senderRatchetKey
                     (KeyPair.generate P.C rc).privateKey with
                 | .error _ => pure none
                 | .ok (rk2, ck2) =>
                   let sess' : SessionState Bytes :=
                     { g.session with
                       previousCounter := 0
                       rootKey := rk2
                       receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
                       senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
                   match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
                       msg .whisper rc sess' with
                   | (.error _, _) => pure none
                   | (.ok m, s_out) =>
                     let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
                     pure (some ({ g with session := s_out, epoch := 1, chainEpochs := epochs },
                       1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m))) ∧
              (∀ r ∈ support
                (let (rk1, ck1) := (expandPRG P.C.F).gen prk
                 match rootCreateChain P.C rk1 msg.senderRatchetKey
                     (KeyPair.generate P.C rc).privateKey with
                 | .error _ =>
                   (pure none :
                     OracleComp (unifSpec + prfSpec Pt (BitVec 256))
                       (Option (GhostState Bytes × ℕ × ℕ × Plain ℓ)))
                 | .ok (rk2, ck2) =>
                   let sess' : SessionState Bytes :=
                     { g.session with
                       previousCounter := 0
                       rootKey := rk2
                       receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
                       senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
                   match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
                       msg .whisper rc sess' with
                   | (.error _, _) => pure none
                   | (.ok m, s_out) =>
                     let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
                     pure (some ({ g with session := s_out, epoch := 1, chainEpochs := epochs },
                       1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m))),
                ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st') := by
            intro prk
            let ρ₂ := Env.cons (t := BV256) prk
              (Env.cons (t := .prod PK PtT) (msg.senderRatchetKey, T) ρ₁)
            have hprep := eval_prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0))) ρ₂
            have harg2 :
                (Expr.pair (.fst (.snd (Expr.v2 (O := AOps))))
                  (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0))).eval ρ₂ =
                (g, (msg.senderRatchetKey, (rc, prk))) := rfl
            rw [harg2] at hprep
            dsimp only at hprep
            have hprg1 : ((expandPRG C.F).1 prk).1 = ((expandPRG C.F).gen prk).1 := rfl
            have hprg2 : ((expandPRG C.F).1 prk).2 = ((expandPRG C.F).gen prk).2 := rfl
            rw [hprg1, hprg2] at hprep
            rw [comp_eval_caseOpt, hprep]
            have hPC : P.C = C := rfl
            rw [hPC]
            rcases hprg : (expandPRG C.F).gen prk with ⟨rk1, ck1⟩
            dsimp only
            rcases hrc : rootCreateChain C rk1 msg.senderRatchetKey
                (KeyPair.generate C rc).privateKey with _ | ⟨rk2, ck2⟩
            · dsimp only
              refine ⟨?_, ?_⟩
              · rw [comp_eval_ret]
                simp only [Expr.eval, map_pure, Option.map]
              · intro r hr _ _ _ _ hrEq
                simp only [support_pure, Set.mem_singleton_iff] at hr
                subst hr
                cases hrEq
            · dsimp only
              set sess' : SessionState Bytes :=
                { g.session with
                  previousCounter := 0
                  rootKey := rk2
                  receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
                  senderChain := some ⟨KeyPair.generate C rc, ck2⟩ }
              set g' : GhostState Bytes := { g with session := sess', epoch := 1, chainEpochs := [1] }
              have hg' : PartyReachInv C K g' := by
                refine ⟨hg.topTight, ?_, ?_, ?_, rfl⟩
                · simp [g', sess', maxReceiverChains]
                · intro rch hrch
                  simp only [g', sess', List.mem_singleton] at hrch
                  subst hrch
                  simp [maxMessageKeys]
                · intro rch hrch mk hmk
                  simp only [g', sess', List.mem_singleton] at hrch
                  subst hrch
                  simp at hmk
              let ρ₃ := Env.cons (t := GhostStT) g' ρ₂
              have hdr := drReceiveAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) PrfI
                (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))
                ρ₃ idA idB hg'
              have harg3 :
                  (Expr.pair (Expr.v0 (O := AOps))
                    (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3))))).eval ρ₃ =
                  (g', (c, rc)) := rfl
              rw [harg3] at hdr
              have hrecv_eq :
                  ((P.receive g' c rc).map fun (g_out, t, idx, ptBytes) =>
                    (g_out, t, idx, padOrTruncatePlain ℓ ptBytes)) =
                  match SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                      msg .whisper rc sess' with
                  | (.error _, _) => none
                  | (.ok m, s_out) =>
                    let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
                    some ({ g with session := s_out, epoch := 1, chainEpochs := epochs },
                      1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m) := by
                dsimp only [CryptoGames.LibsignalSession.Params.receive]
                rw [hcodec, htry]
                dsimp only
                have hg'P : g'.party = .B := hpB
                have hg'S : g'.session = sess' := rfl
                rw [hg'P, hg'S, hPC]
                cases hdec2 : SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                    msg .whisper rc sess' with
                | mk res s_out =>
                  cases res with
                  | error _ => rfl
                  | ok m =>
                    have hfind :
                        sess'.receiverChains.findIdx?
                          (·.senderRatchetKey == msg.senderRatchetKey) = some 0 := by
                      simp [sess', List.findIdx?, List.findIdx?.go]
                    simp only [g', hfind, List.length_singleton, Option.map]
                    rfl
              refine ⟨?_, ?_⟩
              · change (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam) PrfI
                    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))).eval ρ₃ = _
                rw [hdr]
                change pure (Option.map (fun (g_out, t, idx, ptBytes) =>
                    (g_out, t, idx, padOrTruncatePlain ℓ ptBytes)) (P.receive g' c rc)) = _
                rw [hrecv_eq]
                cases hdec2 : SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                    msg .whisper rc sess' with
                | mk res s_out =>
                  cases res with
                  | error _ => simp only [map_pure, Option.map]
                  | ok m => simp only [map_pure, Option.map]
              · intro r hr st' t' i' m' hrEq
                subst hrEq
                have hfixed : (sessionSchemeFixedSpk P ℓ s).receive g' c rc =
                    some (st', t', i', m') := by
                  dsimp only [sessionSchemeFixedSpk]
                  rw [hrecv_eq]
                  cases hdecRec : SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                      msg .whisper rc sess' with
                  | mk res s_out =>
                    cases res with
                    | error _ =>
                      rw [hdecRec] at hr
                      dsimp only at hr
                      simp only [support_pure, Set.mem_singleton_iff] at hr
                      cases hr
                    | ok m =>
                      rw [hdecRec] at hr
                      dsimp only at hr ⊢
                      simp only [support_pure, Set.mem_singleton_iff] at hr
                      exact hr.symm
                exact partyReachInv_fixedSpk_receive C K idA idB ℓ s hg' hfixed
          refine ⟨bind_congr fun prk => (hbranch prk).1, ?_⟩
          intro r hr st' t' i' m' hrEq
          rw [mem_support_bind_iff] at hr
          obtain ⟨prk, -, hr⟩ := hr
          exact (hbranch prk).2 r hr st' t' i' m' hrEq
  · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    have hdr := drReceiveAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) PrfI
      (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))
      ρ₁ idA idB hg
    have harg1 :
        (Expr.pair (.fst (.snd (Expr.v0 (O := AOps))))
          (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))))).eval ρ₁ =
        (g, (c, rc)) := rfl
    rw [harg1] at hdr
    rw [hdr]
    have hU : (CryptoVerification.E2E.sessionSchemeU P ℓ).receive g c rc =
        (sessionSchemeFixedSpk P ℓ s).receive g c rc := rfl
    rw [hU]
    refine ⟨?_, ?_⟩
    · simp only [sessionSchemeFixedSpk, P, map_pure, Option.map_map, Function.comp_def]
    · intro r hr st' t' i' m' hrEq
      subst hrEq
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact partyReachInv_fixedSpk_receive C K idA idB ℓ s hg hr.symm

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


theorem spkDlArmC_eval_and_inv (q qRem : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).eval
      (.cons (s, (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c))) .nil) =
      (fun out : Option (RecvResult (Plain ℓ)) × GameState (GhostState Bytes) (Plain ℓ) Bytes =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (none, (out.1.map recvResultEnc, none)),
          (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) <$>
        (deliverSpk P ℓ Dh encT decT s (party, c)).run st ∧
    (∀ r ∈ support ((deliverSpk P ℓ Dh encT decT s (party, c)).run st),
      SmReachBounded C K (qRem + 1) r.2) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  let ρ₀ : Env [t0] := .cons (s, (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c))) .nil
  unfold spkDlArmC deliverSpk
  have hpreL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
    (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)
  have hpreE := eval_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
    st party c hQ.lists.trans_le
  rw [comp_eval_caseSum]
  have hpreStep :
      (Expr.letE (O := AOps) (.snd .v0)
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))).eval ρ₀ =
      liftVal (Pt := Pt)
        ((dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
          (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)) := by
    rw [letE_eval, wk1Expr_eval]
    exact hpreL
  rw [hpreStep, hpreE]
  by_cases hwin : st.win
  · simp only [hwin, ↓reduceIte, liftVal, comp_eval_ret, Expr.eval, Expr.v0, Expr.v1, Env.get,
      StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, map_pure]
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hRem.mono (Nat.le_succ qRem)
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    cases htr : st.inTransit party.other c with
    | none =>
      simp only [liftVal, comp_eval_ret, Expr.eval, Expr.v0, Expr.v1, Env.get,
        StateT.run_pure, map_pure]
      refine ⟨rfl, fun r hr => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hRem.mono (Nat.le_succ qRem)
    | some rec_ =>
      dsimp only [liftVal]
      rw [comp_eval_bind, atomicDraw256_eval, atomicPrfIface_liftP]
      simp only [comp_eval_bind, comp_eval_ret,
        StateT.run_bind, StateT.run_lift, bind_assoc, map_bind]
      have hbranch : ∀ rc : BitVec 256,
          (let ρ₂ : Env [BV256, .prod GhostStT posTy, t0] :=
              .cons rc (.cons (st.st party, posEnc rec_.pos) ρ₀)
           (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (.fst .v2) (.fst .v1) (.snd (.snd (.snd .v2))) .v0).eval ρ₂ >>=
            fun out =>
              pure ((Expr.letE (O := AOps) (.pair (.snd .v3) (.pair (.snd .v2) .v0))
                (.letE (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (dlPostE2EE (ℓ := ℓ) (C := C) (K := K)
                    (decT := decT) (encT := encT) q)))
                  (.pair (.fst .v0) (.pair (.fst .v5) (.snd .v0))))).eval (.cons out ρ₂))) =
          (receiveSpk P ℓ Dh encT decT s (st.st party) c rc >>= fun r =>
            (match r with
              | none => (pure (some RecvResult.rejected) :
                  StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
                    (OracleComp (unifSpec + prfSpec Pt (BitVec 256))) (Option (RecvResult (Plain ℓ))))
              | some (st', t', i', m') => do
                set (st.accept party st' rec_.pos)
                pure (some (.accepted t' i'
                  (if st.chall.contains rec_.pos then none else some m')))).run st >>=
              fun out => pure (liftVal (Pt := Pt)
                (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
                (none, (out.1.map recvResultEnc, none)),
                (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) ∧
          (∀ r ∈ support (receiveSpk P ℓ Dh encT decT s (st.st party) c rc >>= fun res =>
              (match res with
                | none => (pure (some RecvResult.rejected) :
                    StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
                      (OracleComp (unifSpec + prfSpec Pt (BitVec 256)))
                      (Option (RecvResult (Plain ℓ))))
                | some (st', t', i', m') => do
                  set (st.accept party st' rec_.pos)
                  pure (some (.accepted t' i'
                    (if st.chall.contains rec_.pos then none else some m')))).run st),
            SmReachBounded C K (qRem + 1) r.2) := by
        intro rc
        let ρ₂ : Env [BV256, .prod GhostStT posTy, t0] :=
          .cons rc (.cons (st.st party, posEnc rec_.pos) ρ₀)
        have hrecv := receiveSpkAtomicC_eval_and_inv (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.fst .v2) (.fst .v1) (.snd (.snd (.snd .v2))) .v0 ρ₂ idA idB (hQ.reach.party party)
        have hrecv1 :
            (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (.fst .v2) (.fst .v1) (.snd (.snd (.snd .v2))) .v0).eval ρ₂ =
            Option.map (fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
              (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) <$>
              receiveSpk P ℓ Dh encT decT s (st.st party) c rc := hrecv.1
        have hrecv2 :
            ∀ r ∈ support (receiveSpk P ℓ Dh encT decT s (st.st party) c rc),
              ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st' := hrecv.2
        refine ⟨?_, ?_⟩
        · dsimp only
          rw [hrecv1, bind_map_left]
          refine bind_congr fun res => ?_
          let outE2E : (drRecvOutT ℓ).denote :=
            res.map fun x => (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))
          have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
            (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, outE2E)) .nil)
          have hpostE := eval_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
            q st party c rec_.pos outE2E hQ.lists
          dsimp only [Comp.eval, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Expr.v5, Env.get, ρ₂, ρ₀]
          rw [wk1Expr_eval]
          have hargPost :
              (Env.cons
                (t := .prod (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
                  (.prod (liftTy (Pt := Pt) posTy) (liftTy (Pt := Pt) (drRecvOutT ℓ))))
                ((liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c)),
                  (posEnc rec_.pos, liftVal (Pt := Pt) (t := drRecvOutT ℓ) outE2E)) .nil) =
              liftEnv (Pt := Pt)
                (.cons
                  (t := .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
                    (.prod posTy (drRecvOutT ℓ)))
                  ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, outE2E)) .nil) := by
            rcases res with _ | ⟨_, _, _, _⟩ <;> rfl
          have houtLift :
              (res.map fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
                (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) =
                liftVal (Pt := Pt) (t := drRecvOutT ℓ) outE2E := by
            rcases res with _ | ⟨_, _, _, _⟩ <;> rfl
          simp only [houtLift, Env.get]
          rw [hargPost, hpostL, hpostE]
          rcases res with _ | ⟨st', t', i', m'⟩
          · simp [outE2E, StateT.run_pure, liftVal]
          · simp [outE2E, StateT.run_set, liftVal]
        · intro r hr
          rw [mem_support_bind_iff] at hr
          obtain ⟨res, hres, hr⟩ := hr
          rcases res with _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact hRem.mono (Nat.le_succ qRem)
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hr
            subst hr
            exact smReachBounded_accept C K hRem party
              (hrecv2 _ hres st' t' i' m' rfl) rec_.pos
      refine ⟨?_, ?_⟩
      · simp only [map_eq_bind_pure_comp, Function.comp_def, pure_bind]
        exact bind_congr fun rc => (hbranch rc).1
      · intro r hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨rc, -, hr⟩ := hr
        exact (hbranch rc).2 r hr


theorem spkIjArmC_eval_and_inv (q qRem qep : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
      (.cons (s, (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c))) .nil) =
      (fun out : Option (RecvResult (Plain ℓ)) × GameState (GhostState Bytes) (Plain ℓ) Bytes =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (none, (out.1.map recvResultEnc, none)),
          (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) <$>
        (injectSpk P ℓ Dh encT decT qep s (party, c)).run st ∧
    (∀ r ∈ support ((injectSpk P ℓ Dh encT decT qep s (party, c)).run st),
      SmReachBounded C K (qRem + 1) r.2) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  let ρ₀ : Env [t0] := .cons (s, (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c))) .nil
  unfold spkIjArmC injectSpk
  have hpreL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
    (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)
  have hpreE := eval_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q 3
    st party c hQ.lists.trans_le
  rw [comp_eval_caseSum]
  have hpreStep :
      (Expr.letE (O := AOps) (.snd .v0)
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))))).eval
        ρ₀ =
      liftVal (Pt := Pt)
        ((ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)).eval
          (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)) := by
    rw [letE_eval, wk1Expr_eval]
    exact hpreL
  rw [hpreStep, hpreE]
  by_cases href :
      st.win || (st.inTransit party.other c).isSome || !(st.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp only [href, ↓reduceIte, liftVal, comp_eval_ret, Expr.eval, Expr.v0, Expr.v1, Env.get,
      StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, map_pure]
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hRem.mono (Nat.le_succ qRem)
  · simp only [href, Bool.false_eq_true, ↓reduceIte, liftVal, StateT.run_bind, StateT.run_get,
      StateT.run_lift, pure_bind, bind_assoc, map_bind]
    rw [comp_eval_bind, atomicDraw256_eval, atomicPrfIface_liftP]
    simp only [comp_eval_bind, comp_eval_ret]
    have hbranch : ∀ rc : BitVec 256,
        (let ρ₂ : Env [BV256, GhostStT, t0] := .cons rc (.cons (st.st party) ρ₀)
         (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (.fst .v2) .v1 (.snd (.snd (.snd .v2))) .v0).eval ρ₂ >>=
          fun out =>
            pure ((Expr.letE (O := AOps) (.pair (.snd .v3) .v0)
              (.letE (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (ijPostE2EE (ℓ := ℓ) (C := C) (K := K)
                  (decT := decT) (encT := encT) q (2 + 1) qep)))
                (.pair (.fst .v0) (.pair (.fst .v5) (.snd .v0))))).eval (.cons out ρ₂))) =
        (receiveSpk P ℓ Dh encT decT s (st.st party) c rc >>= fun r =>
          (match r with
            | none => (pure (some RecvResult.rejected) :
                StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
                  (OracleComp (unifSpec + prfSpec Pt (BitVec 256))) (Option (RecvResult (Plain ℓ))))
            | some (st', t', i', m') =>
              if qep + 1 < t' then pure (some .rejected)
              else
                let pos : Pos := ⟨party.other, t', i'⟩
                if st.trivial 3 pos then do
                  set (st.accept party st' pos)
                  pure (some (.accepted t' i' (some m')))
                else do
                  set { st with win := true }
                  pure (some .rejected)).run st >>=
            fun out => pure (liftVal (Pt := Pt)
              (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
              (none, (out.1.map recvResultEnc, none)),
              (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) ∧
        (∀ r ∈ support (receiveSpk P ℓ Dh encT decT s (st.st party) c rc >>= fun res =>
            (match res with
              | none => (pure (some RecvResult.rejected) :
                  StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
                    (OracleComp (unifSpec + prfSpec Pt (BitVec 256)))
                    (Option (RecvResult (Plain ℓ))))
              | some (st', t', i', m') =>
                if qep + 1 < t' then pure (some .rejected)
                else
                  let pos : Pos := ⟨party.other, t', i'⟩
                  if st.trivial 3 pos then do
                    set (st.accept party st' pos)
                    pure (some (.accepted t' i' (some m')))
                  else do
                    set { st with win := true }
                    pure (some .rejected)).run st),
          SmReachBounded C K (qRem + 1) r.2) := by
      intro rc
      let ρ₂ : Env [BV256, GhostStT, t0] := .cons rc (.cons (st.st party) ρ₀)
      have hrecv := receiveSpkAtomicC_eval_and_inv (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (.fst .v2) .v1 (.snd (.snd (.snd .v2))) .v0 ρ₂ idA idB (hQ.reach.party party)
      have hrecv1 :
          (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (.fst .v2) .v1 (.snd (.snd (.snd .v2))) .v0).eval ρ₂ =
          Option.map (fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
            (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) <$>
            receiveSpk P ℓ Dh encT decT s (st.st party) c rc := hrecv.1
      have hrecv2 :
          ∀ r ∈ support (receiveSpk P ℓ Dh encT decT s (st.st party) c rc),
            ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st' := hrecv.2
      refine ⟨?_, ?_⟩
      · dsimp only
        rw [hrecv1, bind_map_left]
        refine bind_congr fun res => ?_
        let outE2E : (drRecvOutT ℓ).denote :=
          res.map fun x => (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))
        have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep)
          (.cons ((e2eGsEnc st, (partyEnc party, c)), outE2E) .nil)
        have hpostE := eval_ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
          q 3 qep st party c outE2E hQ.lists
        dsimp only [Comp.eval, Expr.eval, Expr.v0, Expr.v3, Expr.v5, Env.get, ρ₂, ρ₀]
        rw [wk1Expr_eval]
        have hargPost :
            (Env.cons
              (t := .prod (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
                (liftTy (Pt := Pt) (drRecvOutT ℓ)))
              ((liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c)),
                liftVal (Pt := Pt) (t := drRecvOutT ℓ) outE2E)
              .nil) =
            liftEnv (Pt := Pt)
              (.cons
                (t := .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
                  (drRecvOutT ℓ))
                ((e2eGsEnc st, (partyEnc party, c)), outE2E) .nil) := by
          rcases res with _ | ⟨_, _, _, _⟩ <;> rfl
        have houtLift :
            (res.map fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
              (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) =
              liftVal (Pt := Pt) (t := drRecvOutT ℓ) outE2E := by
          rcases res with _ | ⟨_, _, _, _⟩ <;> rfl
        simp only [houtLift, Env.get]
        rw [hargPost, hpostL, hpostE]
        rcases res with _ | ⟨st', t', i', m'⟩
        · simp [outE2E, StateT.run_pure, liftVal]
        · simp only [outE2E, Option.map]
          by_cases hqep : qep + 1 < t'
          · simp [hqep, StateT.run_pure, liftVal]
          · simp only [hqep, ↓reduceIte]
            by_cases htriv : st.trivial 3 ⟨party.other, t', i'⟩
            · simp [htriv, StateT.run_set, liftVal]
            · simp [htriv, StateT.run_set, liftVal]
      · intro r hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨res, hres, hr⟩ := hr
        rcases res with _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hRem.mono (Nat.le_succ qRem)
        · dsimp only at hr
          by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at hr
            subst hr; exact hRem.mono (Nat.le_succ qRem)
          · simp only [hqep, ↓reduceIte] at hr
            by_cases htriv : st.trivial 3 ⟨party.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              exact smReachBounded_accept C K hRem party
                (hrecv2 _ hres st' t' i' m' rfl) ⟨party.other, t', i'⟩
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              exact ⟨⟨hRem.reach.alice, hRem.reach.bob⟩,
                (hRem.lists.setWin true).mono (Nat.le_succ qRem)⟩
    refine ⟨?_, ?_⟩
    · simp only [map_eq_bind_pure_comp, Function.comp_def]
      exact bind_congr fun rc => (hbranch rc).1
    · intro r hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨rc, -, hr⟩ := hr
      exact (hbranch rc).2 r hr


theorem spkStepC_eval_and_inv (q qRem qep : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
      (.cons (s, liftVal (Pt := Pt) (e2eGsEnc st))
        (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)) =
      (fun out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
            GameState (GhostState Bytes) (Plain ℓ) Bytes =>
        (liftVal (Pt := Pt)
          (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id sq out.1),
         (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) <$>
        (spkOracleImpl P ℓ Dh encT decT qep s (.inr sq)).run st ∧
    (∀ r ∈ support ((spkOracleImpl P ℓ Dh encT decT qep s (.inr sq)).run st),
      SmReachBounded C K (qRem + 1) r.2) := by
  intro P
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  change (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
      (.cons (s, liftVal (Pt := Pt) (e2eGsEnc st))
        (.cons (t := smQT) (ReductionDsl.smQenc sq) .nil)) = _ ∧ _
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v0, Expr.v3, Env.get,
      r_partyToBool_eq_partyEnc]
    let tTr : Ty ESig :=
      .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.opt CryptoVerification.E2E.Costed.BV512)))
    let argE2E : tTr.denote := (e2eGsEnc st, (partyEnc party, (m, optR)))
    have htrStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
          (drTrArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons
            (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ))
              (.prod .bool (.prod PlainT (.opt BV512))))
            (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, (m, optR))) .nil) =
        liftVal (Pt := Pt) <$>
          ((drTrArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
        (drTrArmC hooks coins q (2 + 1) qep
          (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases optR <;> rfl
    dsimp only [Expr.v0] at htrStep
    rw [htrStep]
    have htr := drTrArmC_eval hooks coins q (2 + 1) qep
      (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      idA idB s st party m optR hQ rfl rfl
    dsimp only [Expr.v0] at htr
    rw [htr]
    have hliftP :
        (coinE2EIface PrfI).liftP
          ((transmitR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT)
            (party, m, optR)).run st) =
        (liftSpkGameM
          (transmitR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (party, m, optR))).run st := by
      change (extractPtPrfIface ℓ Pt).liftP ((transmitR (sessionSchemeFixedSpk P ℓ s) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m, optR)).run st) = _
      rw [atomicPrfIface_liftP]
      rfl
    rw [hliftP]
    refine ⟨?_, ?_⟩
    · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        Prod.map, Option.map, smRenc, liftVal]
      exact bind_congr fun x => by rcases x with ⟨w, _⟩; rcases w <;> rfl
    · intro r hr
      dsimp only [liftSpkGameM] at hr
      change r ∈ support (liftM (transmitR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m, optR) st)) at hr
      rw [← liftComp_eq_liftM, support_liftComp] at hr
      exact smReachBounded_transmitR C K idA idB ℓ 3 qep qRem s
        (configRefuseEarlyBobCorr decT encT) (party, m, optR) hRem hr
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v2, Expr.v4, Env.get,
      r_partyToBool_eq_partyEnc]
    let tCh : Ty ESig :=
      .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
    let argE2E : tCh.denote := (e2eGsEnc st, (partyEnc party, (m0, (m1, optR))))
    have hchStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
          (drChArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons
            (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ))
              (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
            (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, (m0, (m1, optR)))) .nil) =
        liftVal (Pt := Pt) <$>
          ((drChArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
        (drChArmC hooks coins q (2 + 1) qep
          (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases optR <;> rfl
    dsimp only [Expr.v0] at hchStep
    rw [hchStep]
    have hch := drChArmC_eval hooks coins q (2 + 1) qep
      (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      idA idB s st party m0 m1 optR hQ rfl rfl
    dsimp only [Expr.v0] at hch
    rw [hch]
    have hliftP :
        (coinE2EIface PrfI).liftP
          ((challR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT)
            (party, m0, m1, optR)).run st) =
        (liftSpkGameM
          (challR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR))).run st := by
      change (extractPtPrfIface ℓ Pt).liftP ((challR (sessionSchemeFixedSpk P ℓ s) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR)).run st) = _
      rw [atomicPrfIface_liftP]
      rfl
    rw [hliftP]
    refine ⟨?_, ?_⟩
    · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        Prod.map, Option.map, smRenc, liftVal]
      exact bind_congr fun x => by rcases x with ⟨w, _⟩; rcases w <;> rfl
    · intro r hr
      dsimp only [liftSpkGameM] at hr
      change r ∈ support (liftM (challR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR) st)) at hr
      rw [← liftComp_eq_liftM, support_liftComp] at hr
      exact smReachBounded_challR C K idA idB ℓ 3 qep qRem s
        (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR) hRem hr
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc, smRenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, wk1Comp_eval]
    simp only [Expr.eval, Expr.v3, Env.get, r_partyToBool_eq_partyEnc]
    exact spkDlArmC_eval_and_inv C K Dh encPt encT decT idA idB lam q qRem s st party c hQ hRem
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc, smRenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, wk1Comp_eval]
    simp only [Expr.eval, Expr.v4, Env.get, r_partyToBool_eq_partyEnc]
    exact spkIjArmC_eval_and_inv C K Dh encPt encT decT idA idB lam q qRem qep s st party c hQ hRem
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v4, Expr.v6, Env.get,
      r_partyToBool_eq_partyEnc]
    let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
    let argE2E : tCr.denote := (e2eGsEnc st, partyEnc party)
    have hcrStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
          (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
            (decT := decT) (encT := encT) q
            (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) .bool)
            (liftVal (Pt := Pt) (e2eGsEnc st), partyEnc party) .nil) =
        liftVal (Pt := Pt) <$>
          ((drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
            (decT := decT) (encT := encT) q
            (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) :=
      liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
        (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
          (decT := decT) (encT := encT) q
          (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil)
    dsimp only [Expr.v0] at hcrStep
    rw [hcrStep]
    have hcr := drCrArmC_eval (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q
      (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      st party hQ.lists rfl rfl
    dsimp only [Expr.v0] at hcr
    rw [hcr]
    have hliftP :
        (coinE2EIface PrfI).liftP ((corrR (configRefuseEarlyBobCorr decT encT) party).run st) =
        (liftSpkGameM (corrR (configRefuseEarlyBobCorr decT encT) party)).run st := by
      change (extractPtPrfIface ℓ Pt).liftP ((corrR (configRefuseEarlyBobCorr decT encT) party).run st) = _
      rw [atomicPrfIface_liftP]
      rfl
    rw [hliftP]
    refine ⟨?_, ?_⟩
    · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        Prod.map, smRenc]
      refine bind_congr fun ⟨st?, s'⟩ => congrArg pure ?_
      cases st? <;> rfl
    · intro r hr
      dsimp only [liftSpkGameM] at hr
      change r ∈ support (liftM (corrR (configRefuseEarlyBobCorr decT encT) party st)) at hr
      rw [← liftComp_eq_liftM, support_liftComp] at hr
      exact smReachBounded_corrR C K ℓ qRem (configRefuseEarlyBobCorr decT encT) party hRem hr


private theorem liftM_sample_prod_bind_bv256 {γ : Type}
    (f : BitVec 256 × BitVec 256 → OracleComp (unifSpec + prfSpec Pt (BitVec 256)) γ) :
    ((liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256)) >>= f) =
      ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun a =>
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun b => f (a, b)) := by
  rw [SampleableType.uniformSample_prod_eq_bind (BitVec 256) (BitVec 256)]
  simp [← liftComp_eq_liftM, liftComp_bind, bind_assoc]

theorem spkInitC_eval_and_inv (s : BitVec 256) :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).eval (.cons s .nil) =
      Prod.map id (fun gs => (s, liftVal (Pt := Pt) (e2eGsEnc gs))) <$>
        spkInitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB s ∧
    (∀ r ∈ support (spkInitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB s),
      SmReachBounded C K 0 r.2) := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  refine ⟨?_, ?_⟩
  · dsimp only [spkInitC, spkInitImpl, initAOracle, Comp.eval]
    have hbSamp :
        ((extractPtPrfIface ℓ Pt).liftP ((extractPtPrfIface ℓ Pt).smp.samp UniformSamplerTag.bool ())) =
        (liftM ($ᵗ Bool : ProbComp Bool) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool) := by
      change (extractPtPrfIface ℓ Pt).liftP ($ᵗ Bool : ProbComp Bool) = _
      exact atomicPrfIface_liftP PtT BV256 2 (atomicSamplers ℓ Pt) ($ᵗ Bool : ProbComp Bool)
    rw [hbSamp]
    simp only [atomicDraw256_eval, bind_assoc, map_bind]
    refine bind_congr fun b => ?_
    refine bind_congr fun ck0 => ?_
    rw [liftM_sample_prod_bind_bv256]
    refine bind_congr fun alice => ?_
    refine bind_congr fun pqr => ?_
    simp only [eval_sGroupOp, Expr.eval, Expr.v1, Expr.v4,
      Env.get, ReductionDsl.AtomicGroupOp.eval]
    change ((query (spec := unifSpec + prfSpec Pt (BitVec 256))
        (.inr (Dh.dh s (Dh.dh alice Dh.base))) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= _) = _
    have hqeq :
        query (spec := unifSpec + prfSpec Pt (BitVec 256))
          (.inr (Dh.dh s (Dh.dh alice Dh.base))) =
        (CryptoGames.MACScheme.evalQuery (Input := Pt) (Tag := BitVec 256)
          (Dh.dh s (Dh.dh alice Dh.base)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) := rfl
    rw [hqeq]
    simp only [pure_bind, map_pure]
    refine bind_congr fun prk => ?_
    have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
      (.cons (t := spkInitArgT ℓ) (b, (s, ((expandPRG C.F).gen prk, (ck0, (alice, pqr))))) .nil)
    have hgs := eval_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      idA idB b s ((expandPRG C.F).gen prk).1 ((expandPRG C.F).gen prk).2 ck0 alice pqr
    simp only [Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get, wk1Expr_eval, Prod.map, id_eq]
    have harg :
        Env.cons (t := liftTy (Pt := Pt) (spkInitArgT ℓ))
          (b, (s, ((expandPRG C.F).gen prk, (ck0, (alice, pqr))))) .nil =
        liftEnv (Pt := Pt)
          (.cons (t := spkInitArgT ℓ)
            (b, (s, ((expandPRG C.F).gen prk, (ck0, (alice, pqr))))) .nil) := rfl
    rw [harg, hl, hgs]
    rfl
  · intro r hr
    dsimp only [spkInitImpl, initAOracle] at hr
    simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hr
    obtain ⟨b, -, ck0, -, ⟨alice, pqr⟩, -, prk, -, rfl⟩ := hr
    refine ⟨⟨?_, ?_⟩,
      ⟨Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0⟩⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [P, paramsIdsWithSpqr, spqrV1SessionUniformCoins, SessionState.new,
          SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage] using
          topStateTight_init C.F K .a2b pqr
      · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
      · intro rch hrch
        simp only [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains] at hrch
        have hrch' :
            rch = { senderRatchetKey := (KeyPair.generate P.C s).publicKey,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'
        simp [maxMessageKeys]
      · intro rch hrch mk hmk
        simp only [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains] at hrch
        have hrch' :
            rch = { senderRatchetKey := (KeyPair.generate P.C s).publicKey,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'
        simp at hmk
      · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
    · exact partyReachInv_fixedSpk_initB C K idA idB ℓ s ((0, ck0), (alice, pqr))


private theorem spkOracleImpl_preserves_b {PQC : Type} [SampleableType PQC]
    (P : CryptoGames.LibsignalSession.Params Bytes PQC) (ℓ qep : ℕ) (s : BitVec 256)
    (qy : (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    {out : (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Range qy ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support ((spkOracleImpl P ℓ Dh encT decT qep s qy).run st)) :
    out.2.b = st.b := by
  rcases qy with n | (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · simp only [spkOracleImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hout
    obtain ⟨_, -, rfl⟩ := hout; rfl
  · change out ∈ support (liftM (transmitR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m, optR) st)) at hout
    rw [← liftComp_eq_liftM, support_liftComp] at hout
    exact CryptoVerification.E2E.oracleImplR_preserves_b
      (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) (.inl (.inl (.inl (.inl (party, m, optR))))) st hout
  · change out ∈ support (liftM (challR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR) st)) at hout
    rw [← liftComp_eq_liftM, support_liftComp] at hout
    exact CryptoVerification.E2E.oracleImplR_preserves_b
      (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) (.inl (.inl (.inl (.inr (party, m0, m1, optR))))) st hout
  · simp only [spkOracleImpl, deliverSpk, StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases hwin : st.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; rfl
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hout
      cases htr : st.inTransit party.other c with
      | none =>
        simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; rfl
      | some rec_ =>
        simp only [htr, StateT.run_bind, StateT.run_lift, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at hout
        rcases hout with ⟨⟨rc, st0⟩, ⟨_, -, h0⟩, ⟨res, st1⟩, ⟨hres, -, h1⟩, hout⟩
        have hst0 : st0 = st := (Prod.mk.inj h0).2; subst st0
        have hst1 : st1 = st := (Prod.mk.inj h1).2; subst st1
        rcases res with _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
  · simp only [spkOracleImpl, injectSpk, StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases href :
        st.win || (st.inTransit party.other c).isSome || !(st.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; rfl
    · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
      rcases hout with ⟨⟨rc, st0⟩, ⟨_, -, h0⟩, ⟨res, st1⟩, ⟨hres, -, h1⟩, hout⟩
      have hst0 : st0 = st := (Prod.mk.inj h0).2; subst st0
      have hst1 : st1 = st := (Prod.mk.inj h1).2; subst st1
      rcases res with _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; rfl
      · dsimp only at hout
        split_ifs at hout
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
  · change out ∈ support (liftM (corrR (configRefuseEarlyBobCorr decT encT) party st)) at hout
    rw [← liftComp_eq_liftM, support_liftComp] at hout
    exact CryptoVerification.E2E.oracleImplR_preserves_b
      (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) (.inr party) st hout

/-- Exact `.eval` agreement of `spkLeakRed` with `CryptoVerification.E2E.spkLeakRed`. -/
theorem spkLeakRed_eval (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) s =
      CryptoVerification.E2E.spkLeakRed
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s A := by
  unfold spkLeakRed
  simp only [hℓ, ↓reduceIte]
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let so := spkOracleImpl P ℓ Dh encT decT qep s
  let enc : GameState (GhostState Bytes) (Plain ℓ) Bytes →
      (Ty.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ))).denote :=
    fun gs => (s, liftVal (Pt := Pt) (e2eGsEnc gs))
  let Inv : ℕ → GameState (GhostState Bytes) (Plain ℓ) Bytes → Prop :=
    fun m gs => m ≤ q ∧ SmReachBounded C K (q - m) gs
  have hinitBoth := spkInitC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam s
  have hsim := eval_eq_simulateQ_of_enc
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
    enc Inv
    (spkInitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB)
    so
    (fun s₁ b' => pure (s₁.b == b' || s₁.win))
    q s
    hinitBoth.1
    (fun r hr => by
      refine ⟨Nat.le_refl q, ?_⟩
      rw [Nat.sub_self]
      exact hinitBoth.2 r hr)
    (fun n gs => rfl)
    (fun m sq gs hs => by
      have hreachQ : SmReachBounded C K q gs := hs.2.mono (by omega)
      have hstep := spkStepC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
        q (q - (m + 1)) qep s gs sq hreachQ hs.2
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
              (.cons (enc gs) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id enc <$> (so (.inr sq)).run gs
        rw [hstep.1]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun ⟨ans, s'⟩ => congrArg pure ?_
        exact Prod.ext (e2eSessionCodec_rdec_liftVal_smRenc Pt sq ans) rfl
      · intro r hr
        have hr' := hstep.2 r hr
        refine ⟨by omega, ?_⟩
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact heq ▸ hr')
    (fun s₁ b' _ => by
      dsimp only [spkLeakRedReal, Comp.eval]
      simp [orE_eval, boolEq_eval, e2eGsEnc, liftVal, Expr.eval, Expr.v0, Expr.v1, enc])
    (fun {m n} gs hmn hn => ⟨by omega, hn.2.mono (by omega)⟩)
    (fun _ => A)
    (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]
  unfold CryptoVerification.E2E.spkLeakRed spkInitImpl
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  refine bind_congr fun ck0 => ?_
  refine bind_congr fun rest => ?_
  refine bind_congr fun stA => ?_
  set initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
    { st := fun Q => match Q with | .A => stA | .B => P.initB ⟨0, ck0, s, rest.1, rest.2⟩, b := b }
  refine bind_congr_of_mem_support' ((simulateQ so A).run initSt) ?_
  intro ⟨b', finalSt⟩ hr
  have hb_pres : ∀ {α : Type}
      {oa : OracleComp (unifSpec +
        CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α}
      (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (r : α × GameState (GhostState Bytes) (Plain ℓ) Bytes),
      r ∈ support ((simulateQ so oa).run gs) → r.2.b = gs.b := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro gs r hr0
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr0
      subst hr0; rfl
    | query_bind qy mx ih =>
      intro gs r hr0
      rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr0
      obtain ⟨⟨u, s'⟩, hst, hr0⟩ := hr0
      have hs' : s'.b = gs.b := spkOracleImpl_preserves_b Dh encT decT P ℓ qep s qy gs hst
      exact (ih u s' r hr0).trans hs'
  have hbEq : finalSt.b = b := hb_pres initSt (b', finalSt) hr
  rw [hbEq]

theorem spkLeakRed_eval_paramsV1 (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) s =
      CryptoVerification.E2E.spkLeakRed (paramsV1 C K idA idB) Dh encPt encT decT qep s A :=
  spkLeakRed_eval C K Dh encPt encT decT idA idB lam ℓ q qep s A hA hℓ

end SpkLeakRed

end Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg

-- AUTO-BRIDGE BEGIN
namespace Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
export Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInDefs (
  atomicPrfIface_liftP spkLeakRedU spkLeakRedU_totalQueries spkLeakRedU_totalCost spkLeakRedU_totalCost_le spkLeakRedU_totalCost_q_le spkLeakRedU_size_le spkLeakRedU_gRedBounded spkLeakRedU_gRedBounded_q spkLeakRedU_eval_family spkLeakRedU_eval spkInitArgT spkInitAliceE2EE eval_spkInitAliceE2EE cost_spkInitAliceE2EE size_spkInitAliceE2EE spkInitGsE2EE eval_spkInitGsE2EE cost_spkInitGsE2EE size_spkInitGsE2EE dlPreE2EE cost_dlPreE2EE size_dlPreE2EE dlPostE2EE cost_dlPostE2EE size_dlPostE2EE ijPreE2EE cost_ijPreE2EE size_ijPreE2EE ijPostE2EE cost_ijPostE2EE size_ijPostE2EE eval_dlPreE2EE eval_dlPostE2EE eval_ijPreE2EE eval_ijPostE2EE sPureOp sSymOp sGroupOp sPtDecOp sCurveOp eval_sPureOp cost_sPureOp eval_sSymOp cost_sSymOp eval_sGroupOp cost_sGroupOp eval_sPtDecOp cost_sPtDecOp eval_sCurveOp cost_sCurveOp size_sPureOp size_sSymOp size_sGroupOp size_sPtDecOp size_sCurveOp senderKeyPtAtomicE cost_senderKeyPtAtomicE size_senderKeyPtAtomicE eval_senderKeyPtAtomicE prepRecvB0StateAtomicE cost_prepRecvB0StateAtomicE size_prepRecvB0StateAtomicE eval_prepRecvB0StateAtomicE receiveSpkAtomicC receiveSpkAtomicC_queries receiveSpkAtomicC_size_le receiveSpkAtomicC_cost_tier1 receiveSpkAtomicC_cost r_partyToBool_eq_partyEnc spkInitC spkInitC_queries atomicDraw256_size spkInitC_size_le smReachBounded_accept spkDlArmC spkDlArmC_queries spkDlArmC_size_le spkIjArmC spkIjArmC_queries spkIjArmC_size_le spkStepC spkStepC_queries spkStepC_size_le spkInitImpl spkInitC_cost spkDlArmC_cost spkIjArmC_cost spkStepC_cost spkLeakRedReal spkLeakRed spkLeakRed_totalQueries_le spkLeakRedReal_init_cost spkLeakRedReal_handle_cost spkLeakRed_totalCost_le spkLeakRedReal_init_size spkLeakRedReal_handle_size spkLeakRed_size_le_of_clamp spkLeakRed_size_le spkLeakRed_gRedBounded_of_clamp spkLeakRed_gRedBounded_of_le spkLeakRed_gRedBounded spkLeakRed_gRedBounded_succ spkLeakRed_gRedBounded_tier1
)
end Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
-- AUTO-BRIDGE END

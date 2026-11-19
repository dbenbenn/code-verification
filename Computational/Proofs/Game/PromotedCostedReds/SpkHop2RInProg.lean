/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SessionCostExactDefs -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInDefs
import Computational.Proofs.E2E.Dsl.DrSessionSim
public import Computational.Proofs.E2E.SpkHop2Red -- proof-setup: allow-public-import
public import Computational.Specifications.Session.StatementSpkModel
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
public import Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSimHooks -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSimRecv -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.SpqrSimChain
public import Computational.Proofs.E2E.Dsl.StartAndExtSmAux -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SM.GameCosted

/-!
# Promoted `CostedReduction` Witnesses for `hop2PrgRedK` and `hop2PrfRedK`

Constructs `CostedReduction` witnesses `hop2PrgRedK` and `hop2PrfRedK` over `atomicSessionOps` and
`e2eSessionCodec` via a shared `Hop2Mode`-parameterized reduction `hop2GameRed`, proving
`GRedBounded` and exact `.eval` agreement with the game-level hybrids across all
`k < spkSwapHybridCount`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface GameCodec Expr Comp CostedReduction
  UniformSamplerTag AtomicBaseUnif bits bits_mono reductionSizeBudget handlerImpl
  bind_congr_of_mem_support'
  atomicSig atomicSessionOps atomicSamplers atomicPrfIface
  coinOnlyIface extractPtPrfIface e2eSessionCodec
  BV256 BV512 U32 PtT PK GhostStT PlainT B ghostPartsT smQT smRT)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec PRFAdversary evalQuery)
open CryptoGames.Ratchet (extractPRF expandPRG rootExpand padOrTruncatePlain keyToBytesVec32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (Pos Record RecvResult GameState transmitR challR corrR
  MakesAtMostQueries partyEnc posTy posEnc orE boolEq isSomeE otherE pGet
  pair_eval some_eval ite_eval orE_eval boolEq_eval isSomeE_eval otherE_eval pGet_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey KeyPair SessionState
  RatchetState SenderChain ReceiverChain ChainKey GhostState Params SignalMessage
  currentVersion maxReceiverChains maxMessageKeys rootCreateChain)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (topStateTight_init)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr paramsV1 sessionSchemeU sessionSchemeFixedSpk
  configRefuseEarlyBobCorr spkSwapHybridCount SpkSwapPrgHybridProg evalSpkSwapPrgHybrid
  SpkSwapPrfHybridProg evalSpkSwapPrfHybrid
  Hop2Comp Hop2Hyb Hop2Aux Hop2Upd Hop2M Hop2Out hop2Unif hop2Lazy hop2Lift
  hop2RecvHalf hop2SendHalf hop2DH hop2Recv hop2BadAt hop2Commit hop2Deliver hop2Inject hop2Impl
  hop2Game spkTier1Budget)
open CryptoVerification.E2E.Costed (e2eSig e2eOps E2EPureOp E2ECryptoOp recvResultEnc
  gRedBounded_of_bounds)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp eval_e2ePureOp
  cost_e2ePureOp eval_e2eCryptoOp cost_e2eCryptoOp
  size_e2ePureOp size_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (spqrV1InitOp_eval_lossless)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv partyReachInv_receive
  partyReachInv_fixedSpk_initB partyReachInv_fixedSpk_send partyReachInv_fixedSpk_receive)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp_filter GameReachInv SmListBounded
  SmReachBounded smReachBounded_transmitR smReachBounded_challR smReachBounded_corrR)
open Computational.Proofs.E2E.Dsl.StartAndExtSmAux (initFixedSpkBobE eval_initFixedSpkBobE
  cost_initFixedSpkBobE)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (keyVec_bytesToKey32_vec privateKey_roundtrip
  encodeSenderChain decodeSenderChain decodeSenderChain_encodeSenderChain
  encodeRecvChain decodeRecvChain decodeRecvChain_encodeRecvChain decodeRecvChains_encodeRecvChains
  boolToParty_partyToBool_eq ghostSplitEval_eq_of_le ghostJoinEval_eq_of_le
  gpIsB gpVer gpLocId gpRemId gpRk gpPend gpEp gpCEps gpSc gpRcs gpPqSt gpMk
  pushEvict5E eval_pushEvict5E cost_pushEvict5E_le)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvOutT drReceiveC)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (ratchetKeyAdmissibleE
  eval_ratchetKeyAdmissibleE cost_ratchetKeyAdmissibleE partyToBool_eq_partyEnc smRenc
  recvResultRejE recvResultAccE smRRecvE eval_recvResultRejE cost_recvResultRejE
  eval_recvResultAccE cost_recvResultAccE eval_smRRecvE cost_smRRecvE
  e2eRecTy e2eRecEncWith e2eRecPos e2eGsTy e2eGsEnc e2eGsSt e2eGsB e2eGsWin
  e2eGsSetWin eval_e2eGsSetWin cost_e2eGsSetWin_le
  e2eSafeInjE eval_e2eSafeInjE cost_e2eSafeInjE_le
  e2eChallContainsE eval_e2eChallContainsE cost_e2eChallContainsE_le
  e2eAcceptE eval_e2eAcceptE cost_e2eAcceptE_le
  e2eTrivialE eval_e2eTrivialE cost_e2eTrivialE_le
  e2eInTransitE eval_e2eInTransitE cost_e2eInTransitE_le)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drTrArmC drChArmC drCrArmC
  drTrArmC_queries_zero drChArmC_queries_zero drCrArmC_queries
  drTrArmC_cost drChArmC_cost drCrArmC_cost
  drTrArmC_eval drChArmC_eval drCrArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicSessionOps_sizeHonest
  atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  sessPureOp sessSymOp sessGroupOp sessPtDecOp sessCurveOp
  eval_sessPureOp cost_sessPureOp eval_sessSymOp cost_sessSymOp eval_sessGroupOp cost_sessGroupOp
  eval_sessPtDecOp cost_sessPtDecOp eval_sessCurveOp cost_sessCurveOp
  atomicDraw256 atomicDraw256_eval atomicDraw256_cost
  liftTy liftVal liftEnv liftExpr liftExpr_cost liftExpr_eval
  renExpr renExpr_cost renExpr_eval renComp
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
  renExpr_size wk1Expr_size wk1Comp_size
  bits_succ_le session_cost_le_ratchetCostBudget
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize (size_pushEvict5E_le
  drReceiveC_spqr_size_le size_ratchetKeyAdmissibleE size_recvResultRejE size_recvResultAccE_le
  size_smRRecvE_le size_e2eGsSetWin_le size_e2eSafeInjE_le size_e2eChallContainsE_le
  size_e2eAcceptE_le size_e2eTrivialE_le size_e2eInTransitE_le
  drTrArmC_spqr_size_le drChArmC_spqr_size_le drCrArmC_size_le)

open Computational.Proofs.Game.PromotedCostedReds.SessionCostExactDefs (BoxEq box_le exprAllOps compAllOps exprAllOps_renExpr exprAllOps_wk1Expr compAllOps_renComp compAllOps_wk1Comp sessionCostExactCryptoOp sessionCostExactOp NoKemKeyGenExpr NoKemKeyGenComp liftExpr_cost_exact liftCompEmpty_cost_exact liftCompCoins_cost_exact noKemKeyGenExpr_renExpr noKemKeyGenExpr_wk1Expr noKemKeyGenComp_renComp noKemKeyGenComp_wk1Comp noKemKeyGenComp_ret noKemKeyGenComp_bind noKemKeyGenComp_ite noKemKeyGenComp_caseOpt noKemKeyGenComp_caseSum noKemKeyGenComp_sample noKemKeyGenComp_query noKemKeyGenComp_iter noKemKeyGenComp_findM noKemKeyGenComp_anyM noKemKeyGenComp_mapM noKemKeyGenComp_consumeFirstM noKemKeyGenComp_foldM noKemKeyGenExpr_optBytes32LitE noKemKeyGenExpr_var noKemKeyGenExpr_v0 noKemKeyGenExpr_v1 noKemKeyGenExpr_v2 noKemKeyGenExpr_v3 noKemKeyGenExpr_v4 noKemKeyGenExpr_v5 noKemKeyGenExpr_v6 noKemKeyGenExpr_unit noKemKeyGenExpr_bool noKemKeyGenExpr_nat noKemKeyGenExpr_none noKemKeyGenExpr_nil noKemKeyGenExpr_add noKemKeyGenExpr_sub noKemKeyGenExpr_mulK noKemKeyGenExpr_divK noKemKeyGenExpr_modK noKemKeyGenExpr_lt noKemKeyGenExpr_eqN noKemKeyGenExpr_not noKemKeyGenExpr_and noKemKeyGenExpr_ite noKemKeyGenExpr_pair noKemKeyGenExpr_fst noKemKeyGenExpr_snd noKemKeyGenExpr_inl noKemKeyGenExpr_inr noKemKeyGenExpr_some noKemKeyGenExpr_caseOpt noKemKeyGenExpr_caseSum noKemKeyGenExpr_letE noKemKeyGenExpr_cons noKemKeyGenExpr_len noKemKeyGenExpr_take noKemKeyGenExpr_appendL noKemKeyGenExpr_findB noKemKeyGenExpr_anyB noKemKeyGenExpr_mapB noKemKeyGenExpr_foldrB noKemKeyGenExpr_tconst noKemKeyGenExpr_tget noKemKeyGenExpr_tset noKemKeyGenExpr_e2ePureOp noKemKeyGenExpr_e2eCurveOp noKemKeyGenExpr_e2eCryptoOp noKemKeyGenExpr_orE noKemKeyGenExpr_boolEq noKemKeyGenExpr_isSomeE noKemKeyGenExpr_otherE noKemKeyGenExpr_pGet noKemKeyGenExpr_sendAddrsE noKemKeyGenExpr_expectedAddrsE noKemKeyGenComp_spqrSendComp noKemKeyGenComp_spqrRecvComp noKemKeyGenExpr_drSendPostE noKemKeyGenComp_drSendC noKemKeyGenExpr_drRecvFinishE noKemKeyGenComp_drReceiveC noKemKeyGenComp_drTrArmC noKemKeyGenComp_drChArmC noKemKeyGenComp_drCrArmC drSendAtomicC_cost_exact drReceiveAtomicC_cost_exact)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInDefs (env_get_zero fst_eval snd_eval env_get_succ compCoinToPrf cost_compCoinToPrf size_compCoinToPrf queries_compCoinToPrf_zero queries_coinOnly_zero redCoinToPrf size_redCoinToPrf atomicPrfIface_liftP coinOnlyIface_liftP eval_compCoinToPrf eval_redCoinToPrf compCoinToPrf_renComp compCoinToPrf_wk1Comp compCoinToPrf_eval_eq_liftM hop2InitArgT hop2InitAliceE2EE eval_hop2InitAliceE2EE cost_hop2InitAliceE2EE size_hop2InitAliceE2EE hop2InitGsE2EE eval_hop2InitGsE2EE cost_hop2InitGsE2EE size_hop2InitGsE2EE dlPreE2EE cost_dlPreE2EE size_dlPreE2EE dlPostE2EE cost_dlPostE2EE size_dlPostE2EE ijPreE2EE cost_ijPreE2EE size_ijPreE2EE ijPostHop2E2EE cost_ijPostHop2E2EE size_ijPostHop2E2EE eval_dlPreE2EE eval_dlPostE2EE eval_ijPreE2EE eval_ijPostHop2E2EE hop2BadAtE2EE cost_hop2BadAtE2EE size_hop2BadAtE2EE eval_hop2BadAtE2EE needsDHE2EE cost_needsDHE2EE size_needsDHE2EE eval_needsDHE2EE hasSenderChainE2EE cost_hasSenderChainE2EE size_hasSenderChainE2EE eval_hasSenderChainE2EE sendHalfRealE2EE cost_sendHalfRealE2EE size_sendHalfRealE2EE eval_sendHalfRealE2EE prepHop2DHState prepHop2DHStateE2EE cost_prepHop2DHStateE2EE size_prepHop2DHStateE2EE eval_prepHop2DHStateE2EE partyReachInv_prepHop2DHState params_receive_prepHop2DHState sPureOp sSymOp sGroupOp sPtDecOp sCurveOp eval_sPureOp cost_sPureOp eval_sSymOp cost_sSymOp eval_sGroupOp cost_sGroupOp eval_sPtDecOp cost_sPtDecOp eval_sCurveOp cost_sCurveOp size_sPureOp size_sSymOp size_sGroupOp size_sPtDecOp size_sCurveOp drawBoolCoin draw256Coin drawBoolCoin_cost draw256Coin_cost drawBoolCoin_size draw256Coin_size atomicDraw256_size drawBoolCoin_eval draw256Coin_eval Hop2Mode prgCoinMode prgLiftedMode prfOracleMode hop2EntryTy hop2AuxTy hop2ChallTy hop2UpdTy hop2OutTy hop2RecvResTy hop2SendHalfResTy hop2FullStTy hop2AuxEnc hop2AuxDec hop2AuxDec_enc hop2UpdEnc hop2UpdDec hop2UpdDec_enc hop2OutEnc pSetLocal auxLazy auxMade auxIdx auxCoins auxBad auxMk auxSetBad auxConsLazy hop2LookupE hop2CommitE cost_auxSetBad cost_auxConsLazy cost_hop2LookupE cost_hop2CommitE size_auxSetBad size_auxConsLazy size_hop2LookupE size_hop2CommitE eval_hop2LookupE eval_hop2CommitE dhTargetPtAtomicE cost_dhTargetPtAtomicE size_dhTargetPtAtomicE eval_dhTargetPtAtomicE finishHop2DHAtomicC queries_finishHop2DHAtomicC cost_finishHop2DHAtomicC size_finishHop2DHAtomicC hop2FinishNoneC queries_hop2FinishNoneC cost_hop2FinishNoneC size_hop2FinishNoneC hop2LazyC queries_hop2LazyC cost_hop2LazyC size_hop2LazyC hop2SendHalfSomeC queries_hop2SendHalfSomeC cost_hop2SendHalfSomeC size_hop2SendHalfSomeC hop2DHC queries_hop2DHC cost_hop2DHC size_hop2DHC hop2RecvC queries_hop2RecvC size_hop2RecvC Hop2EvalSpec prgLiftedMode_evalSpec prfOracleMode_evalSpec compCoinToPrf_finishHop2DHAtomicC compCoinToPrf_hop2FinishNoneC compCoinToPrf_hop2LazyC compCoinToPrf_hop2SendHalfSomeC compCoinToPrf_hop2DHC compCoinToPrf_hop2RecvC Hop2AuxBounded Hop2AuxBounded.mono hop2AuxBounded_commit hop2DecryptOut finishHop2DHAtomicC_eval_and_inv hop2FinishNoneOut hop2FinishNoneC_eval_and_inv hop2LazyC_eval hop2SendHalfSomeC_eval noKemKeyGenExpr_hop2InitGsE2EE noKemKeyGenExpr_dlPreE2EE noKemKeyGenExpr_dlPostE2EE noKemKeyGenExpr_ijPreE2EE noKemKeyGenExpr_ijPostHop2E2EE noKemKeyGenExpr_hop2BadAtE2EE noKemKeyGenExpr_needsDHE2EE noKemKeyGenExpr_hasSenderChainE2EE noKemKeyGenExpr_sendHalfRealE2EE noKemKeyGenExpr_prepHop2DHStateE2EE cost_finishHop2DHAtomicC_tight cost_hop2RecvC stS stGs stAux stChall stMk hop2FullEnc eval_auxSetBad eval_auxBad smReachBounded_accept hop2DlArmC queries_hop2DlArmC size_hop2DlArmC compCoinToPrf_hop2DlArmC hop2IjArmC queries_hop2IjArmC size_hop2IjArmC compCoinToPrf_hop2IjArmC hop2StepC queries_hop2StepC size_hop2StepC compCoinToPrf_hop2StepC hop2InitBodyC hop2InitPrfC queries_hop2InitBodyC queries_hop2InitPrfC cost_hop2InitBodyC cost_hop2InitPrfC size_hop2InitBodyC size_hop2InitPrfC hop2InitImpl hop2InitBodyC_eval_and_inv hop2GameRed redCoinToPrf_hop2GameRed_prgCoinMode cost_hop2DlArmC cost_hop2IjArmC cost_hop2StepC hop2PrgRedKReal hop2PrgRedK hop2PrgRedK_totalQueries_zero hop2PrgRedK_totalCost_le hop2PrgRedK_size_raw_le hop2PrgRedK_size_le_of_clamp hop2PrgRedK_size_le hop2PrgRedK_gRedBounded_of_clamp hop2PrgRedK_gRedBounded_of_le hop2PrgRedK_gRedBounded hop2PrgRedK_gRedBounded_succ hop2PrgRedK_gRedBounded_tier1 hop2PrfRedKReal hop2PrfRedK hop2PrfRedK_totalQueries_le hop2PrfRedK_totalCost_le hop2PrfRedK_size_raw_le hop2PrfRedK_size_le_of_clamp hop2PrfRedK_size_le hop2PrfRedK_gRedBounded_of_clamp hop2PrfRedK_gRedBounded_of_le hop2PrfRedK_gRedBounded hop2PrfRedK_gRedBounded_succ hop2PrfRedK_gRedBounded_tier1)

section Hop2AtomicOps

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

theorem hop2DHC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (chall : BitVec 256 × BitVec 256) (aux : Hop2Aux Pt)
    (t : ℕ) (coins : BitVec 256) (g : GhostState Bytes)
    (c : Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (hchallE : challE.eval ρ = chall)
    (hauxE : auxE.eval ρ = hop2AuxEnc (ℓ := ℓ) aux)
    (htE : tE.eval ρ = t) (hcoinsE : coinsE.eval ρ = coins)
    (hgE : gE.eval ρ = g) (hsrkE : srkE.eval ρ = msg.senderRatchetKey)
    (hcE : cE.eval ρ = c) (hrcE : rcE.eval ρ = rc)
    (hg : PartyReachInv C K g)
    (hlazy : aux.lazy.length ≤ q) (hmade : aux.made.length ≤ q + 1)
    (htry : SignalMessage.tryFrom protoSignalCodec c = .ok msg)
    (hnone : (g.session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2DHC M q k challE auxE tE coinsE gE srkE cE rcE).eval ρ =
      ((fun r : Hop2Out Pt ℓ × (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
          (hop2OutEnc (ℓ := ℓ) r.1, hop2AuxEnc (ℓ := ℓ) r.2.2)) <$>
        (hop2DH P Dh encT decT hyb (some t) coins g msg rc).run (gs, aux)) ∧
    (∀ r ∈ support ((hop2DH P Dh encT decT hyb (some t) coins g msg rc).run (gs, aux)),
      r.2.1 = gs ∧ r.2.2.lazy.length ≤ aux.lazy.length + 1 ∧ r.2.2.made = aux.made ∧
      (∀ st' t' i' m' uOpt, r.1 = some ((st', t', i', m'), uOpt) → PartyReachInv C K st')) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  have hPC : P.C = C := rfl
  have hdt : (dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) srkE).eval ρ =
      match decT msg.senderRatchetKey with
      | none => none
      | some T => if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none else some T := by
    rw [eval_dhTargetPtAtomicE, hsrkE]
    cases decT msg.senderRatchetKey <;> simp
  have hscB :
      (Expr.letE gE
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
              (encT := encT))))).eval ρ = g.session.senderChain.isSome := by
    rw [letE_eval, wk1Expr_eval, hgE]
    have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
      (.cons g .nil)
    have he := eval_hasSenderChainE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) g hg.receiverChains_le
    change (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))).eval
        (liftEnv (Pt := Pt) (.cons g .nil)) = _
    rw [hl, he]; rfl
  have hdecM_run : ∀ (sc : SenderChain) (rk2 ckR ckS : BitVec 256) (upd : Hop2Upd Pt)
        (aux' : Hop2Aux Pt),
      (let sess' : SessionState Bytes :=
        { g.session with
          previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
          rootKey := rk2
          receiverChains := RatchetState.evictReceiverChains
            (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
          senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ }
       match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
           rc sess' with
       | (.error _, _) => return (none : Hop2Out Pt ℓ)
       | (.ok m, s_out) =>
         let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
           ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
         return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
           g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some upd) : Hop2M Pt ℓ _).run
        (gs, aux') =
      pure (hop2DecryptOut P g sc msg rc rk2 ckR ckS upd, (gs, aux')) := by
    intro sc rk2 ckR ckS upd aux'
    dsimp only [hop2DecryptOut, prepHop2DHState]
    cases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc _ with
    | mk res s_out => cases res <;> simp [StateT.run_pure]
  have htail_none : ∀ (sc : SenderChain) (rkM ckR : BitVec 256) (aux' : Hop2Aux Pt) (T : Pt),
      (do
        let newKey := KeyPair.generate P.C rc
        match ← StateT.lift (hop2SendHalf P hyb none rkM msg.senderRatchetKey newKey.privateKey
            (Dh.dh rc T)) with
        | none => return (none : Hop2Out Pt ℓ)
        | some (idx2, rk2, ckS, pend) =>
          let sess' : SessionState Bytes :=
            { g.session with
              previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
              rootKey := rk2
              receiverChains := RatchetState.evictReceiverChains
                (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
              senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
          match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              rc sess' with
          | (.error _, _) => return none
          | (.ok m, s_out) =>
            let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
              ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
            return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
              g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m),
              some ⟨idx2, rc, pend⟩) : Hop2M Pt ℓ _).run
          (gs, aux') =
      pure (hop2FinishNoneOut P g sc msg rc rkM ckR, (gs, aux')) := by
    intro sc rkM ckR aux' T
    dsimp only [hop2SendHalf, hop2FinishNoneOut]
    cases rootCreateChain P.C rkM msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
    | error _ => simp [StateT.run_bind, StateT.run_lift, StateT.run_pure]
    | ok pair =>
      rcases pair with ⟨rk', ck⟩
      rw [StateT.run_bind, StateT.run_lift, pure_bind]
      exact hdecM_run sc rk' ckR ck.key ⟨none, rc, none⟩ aux'
  set dtVal : Option Pt :=
    match decT msg.senderRatchetKey with
    | none => none
    | some T => if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none else some T
  let t0 : Ty ASig :=
    .prod (.opt PtT)
      (.prod .bool
        (.prod (hop2ChallTy ℓ Pt)
          (.prod (hop2AuxTy ℓ Pt)
            (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  let v0Val : t0.denote :=
    (dtVal, (g.session.senderChain.isSome,
      (chall, (hop2AuxEnc (ℓ := ℓ) aux, (t, (coins, (g, (msg.senderRatchetKey, (c, rc)))))))))
  unfold hop2DHC hop2DH
  rw [comp_eval_bind_ret]
  have houter :
      (Expr.pair (dhTargetPtAtomicE srkE)
        (.pair
          (Expr.letE gE
            (wk1Expr
              (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)))))
          (.pair challE
            (.pair auxE (.pair tE (.pair coinsE (.pair gE (.pair srkE (.pair cE rcE))))))))).eval ρ =
      v0Val :=
    Prod.ext hdt (Prod.ext hscB (Prod.ext hchallE (Prod.ext hauxE
      (Prod.ext htE (Prod.ext hcoinsE (Prod.ext hgE (Prod.ext hsrkE (Prod.ext hcE hrcE))))))))
  rw [houter, comp_eval_caseOpt]
  have hscrut0 : (Expr.fst (Expr.v0 (O := AOps))).eval (.cons v0Val ρ) = dtVal := rfl
  rw [hscrut0]
  dsimp only [dtVal]
  cases hdec : decT msg.senderRatchetKey with
  | none =>
    refine ⟨?_, ?_⟩
    · simp only [comp_eval_ret, StateT.run_pure]; rfl
    · intro r hr; simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
  | some T =>
    dsimp only
    by_cases hbad : T = 0 ∨ encT T ≠ msg.senderRatchetKey
    · refine ⟨?_, ?_⟩
      · simp only [hbad, ↓reduceIte, comp_eval_ret, StateT.run_pure]; rfl
      · intro r hr
        simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
    · simp only [hbad, ↓reduceIte]
      have hv0 : v0Val = (some T, (g.session.senderChain.isSome,
          (chall, (hop2AuxEnc (ℓ := ℓ) aux,
            (t, (coins, (g, (msg.senderRatchetKey, (c, rc))))))))) := by
        simp [v0Val, dtVal, hdec, hbad]
      rw [hv0]
      let ρT : Env ([PtT, t0] ++ Γ) :=
        .cons T (.cons (some T, (g.session.senderChain.isSome,
          (chall, (hop2AuxEnc (ℓ := ℓ) aux, (t, (coins, (g, (msg.senderRatchetKey, (c, rc))))))))) ρ)
      change (Comp.ite _ _ _).eval ρT = _ ∧ _
      rw [comp_eval_ite]
      have hscCond : (Expr.fst (.snd (Expr.v1 (O := AOps)))).eval ρT =
          g.session.senderChain.isSome := rfl
      rw [hscCond]
      cases hsc : g.session.senderChain with
      | none =>
        refine ⟨?_, ?_⟩
        · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            comp_eval_ret, StateT.run_pure]
          rfl
        · intro r hr
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
      | some sc =>
        simp only [Option.isSome_some, ↓reduceIte]
        set Q := Dh.dh coins T
        rw [comp_eval_ite]
        have hQ0_eval :
            (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .ptIsZero
              (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))).eval ρT =
            decide (Q = 0) := rfl
        rw [hQ0_eval]
        dsimp only [hop2RecvHalf]
        by_cases hQ0 : Q = 0
        · refine ⟨?_, ?_⟩
          · simp [hQ0, comp_eval_ret, StateT.run_pure,
              Expr.eval, Expr.v1, ρT, hop2OutEnc]
          · intro r hr
            simp only [hQ0, ↓reduceIte, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
        · simp only [hQ0, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [comp_eval_ite]
          have htk_eval : (Expr.lt (.fst (.snd (.snd (.snd (.snd (Expr.v1 (O := AOps)))))))
              (.nat (k + 1))).eval ρT = decide (t ≤ k) := by
            change decide (t < k + 1) = decide (t ≤ k)
            exact decide_eq_decide.mpr Nat.lt_succ_iff
          rw [htk_eval]
          have hhybk : hyb.k = k := rfl
          rw [hhybk]
          by_cases htk : t ≤ k
          · simp only [htk, decide_true, ↓reduceIte]
            have hlkMade :
                (hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) (q + 1)
                  (auxMade (.fst (.snd (.snd (.snd .v1)))))
                  (.fst (.snd (.snd (.snd (.snd .v1)))))
                  (sGroupOp .ptDh
                    (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))).eval ρT =
                aux.made.lookup (t, Q) :=
              eval_hop2LookupE (q + 1) _ _ _ ρT aux.made t Q hmade rfl rfl rfl
            rw [comp_eval_caseOpt, hlkMade]
            have hgetMade : (get : Hop2M Pt ℓ _).run (gs, aux) = pure ((gs, aux), (gs, aux)) := rfl
            cases hmadeLk : aux.made.lookup (t, Q) with
            | none =>
              have hlz := hop2LazyC_eval M hM q
                (.fst (.snd (.snd (.snd .v1))))
                (.fst (.snd (.snd (.snd (.snd .v1)))))
                (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))
                ρT gs aux t Q hlazy rfl rfl rfl
              rw [comp_eval_bind, hlz.1]
              let rhsM : Hop2M Pt ℓ (Hop2Out Pt ℓ) := do
                let rOpt ← (do
                  match (← get).2.made.lookup (t, Dh.dh coins T) with
                  | some ck => return some (some (t + 1), (0 : BitVec 256), ck)
                  | none =>
                    let u ← hop2Lazy t (Dh.dh coins T)
                    let (rk', ck) := rootExpand P.C.F (keyToBytes32 u)
                    return some (none, rk', ck) : Hop2M Pt ℓ _)
                match rOpt with
                | none => return (none : Hop2Out Pt ℓ)
                | some (idx1, rkM, ckR) =>
                  let newKey := KeyPair.generate P.C rc
                  match ← StateT.lift (hop2SendHalf P hyb idx1 rkM msg.senderRatchetKey
                      newKey.privateKey (Dh.dh rc T)) with
                  | none => return none
                  | some (idx2, rk2, ckS, pend) =>
                    let sess' : SessionState Bytes :=
                      { g.session with
                        previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                        rootKey := rk2
                        receiverChains := RatchetState.evictReceiverChains
                          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                        senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
                    match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                        rc sess' with
                    | (.error _, _) => return none
                    | (.ok m, s_out) =>
                      let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
                        ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
                      return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
                        g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨idx2, rc, pend⟩)
              have hrhs_none :
                  rhsM.run (gs, aux) =
                  ((hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run (gs, aux) >>= fun r =>
                    let (rk', ck) := rootExpand P.C.F (keyToBytes32 r.1)
                    pure (hop2FinishNoneOut P g sc msg rc rk' ck, (r.2.1, r.2.2))) := by
                dsimp only [rhsM]
                rw [StateT.run_bind, StateT.run_bind, hgetMade, pure_bind]
                dsimp only
                rw [show Dh.dh coins T = Q from rfl, hmadeLk, StateT.run_bind, bind_assoc]
                refine bind_congr_of_mem_support' ((hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run (gs, aux)) ?_
                intro ⟨u, gs1, aux1⟩ hr
                have hgs1 : gs1 = gs := (hlz.2 _ hr).1
                subst hgs1
                rw [StateT.run_pure, pure_bind]
                exact htail_none sc _ _ aux1 T
              change _ = _ <$> rhsM.run (gs, aux) ∧ ∀ r ∈ support (rhsM.run (gs, aux)), _
              rw [hrhs_none]
              refine ⟨?_, ?_⟩
              · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
                refine bind_congr fun ⟨u, gs1, aux1⟩ => ?_
                rw [comp_eval_bind_ret]
                let ρLz := Env.cons (t := .prod BV256 BV256)
                  ((expandPRG C.F).gen u)
                  (Env.cons (t := .prod BV256 (hop2AuxTy ℓ Pt))
                    (u, hop2AuxEnc (ℓ := ℓ) aux1) ρT)
                have hfn := hop2FinishNoneC_eval_and_inv M hM
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                  (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                  (.fst .v0) (.snd .v0) (.snd .v1)
                  ρLz idA idB g sc c msg rc
                  ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 aux1
                  rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
                exact hfn.1
              · intro r hr
                rw [mem_support_bind_iff] at hr
                obtain ⟨⟨u, gs1, aux1⟩, hlz_mem, hr⟩ := hr
                rw [support_pure, Set.mem_singleton_iff] at hr
                subst hr
                obtain ⟨hgs1, hlazy1, hmade1⟩ := hlz.2 _ hlz_mem
                refine ⟨hgs1, hlazy1, hmade1, ?_⟩
                intro st' t' i' m' uOpt hout
                let ρLz := Env.cons (t := .prod BV256 BV256)
                  ((expandPRG C.F).gen u)
                  (Env.cons (t := .prod BV256 (hop2AuxTy ℓ Pt))
                    (u, hop2AuxEnc (ℓ := ℓ) aux1) ρT)
                exact (hop2FinishNoneC_eval_and_inv M hM
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                  (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                  (.fst .v0) (.snd .v0) (.snd .v1)
                  ρLz idA idB g sc c msg rc
                  ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 aux1
                  rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone).2 st' t' i' m' uOpt hout
            | some ckR =>
              let ρCk : Env ([BV256, PtT, t0] ++ Γ) := .cons ckR ρT
              have hsh := hop2SendHalfSomeC_eval M hM k
                (.fst (.snd (.snd .v2)))
                (.add (.fst (.snd (.snd (.snd (.snd .v2))))) (.nat 1))
                (sGroupOp .ptDh
                  (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))))) .v1))
                ρCk P hPC chall (t + 1) (Dh.dh rc T) msg.senderRatchetKey
                (KeyPair.generate P.C rc).privateKey rfl rfl rfl
              dsimp only
              rw [comp_eval_bind, hsh]
              let rhsM : Hop2M Pt ℓ (Hop2Out Pt ℓ) := do
                let rOpt ← (do
                  match (← get).2.made.lookup (t, Dh.dh coins T) with
                  | some ck => return some (some (t + 1), (0 : BitVec 256), ck)
                  | none =>
                    let u ← hop2Lazy t (Dh.dh coins T)
                    let (rk', ck) := rootExpand P.C.F (keyToBytes32 u)
                    return some (none, rk', ck) : Hop2M Pt ℓ _)
                match rOpt with
                | none => return (none : Hop2Out Pt ℓ)
                | some (idx1, rkM, ckR) =>
                  let newKey := KeyPair.generate P.C rc
                  match ← StateT.lift (hop2SendHalf P hyb idx1 rkM msg.senderRatchetKey
                      newKey.privateKey (Dh.dh rc T)) with
                  | none => return none
                  | some (idx2, rk2, ckS, pend) =>
                    let sess' : SessionState Bytes :=
                      { g.session with
                        previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                        rootKey := rk2
                        receiverChains := RatchetState.evictReceiverChains
                          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                        senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
                    match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                        rc sess' with
                    | (.error _, _) => return none
                    | (.ok m, s_out) =>
                      let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
                        ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
                      return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
                        g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨idx2, rc, pend⟩)
              have hrhs_some :
                  rhsM.run (gs, aux) =
                  (hop2SendHalf P hyb (some (t + 1)) 0 msg.senderRatchetKey
                    (KeyPair.generate P.C rc).privateKey (Dh.dh rc T) >>= fun shOpt =>
                    match shOpt with
                    | none => pure (none, (gs, aux))
                    | some (idx2, rk2, ckS, pend) =>
                      pure (hop2DecryptOut P g sc msg rc rk2 ckR ckS ⟨idx2, rc, pend⟩,
                        (gs, aux))) := by
                dsimp only [rhsM]
                rw [StateT.run_bind, StateT.run_bind, hgetMade, pure_bind]
                dsimp only
                rw [show Dh.dh coins T = Q from rfl, hmadeLk, StateT.run_pure, pure_bind,
                  StateT.run_bind, StateT.run_lift, bind_assoc]
                refine bind_congr fun shOpt => ?_
                rcases shOpt with _ | ⟨idx2, rk2, ckS, pend⟩
                · simp [StateT.run_pure]
                · exact hdecM_run sc rk2 ckR ckS ⟨idx2, rc, pend⟩ aux
              change _ = _ <$> rhsM.run (gs, aux) ∧ ∀ r ∈ support (rhsM.run (gs, aux)), _
              rw [hrhs_some]
              refine ⟨?_, ?_⟩
              · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
                refine bind_congr fun shOpt => ?_
                rw [comp_eval_caseOpt]
                rcases shOpt with _ | ⟨idx2, rk2, ckS, pend⟩
                · simp [comp_eval_ret, Expr.eval, Expr.v0, Expr.v3, ρT, hop2OutEnc]
                · dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]; dsimp only
                  let tShInner : Ty ASig :=
                    .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
                  let ρSh : Env ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) :=
                    .cons (idx2, (rk2, (ckS, pend)))
                      (.cons (some (idx2, (rk2, (ckS, pend)))) ρCk)
                  have hfd := finishHop2DHAtomicC_eval_and_inv M hM
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))))
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                    (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))
                    (.pair (.fst .v0)
                      (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                        (.snd (.snd (.snd .v0)))))
                    ρSh idA idB g sc c msg rc rk2 ckR ckS ⟨idx2, rc, pend⟩
                    rfl rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
                  rw [comp_eval_bind]; erw [hfd.1]; rw [pure_bind]
                  simp [comp_eval_ret, Expr.eval, Expr.v5, ρT]; rfl
              · intro r hr
                rw [mem_support_bind_iff] at hr
                obtain ⟨shOpt, -, hr⟩ := hr
                rcases shOpt with _ | ⟨idx2, rk2, ckS, pend⟩
                · rw [support_pure, Set.mem_singleton_iff] at hr
                  subst hr
                  exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
                · rw [support_pure, Set.mem_singleton_iff] at hr
                  subst hr
                  refine ⟨rfl, Nat.le_succ _, rfl, ?_⟩
                  intro st' t' i' m' uOpt hout
                  let tShInner : Ty ASig :=
                    .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
                  let ρSh : Env ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) :=
                    .cons (idx2, (rk2, (ckS, pend)))
                      (.cons (some (idx2, (rk2, (ckS, pend)))) ρCk)
                  exact (finishHop2DHAtomicC_eval_and_inv M hM
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))))
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                    (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))
                    (.pair (.fst .v0)
                      (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                        (.snd (.snd (.snd .v0)))))
                    ρSh idA idB g sc c msg rc rk2 ckR ckS ⟨idx2, rc, pend⟩
                    rfl rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone).2
                    st' t' i' m' uOpt hout
          · simp only [htk, decide_false, Bool.false_eq_true, ↓reduceIte]
            have hstep := hM.stepC_eval
              (.fst (.fst (.snd (.snd .v1))))
              (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0)) ρT
            have hc1 : (Expr.fst (.fst (.snd (.snd (Expr.v1 (O := AOps)))))).eval ρT = chall.1 := rfl
            have hq1 : (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                (decT := decT) (lam := lam) .ptDh
                (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0)).eval ρT = Q := rfl
            rw [hc1, hq1] at hstep
            rw [comp_eval_bind, hstep]
            let rhsM : Hop2M Pt ℓ (Hop2Out Pt ℓ) := do
              let rOpt ← (do
                let u ← StateT.lift (hyb.step (Dh.dh coins T))
                let (rk', ck) := rootExpand P.C.F (keyToBytes32 u)
                return some (none, rk', ck) : Hop2M Pt ℓ _)
              match rOpt with
              | none => return (none : Hop2Out Pt ℓ)
              | some (idx1, rkM, ckR) =>
                let newKey := KeyPair.generate P.C rc
                match ← StateT.lift (hop2SendHalf P hyb idx1 rkM msg.senderRatchetKey
                    newKey.privateKey (Dh.dh rc T)) with
                | none => return none
                | some (idx2, rk2, ckS, pend) =>
                  let sess' : SessionState Bytes :=
                    { g.session with
                      previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                      rootKey := rk2
                      receiverChains := RatchetState.evictReceiverChains
                        (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                      senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
                  match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                      rc sess' with
                  | (.error _, _) => return none
                  | (.ok m, s_out) =>
                    let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
                      ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
                    return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
                      g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨idx2, rc, pend⟩)
            have hrhs_gt :
                rhsM.run (gs, aux) =
                (stepOf chall.1 Q >>= fun u =>
                  let (rk', ck) := rootExpand P.C.F (keyToBytes32 u)
                  pure (hop2FinishNoneOut P g sc msg rc rk' ck, (gs, aux))) := by
              dsimp only [rhsM]
              rw [StateT.run_bind, StateT.run_bind, StateT.run_lift]
              simp only [bind_assoc, pure_bind]
              refine bind_congr fun u => ?_
              rw [StateT.run_pure, pure_bind]
              exact htail_none sc _ _ aux T
            change _ = _ <$> rhsM.run (gs, aux) ∧ ∀ r ∈ support (rhsM.run (gs, aux)), _
            rw [hrhs_gt]
            refine ⟨?_, ?_⟩
            · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
              refine bind_congr fun u => ?_
              rw [comp_eval_bind_ret]
              let ρSt := Env.cons (t := .prod BV256 BV256)
                ((expandPRG C.F).gen u)
                (Env.cons (t := BV256) u ρT)
              have hfn := hop2FinishNoneC_eval_and_inv M hM
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.fst .v0) (.snd .v0) (.fst (.snd (.snd (.snd .v3))))
                ρSt idA idB g sc c msg rc
                ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 aux
                rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
              exact hfn.1
            · intro r hr
              rw [mem_support_bind_iff] at hr
              obtain ⟨u, -, hr⟩ := hr
              rw [support_pure, Set.mem_singleton_iff] at hr
              subst hr
              refine ⟨rfl, Nat.le_succ _, rfl, ?_⟩
              intro st' t' i' m' uOpt hout
              let ρSt := Env.cons (t := .prod BV256 BV256)
                ((expandPRG C.F).gen u)
                (Env.cons (t := BV256) u ρT)
              exact (hop2FinishNoneC_eval_and_inv M hM
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.fst .v0) (.snd .v0) (.fst (.snd (.snd (.snd .v3))))
                ρSt idA idB g sc c msg rc
                ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 aux
                rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone).2 st' t' i' m' uOpt hout

theorem hop2RecvC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (chall : BitVec 256 × BitVec 256) (aux : Hop2Aux Pt)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (hchallE : challE.eval ρ = chall)
    (hauxE : auxE.eval ρ = hop2AuxEnc (ℓ := ℓ) aux)
    (hgE : gE.eval ρ = g) (hcE : cE.eval ρ = c) (hrcE : rcE.eval ρ = rc)
    (hg : PartyReachInv C K g)
    (hlazy : aux.lazy.length ≤ q) (hmade : aux.made.length ≤ q + 1) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2RecvC M q k challE auxE gE cE rcE).eval ρ =
      ((fun r : Hop2Out Pt ℓ × (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
          (hop2OutEnc (ℓ := ℓ) r.1, hop2AuxEnc (ℓ := ℓ) r.2.2)) <$>
        (hop2Recv P Dh encT decT hyb g c rc).run (gs, aux)) ∧
    (∀ r ∈ support ((hop2Recv P Dh encT decT hyb g c rc).run (gs, aux)),
      r.2.1 = gs ∧ r.2.2.lazy.length ≤ aux.lazy.length + 1 ∧ r.2.2.made = aux.made ∧
      (∀ st' t' i' m' uOpt, r.1 = some ((st', t', i', m'), uOpt) → PartyReachInv C K st')) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  have hrealRecv : ∀ {Δ : List (Ty ASig)}
      (g1 : Expr AOps Δ GhostStT) (c1 : Expr AOps Δ (B 32)) (rc1 : Expr AOps Δ BV256)
      (aux1 : Expr AOps Δ (hop2AuxTy ℓ Pt)) (ρ' : Env Δ)
      (hg1 : g1.eval ρ' = g) (hc1 : c1.eval ρ' = c) (hrc1 : rc1.eval ρ' = rc)
      (haux1 : aux1.eval ρ' = hop2AuxEnc (ℓ := ℓ) aux),
      (Comp.bind (.ret (.pair aux1 .unit))
        (.bind
          (M.embedCoin
            (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
              (.pair (renExpr Var.succ g1) (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1)))))
          (.caseOpt .v0
            (.ret (.pair .none (.fst .v1)))
            (.ret (.pair (.some (.pair .v0 .none)) (.fst .v2)))))).eval ρ' =
      pure (hop2OutEnc (ℓ := ℓ) (((sessionSchemeU P ℓ).receive g c rc).map fun r => (r, none)),
        hop2AuxEnc (ℓ := ℓ) aux) := by
    intro Δ g1 c1 rc1 aux1 ρ' hg1 hc1 hrc1 haux1
    rw [comp_eval_bind_ret]
    let ρ'1 : Env ([.prod (hop2AuxTy ℓ Pt) .unit] ++ Δ) :=
      .cons (hop2AuxEnc (ℓ := ℓ) aux, ()) ρ'
    have hp' : (Expr.pair aux1 .unit).eval ρ' = (hop2AuxEnc (ℓ := ℓ) aux, ()) := by
      simp [Expr.eval, haux1]
    rw [hp', comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM]
    have hdrArg : (Expr.pair (renExpr Var.succ g1)
        (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1))).eval ρ'1 = (g, (c, rc)) := by
      have hpComp :
          ∀ {Δ₁ Δ₂ : List (Ty ASig)} {u0 : Ty ASig}
            (f : ∀ {t}, Var Δ₁ t → Var Δ₂ t) (x : u0.denote) (ρ0 : Env Δ₂),
            AtomicSessionBridge.pullEnv (fun {_} v => Var.succ (f v)) (.cons x ρ0) =
              AtomicSessionBridge.pullEnv f ρ0 := by
        intro Δ₁ Δ₂ u0 f x ρ0
        induction Δ₁ with
        | nil => rfl
        | cons _ _ ih => exact congrArg (Env.cons _) (ih (fun v => f (.succ v)))
      have hpId : ∀ {Δ0 : List (Ty ASig)} (ρ0 : Env Δ0),
          AtomicSessionBridge.pullEnv (fun {_} v => v) ρ0 = ρ0 := by
        intro Δ0 ρ0
        induction ρ0 with
        | nil => rfl
        | cons y ρ0 ih => exact congrArg (Env.cons y) ((hpComp (fun v => v) y ρ0).trans ih)
      have hpEnv :
          AtomicSessionBridge.pullEnv (fun {_} => Var.succ) ρ'1 = ρ' :=
        (hpComp (fun v => v) _ ρ').trans (hpId ρ')
      simp [Expr.eval, renExpr_eval, hpEnv, hg1, hc1, hrc1]
    have hdr := drReceiveAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
      (.pair (renExpr Var.succ g1) (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1)))
      ρ'1 idA idB (by rw [hdrArg]; exact hg)
    rw [hdrArg] at hdr
    rw [hdr, ← liftComp_eq_liftM, liftComp_pure, pure_bind]
    dsimp only [sessionSchemeU]
    cases hpr : P.receive g c rc with
    | none => rfl
    | some quad => rcases quad with ⟨st', t', i', ptBytes⟩; rfl
  have hrealInv : ∀ r ∈ support ((pure (((sessionSchemeU P ℓ).receive g c rc).map fun x =>
      (x, (none : Option (Hop2Upd Pt)))) : Hop2M Pt ℓ _).run (gs, aux)),
      r.2.1 = gs ∧ r.2.2.lazy.length ≤ aux.lazy.length + 1 ∧ r.2.2.made = aux.made ∧
      (∀ st' t' i' m' uOpt, r.1 = some ((st', t', i', m'), uOpt) → PartyReachInv C K st') := by
    intro r hr
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    refine ⟨rfl, Nat.le_succ _, rfl, ?_⟩
    intro st' t' i' m' uOpt hout
    dsimp only [sessionSchemeU] at hout
    cases hpr : P.receive g c rc with
    | none => rw [hpr] at hout; simp at hout
    | some quad =>
      rcases quad with ⟨st0, t0, i0, pt0⟩
      rw [hpr, Option.map_some, Option.map_some] at hout
      injection hout with hpair
      have hst_eq : st0 = st' := (Prod.mk.inj (Prod.mk.inj hpair).1).1
      subst hst_eq
      exact partyReachInv_receive C K rfl rfl hg hpr
  unfold hop2RecvC hop2Recv
  rw [comp_eval_bind_ret]
  let t0 : Ty ASig :=
    .prod (hop2ChallTy ℓ Pt) (.prod (hop2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  let ρ0 : Env ([t0] ++ Γ) :=
    .cons (chall, (hop2AuxEnc (ℓ := ℓ) aux, (g, (c, rc)))) ρ
  have hp0 : (Expr.pair challE (.pair auxE (.pair gE (.pair cE rcE)))).eval ρ =
      (chall, (hop2AuxEnc (ℓ := ℓ) aux, (g, (c, rc)))) := by
    simp [Expr.eval, hchallE, hauxE, hgE, hcE, hrcE]
  rw [hp0, comp_eval_caseOpt]
  have hcodec : P.codec = protoSignalCodec := rfl
  rw [hcodec]
  have hparse : (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .signalMsgParse (.fst (.snd (.snd (.snd .v0))))).eval ρ0 =
      match SignalMessage.tryFrom protoSignalCodec c with
      | .ok m =>
        some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
              (m.ciphertext.take c.length,
               (m.pqRatchet.take c.length, m.addresses.map (·.take c.length))))
      | .error _ => none := rfl
  rw [hparse]
  cases htry : SignalMessage.tryFrom protoSignalCodec c with
  | error _ =>
    refine ⟨?_, ?_⟩
    · simp only [comp_eval_ret, StateT.run_pure]; rfl
    · intro r hr
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
  | ok msg =>
    dsimp only
    let parsedVal : (ReductionDsl.signalParsedT (ℓ := ℓ) (Pt := Pt)).denote :=
      ((msg.messageVersion, (msg.senderRatchetKey, (msg.counter, msg.previousCounter))),
       (msg.ciphertext.take c.length,
        (msg.pqRatchet.take c.length, msg.addresses.map (·.take c.length))))
    let ρ1 : Env ([ReductionDsl.signalParsedT, t0] ++ Γ) := .cons parsedVal ρ0
    have hpGetIdx :
        (pGet (auxIdx (.fst (.snd (Expr.v1 (O := AOps)))))
          (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v1)))))).eval ρ1 =
        aux.idx g.party := by
      have hpB : (Expr.fst (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .ghostStateSplit (.fst (.snd (.snd .v1))))).eval ρ1 =
          partyEnc g.party := by
        change ReductionDsl.partyToBool g.party = partyEnc g.party
        cases g.party <;> rfl
      rw [pGet_eval _ _ ρ1 aux.idx g.party rfl hpB]
    rw [comp_eval_caseOpt, hpGetIdx]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only
    cases hidx : aux.idx g.party with
    | none =>
      refine ⟨?_, hrealInv⟩
      rw [hrealRecv _ _ _ _ ρ1 rfl rfl rfl rfl, StateT.run_pure, map_pure]
    | some t =>
      dsimp only
      let ρ2 : Env ([.nat, ReductionDsl.signalParsedT, t0] ++ Γ) := .cons t ρ1
      have hneeds :
          (Expr.letE (.pair (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1))))
            (wk1Expr
              (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                  (encT := encT))))).eval ρ2 =
          (g.session.receiverChains.findIdx?
            (·.senderRatchetKey == msg.senderRatchetKey)).isNone := by
        rw [letE_eval, wk1Expr_eval]
        have harg : (Expr.pair (.fst (.snd (.snd (Expr.v2 (O := AOps)))))
            (.fst (.snd (.fst .v1)))).eval ρ2 = (g, msg.senderRatchetKey) := rfl
        rw [harg]
        have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
          (.cons (g, msg.senderRatchetKey) .nil)
        have he := eval_needsDHE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
          (decT := decT) (encT := encT) g msg.senderRatchetKey hg.receiverChains_le
        change (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))).eval
            (liftEnv (Pt := Pt) (.cons (g, msg.senderRatchetKey) .nil)) = _
        rw [hl, he]; rfl
      rw [comp_eval_ite, hneeds]
      by_cases hnone : (g.session.receiverChains.findIdx?
          (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true
      · simp only [hnone, ↓reduceIte]
        have hpCoins :
            (pGet (auxCoins (.fst (.snd (Expr.v2 (O := AOps)))))
              (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2)))))).eval ρ2 =
            aux.coins g.party := by
          have hpB : (Expr.fst (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .ghostStateSplit (.fst (.snd (.snd .v2))))).eval ρ2 =
              partyEnc g.party := by
            change ReductionDsl.partyToBool g.party = partyEnc g.party
            cases g.party <;> rfl
          rw [pGet_eval _ _ ρ2 aux.coins g.party rfl hpB]
        exact hop2DHC_eval_and_inv M hM q k
          (.fst .v2) (.fst (.snd .v2)) .v0
          (pGet (auxCoins (.fst (.snd .v2)))
            (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2))))))
          (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1)))
          (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
          ρ2 idA idB gs chall aux t (aux.coins g.party) g c msg rc
          rfl rfl rfl hpCoins rfl rfl rfl rfl hg hlazy hmade htry hnone
      · simp only [hnone, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, hrealInv⟩
        rw [hrealRecv _ _ _ _ ρ2 rfl rfl rfl rfl, StateT.run_pure, map_pure]

end Hop2AtomicOps

section Hop2Reductions

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT


theorem hop2DlArmC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qRem k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (party : Party) (c : Bytes)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st)
    (hAuxQ : Hop2AuxBounded q aux) (hAuxRem : Hop2AuxBounded qRem aux) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2DlArmC C K Dh encPt encT decT lam M q k).eval
      (.cons (hop2FullEnc s chall (st, aux), (partyEnc party, c)) .nil) =
      (fun out : Option (RecvResult (Plain ℓ)) ×
            (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (none, (out.1.map recvResultEnc, none)),
         hop2FullEnc s chall out.2)) <$>
        (hop2Deliver P Dh encT decT s hyb (party, c)).run (st, aux) ∧
    (∀ r ∈ support ((hop2Deliver P Dh encT decT s hyb (party, c)).run (st, aux)),
      SmReachBounded C K (qRem + 1) r.2.1 ∧ Hop2AuxBounded (qRem + 1) r.2.2) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let ρ₀ : Env [t0] :=
    .cons (hop2FullEnc s chall (st, aux), (partyEnc party, c)) .nil
  unfold hop2DlArmC hop2Deliver
  have hpreL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
    (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)
  have hpreE := eval_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
    st party c hQ.lists.trans_le
  rw [comp_eval_caseSum]
  have hpreStep :
      (Expr.letE (O := AOps) (.pair (stGs C K Dh encPt encT decT lam (.fst .v0)) (.snd .v0))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))).eval ρ₀ =
      liftVal (Pt := Pt)
        ((dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
          (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)) := by
    rw [letE_eval, wk1Expr_eval]; exact hpreL
  rw [hpreStep, hpreE, StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  by_cases hwin : st.win
  · simp only [hwin, ↓reduceIte]
    dsimp only [liftVal]
    rw [comp_eval_ret, StateT.run_pure, map_pure]
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hRem.mono (Nat.le_succ qRem), hAuxRem.mono (Nat.le_succ qRem)⟩
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    cases htr : st.inTransit party.other c with
    | none =>
      dsimp only [liftVal]
      rw [comp_eval_ret, StateT.run_pure, map_pure]
      refine ⟨rfl, fun r hr => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨hRem.mono (Nat.le_succ qRem), hAuxRem.mono (Nat.le_succ qRem)⟩
    | some rec_ =>
      dsimp only [liftVal]
      rw [StateT.run_bind, StateT.run_lift, bind_assoc]
      let tInr : Ty ASig := .prod GhostStT (liftTy (Pt := Pt) posTy)
      let ρ₁ : Env [tInr, t0] :=
        .cons (st.st party, liftVal (Pt := Pt) (posEnc rec_.pos)) ρ₀
      have hunif :
          (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256)) =
          hop2Unif (Pt := Pt) := rfl
      refine ⟨?_, ?_⟩
      · rw [map_eq_bind_pure_comp]
        simp only [Function.comp_def, bind_assoc]
        rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, hunif]
        refine bind_congr fun rc => ?_
        let ρ₂ : Env [BV256, tInr, t0] := .cons rc ρ₁
        have hrecv := hop2RecvC_eval_and_inv M hM q k
          (stChall C K Dh encPt encT decT lam (.fst .v2))
          (stAux C K Dh encPt encT decT lam (.fst .v2))
          (.fst .v1) (.snd (.snd .v2)) .v0
          ρ₂ idA idB st chall aux (st.st party) c rc
          rfl rfl rfl rfl rfl (hQ.reach.party party) hAuxQ.1 hAuxQ.2
        rw [comp_eval_bind, pure_bind, StateT.run_bind, bind_assoc]
        dsimp only; erw [hrecv.1]; rw [bind_map_left]
        refine bind_congr_of_mem_support'
          ((hop2Recv P Dh encT decT hyb (st.st party) c rc).run (st, aux)) ?_
        intro ⟨res, gs2, aux2⟩ hr
        have hgs2 : gs2 = st := (hrecv.2 _ hr).1
        have hgs2_eq : gs2 = st := hgs2; subst gs2
        rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
        · dsimp only [hop2OutEnc, Option.map]
          rw [comp_eval_caseOpt]
          dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]
          rw [comp_eval_ret]
          have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
            (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, none)) .nil)
          have hpostE := eval_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
            q st party c rec_.pos none hQ.lists
          dsimp only [stS, stGs, stChall, stMk, hop2FullEnc, Expr.eval,
            Expr.v0, Expr.v2, Expr.v3, ρ₂, ρ₁, ρ₀]
          simp only [env_get_zero, env_get_succ]
          rw [wk1Expr_eval]; erw [hpostL]; rw [hpostE]
          simp [StateT.run_pure, liftVal]
        · dsimp only [hop2OutEnc, Option.map]
          rw [comp_eval_caseOpt]
          dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]
          rw [comp_eval_ret]
          let outE2E : (drRecvOutT ℓ).denote := some (st', (t', (i', m')))
          have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
            (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, outE2E)) .nil)
          have hpostE := eval_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
            q st party c rec_.pos outE2E hQ.lists
          have hbadL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
            (.cons (s, (st.st party, c)) .nil)
          have hpartyQ := hQ.reach.party party
          have hbadE := eval_hop2BadAtE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
            (decT := decT) (encT := encT) P rfl rfl s (st.st party) c
            hpartyQ.receiverChains_le (hpartyQ.aligned.trans_le hpartyQ.receiverChains_le)
          let tQuad : Ty ASig :=
            .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
          let ρ₄ : Env [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0] :=
            .cons ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ)))
              (.cons (some ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ))),
                hop2AuxEnc (ℓ := ℓ) aux2) ρ₂)
          have hbadAtEval :
              (Expr.letE
                (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                  (.pair (.fst .v3) (.snd (.snd .v4))))
                (wk1Expr
                  (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam)
                    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                      (encT := encT))))).eval ρ₄ =
              hop2BadAt P s (st.st party) c := by
            rw [letE_eval, wk1Expr_eval]
            exact hbadL.trans hbadE
          have hcommEval := eval_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (.snd .v1) (.fst (.snd .v4)) (.snd .v0) ρ₄ aux2 party
            (uOpt.map (hop2UpdEnc (ℓ := ℓ))) rfl rfl rfl
          have huRound :
              (uOpt.map (hop2UpdEnc (ℓ := ℓ))).map (hop2UpdDec (ℓ := ℓ)) = uOpt := by
            cases uOpt <;> simp
          rw [huRound] at hcommEval
          have horEval :
              (orE (auxBad (.snd .v1))
                (.letE
                  (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                    (.pair (.fst .v3) (.snd (.snd .v4))))
                  (wk1Expr
                    (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                      (encT := encT) (decT := decT) (lam := lam)
                      (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                        (encT := encT)))))).eval ρ₄ =
              (aux2.bad || hop2BadAt P s (st.st party) c) := by
            rw [orE_eval, eval_auxBad C K Dh encPt encT decT lam _ ρ₄ aux2 rfl, hbadAtEval]
          have hauxEval := eval_auxSetBad C K Dh encPt encT decT lam
            (hop2CommitE (.snd .v1) (.fst (.snd .v4)) (.snd .v0)) _ ρ₄
            (hop2Commit aux2 party uOpt) (aux2.bad || hop2BadAt P s (st.st party) c)
            hcommEval horEval
          have hpostEval :
              (Expr.letE
                (.pair (.pair (stGs C K Dh encPt encT decT lam (.fst .v4)) (.snd .v4))
                  (.pair (.snd .v3) (.some (.fst .v0))))
                (wk1Expr
                  (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam)
                    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                      (encT := encT) q)))).eval ρ₄ =
              liftVal (Pt := Pt)
                ((dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
                  (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, outE2E)) .nil)) := by
            rw [letE_eval, wk1Expr_eval]; exact hpostL
          change pure ((Expr.pair _ _).eval ρ₄) = _
          dsimp only [Expr.v0] at hpostEval hauxEval
          simp only [pair_eval, stMk, fst_eval, snd_eval, hpostEval, hpostE, hauxEval, outE2E,
            StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
          rfl
      · intro fin hfin
        rw [mem_support_bind_iff] at hfin
        obtain ⟨rc, -, hfin⟩ := hfin
        rw [pure_bind, StateT.run_bind, mem_support_bind_iff] at hfin
        obtain ⟨⟨res, gs2, aux2⟩, hr, hfin⟩ := hfin
        let ρ₂ : Env [BV256, tInr, t0] := .cons rc ρ₁
        have hrecv := hop2RecvC_eval_and_inv M hM q k
          (stChall C K Dh encPt encT decT lam (.fst .v2))
          (stAux C K Dh encPt encT decT lam (.fst .v2))
          (.fst .v1) (.snd (.snd .v2)) .v0
          ρ₂ idA idB st chall aux (st.st party) c rc
          rfl rfl rfl rfl rfl (hQ.reach.party party) hAuxQ.1 hAuxQ.2
        have ⟨hgs2, hlazy2, hmade2, hstInv⟩ := hrecv.2 _ hr
        have hgs2_eq : gs2 = st := hgs2; subst gs2
        have hlazyRem : aux2.lazy.length ≤ qRem + 1 :=
          Nat.le_trans hlazy2 (Nat.add_le_add_right hAuxRem.1 1)
        have hmadeRem : aux2.made.length ≤ qRem + 1 := hmade2.symm ▸ hAuxRem.2
        rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfin
          subst hfin
          exact ⟨hRem.mono (Nat.le_succ qRem), ⟨hlazyRem, Nat.le_succ_of_le hmadeRem⟩⟩
        · simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hfin
          subst hfin
          refine ⟨smReachBounded_accept C K hRem party (hstInv st' t' i' m' uOpt rfl) rec_.pos,
            ?_⟩
          have hcommB := hop2AuxBounded_commit party uOpt hlazyRem hmadeRem
          exact ⟨hcommB.1, hcommB.2⟩


theorem hop2IjArmC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qRem qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (party : Party) (c : Bytes)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st)
    (hAuxQ : Hop2AuxBounded q aux) (hAuxRem : Hop2AuxBounded qRem aux) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2IjArmC C K Dh encPt encT decT lam M q qep k).eval
      (.cons (hop2FullEnc s chall (st, aux), (partyEnc party, c)) .nil) =
      (fun out : Option (RecvResult (Plain ℓ)) ×
            (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (none, (out.1.map recvResultEnc, none)),
         hop2FullEnc s chall out.2)) <$>
        (hop2Inject P Dh encT decT qep s hyb (party, c)).run (st, aux) ∧
    (∀ r ∈ support ((hop2Inject P Dh encT decT qep s hyb (party, c)).run (st, aux)),
      SmReachBounded C K (qRem + 1) r.2.1 ∧ Hop2AuxBounded (qRem + 1) r.2.2) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let ρ₀ : Env [t0] :=
    .cons (hop2FullEnc s chall (st, aux), (partyEnc party, c)) .nil
  unfold hop2IjArmC hop2Inject
  have hpreL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
    (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)
  have hpreE := eval_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)
    st party c hQ.lists.trans_le
  rw [comp_eval_caseSum]
  have hpreStep :
      (Expr.letE (O := AOps) (.pair (stGs C K Dh encPt encT decT lam (.fst .v0)) (.snd .v0))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
              q (2 + 1))))).eval ρ₀ =
      liftVal (Pt := Pt)
        ((ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)).eval
          (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)) := by
    rw [letE_eval, wk1Expr_eval]; exact hpreL
  rw [hpreStep, hpreE, StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only [Nat.reduceAdd]
  by_cases href :
      st.win || (st.inTransit party.other c).isSome || !(st.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp only [href, ↓reduceIte]
    dsimp only [liftVal]
    rw [comp_eval_ret, StateT.run_pure, map_pure]
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hRem.mono (Nat.le_succ qRem), hAuxRem.mono (Nat.le_succ qRem)⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    dsimp only [liftVal]
    rw [StateT.run_bind, StateT.run_lift, bind_assoc]
    let ρ₁ : Env [GhostStT, t0] := .cons (st.st party) ρ₀
    have hunif :
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256)) =
        hop2Unif (Pt := Pt) := rfl
    refine ⟨?_, ?_⟩
    · rw [map_eq_bind_pure_comp]
      simp only [Function.comp_def, bind_assoc]
      rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, hunif]
      refine bind_congr fun rc => ?_
      let ρ₂ : Env [BV256, GhostStT, t0] := .cons rc ρ₁
      have hrecv := hop2RecvC_eval_and_inv M hM q k
        (stChall C K Dh encPt encT decT lam (.fst .v2))
        (stAux C K Dh encPt encT decT lam (.fst .v2))
        .v1 (.snd (.snd .v2)) .v0
        ρ₂ idA idB st chall aux (st.st party) c rc
        rfl rfl rfl rfl rfl (hQ.reach.party party) hAuxQ.1 hAuxQ.2
      rw [comp_eval_bind, pure_bind, StateT.run_bind, bind_assoc]
      dsimp only; erw [hrecv.1]; rw [bind_map_left]
      refine bind_congr_of_mem_support'
        ((hop2Recv P Dh encT decT hyb (st.st party) c rc).run (st, aux)) ?_
      intro ⟨res, gs2, aux2⟩ hr
      have hgs2 : gs2 = st := (hrecv.2 _ hr).1
      have hgs2_eq : gs2 = st := hgs2; subst gs2
      rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
      · dsimp only [hop2OutEnc, Option.map]
        rw [comp_eval_caseOpt]
        dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]
        rw [comp_eval_ret]
        have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q 3 qep)
          (.cons ((e2eGsEnc st, (partyEnc party, c)), none) .nil)
        have hpostE := eval_ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
          (encT := encT) q 3 qep st party c none hQ.lists
        dsimp only [stS, stGs, stChall, stMk, hop2FullEnc, Expr.eval,
          Expr.v0, Expr.v3, ρ₂, ρ₁, ρ₀]
        simp only [env_get_zero, env_get_succ]
        rw [wk1Expr_eval]; erw [hpostL]; rw [hpostE]
        simp [StateT.run_pure, liftVal]
      · dsimp only [hop2OutEnc, Option.map]
        rw [comp_eval_caseOpt]
        dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]
        rw [comp_eval_ret]
        let outE2E : (drRecvOutT ℓ).denote := some (st', (t', (i', m')))
        have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q 3 qep)
          (.cons ((e2eGsEnc st, (partyEnc party, c)), outE2E) .nil)
        have hpostE := eval_ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
          (encT := encT) q 3 qep st party c outE2E hQ.lists
        have hbadL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
          (.cons (s, (st.st party, c)) .nil)
        have hpartyQ := hQ.reach.party party
        have hbadE := eval_hop2BadAtE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
          (decT := decT) (encT := encT) P rfl rfl s (st.st party) c
          hpartyQ.receiverChains_le (hpartyQ.aligned.trans_le hpartyQ.receiverChains_le)
        let tQuad : Ty ASig :=
          .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
        let ρ₄ : Env [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0] :=
          .cons ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ)))
            (.cons (some ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ))),
              hop2AuxEnc (ℓ := ℓ) aux2) ρ₂)
        have hbadAtEval :
            (Expr.letE
              (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                (.pair .v3 (.snd (.snd .v4))))
              (wk1Expr
                (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                    (encT := encT))))).eval ρ₄ =
            hop2BadAt P s (st.st party) c := by
          rw [letE_eval, wk1Expr_eval]
          exact hbadL.trans hbadE
        let aux1 : Hop2Aux Pt := { aux2 with bad := aux2.bad || hop2BadAt P s (st.st party) c }
        have horEval :
            (orE (auxBad (.snd .v1))
              (.letE
                (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                  (.pair .v3 (.snd (.snd .v4))))
                (wk1Expr
                  (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam)
                    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                      (encT := encT)))))).eval ρ₄ =
            (aux2.bad || hop2BadAt P s (st.st party) c) := by
          rw [orE_eval, eval_auxBad C K Dh encPt encT decT lam _ ρ₄ aux2 rfl, hbadAtEval]
        have haux1Eval := eval_auxSetBad C K Dh encPt encT decT lam
          (.snd .v1) _ ρ₄ aux2 (aux2.bad || hop2BadAt P s (st.st party) c) rfl horEval
        have hcommEval := eval_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          _ (.fst (.snd .v4)) (.snd .v0) ρ₄ aux1 party
          (uOpt.map (hop2UpdEnc (ℓ := ℓ))) haux1Eval rfl rfl
        have huRound :
            (uOpt.map (hop2UpdEnc (ℓ := ℓ))).map (hop2UpdDec (ℓ := ℓ)) = uOpt := by
          cases uOpt <;> simp
        rw [huRound] at hcommEval
        have hpostEval :
            (Expr.letE
              (.pair (.pair (stGs C K Dh encPt encT decT lam (.fst .v4)) (.snd .v4))
                (.some (.fst .v0)))
              (wk1Expr
                (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                    (encT := encT) q 3 qep)))).eval ρ₄ =
            liftVal (Pt := Pt)
              ((ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                (encT := encT) q 3 qep).eval
                (.cons ((e2eGsEnc st, (partyEnc party, c)), outE2E) .nil)) := by
          rw [letE_eval, wk1Expr_eval]; exact hpostL
        change pure ((Expr.pair _ _).eval ρ₄) = _
        dsimp only [Expr.v0] at hpostEval hcommEval
        simp only [pair_eval, stMk, fst_eval, snd_eval, ite_eval,
          hpostEval, hpostE, haux1Eval, hcommEval, outE2E]
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
            StateT.run_pure, pure_bind]
          rfl
        · simp only [hqep, ↓reduceIte]
          by_cases htriv : st.trivial 3 ⟨party.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_pure, pure_bind]
            rfl
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
              StateT.run_set, StateT.run_pure, pure_bind]
            rfl
    · intro fin hfin
      rw [mem_support_bind_iff] at hfin
      obtain ⟨rc, -, hfin⟩ := hfin
      rw [pure_bind, StateT.run_bind, mem_support_bind_iff] at hfin
      obtain ⟨⟨res, gs2, aux2⟩, hr, hfin⟩ := hfin
      let ρ₂ : Env [BV256, GhostStT, t0] := .cons rc ρ₁
      have hrecv := hop2RecvC_eval_and_inv M hM q k
        (stChall C K Dh encPt encT decT lam (.fst .v2))
        (stAux C K Dh encPt encT decT lam (.fst .v2))
        .v1 (.snd (.snd .v2)) .v0
        ρ₂ idA idB st chall aux (st.st party) c rc
        rfl rfl rfl rfl rfl (hQ.reach.party party) hAuxQ.1 hAuxQ.2
      have ⟨hgs2, hlazy2, hmade2, hstInv⟩ := hrecv.2 _ hr
      have hgs2_eq : gs2 = st := hgs2; subst gs2
      have hlazyRem : aux2.lazy.length ≤ qRem + 1 :=
        Nat.le_trans hlazy2 (Nat.add_le_add_right hAuxRem.1 1)
      have hmadeRem : aux2.made.length ≤ qRem + 1 := hmade2.symm ▸ hAuxRem.2
      rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfin
        subst hfin
        exact ⟨hRem.mono (Nat.le_succ qRem), ⟨hlazyRem, Nat.le_succ_of_le hmadeRem⟩⟩
      · dsimp only at hfin
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hfin
          subst hfin
          exact ⟨hRem.mono (Nat.le_succ qRem), ⟨hlazyRem, Nat.le_succ_of_le hmadeRem⟩⟩
        · simp only [hqep, ↓reduceIte] at hfin
          by_cases htriv : st.trivial 3 ⟨party.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hfin
            subst hfin
            refine ⟨smReachBounded_accept C K hRem party
              (hstInv st' t' i' m' uOpt rfl) ⟨party.other, t', i'⟩, ?_⟩
            exact hop2AuxBounded_commit party uOpt hlazyRem hmadeRem
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
              StateT.run_set, StateT.run_pure, pure_bind, support_pure,
              Set.mem_singleton_iff] at hfin
            subst hfin
            exact ⟨⟨⟨hRem.reach.alice, hRem.reach.bob⟩,
              (hRem.lists.setWin true).mono (Nat.le_succ qRem)⟩,
              ⟨hlazyRem, Nat.le_succ_of_le hmadeRem⟩⟩


omit [DecidableEq Pt] [Zero Pt] in
private theorem liftM_hop2_map {α β : Type} (f : α → β) (p : ProbComp α) :
    (liftM (f <$> p) : Hop2Comp Pt β) = f <$> (liftM p : Hop2Comp Pt α) := by
  rw [← atomicPrfIface_liftP PtT BV256 2 (atomicSamplers 0 Pt),
    ← atomicPrfIface_liftP PtT BV256 2 (atomicSamplers 0 Pt)]
  unfold Iface.liftP
  simp [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure]

/-- Combined 5-arm `hop2Impl` handler over `atomicSessionOps` parameterized by `Hop2Mode`. -/

theorem hop2StepC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qRem qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st)
    (hAuxQ : Hop2AuxBounded q aux) (hAuxRem : Hop2AuxBounded qRem aux) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2StepC C K Dh encPt encT decT lam M q qep k).eval
      (.cons (hop2FullEnc (ℓ := ℓ) s chall (st, aux))
        (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)) =
      (fun out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
            (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
        (liftVal (Pt := Pt)
          (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id sq out.1),
         hop2FullEnc (ℓ := ℓ) s chall out.2)) <$>
        (hop2Impl P Dh encT decT qep s hyb (.inr sq)).run (st, aux) ∧
    (∀ r ∈ support ((hop2Impl P Dh encT decT qep s hyb (.inr sq)).run (st, aux)),
      SmReachBounded C K (qRem + 1) r.2.1 ∧ Hop2AuxBounded (qRem + 1) r.2.2) := by
  intro P hyb
  let CoinI := coinOnlyIface ℓ Pt
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  change (hop2StepC C K Dh encPt encT decT lam M q qep k).eval
      (.cons (hop2FullEnc (ℓ := ℓ) s chall (st, aux))
        (.cons (t := smQT) (ReductionDsl.smQenc sq) .nil)) = _ ∧ _
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
      wk1Comp_eval]
    simp only [comp_eval_ret, stS, stGs, stAux, stChall, stMk, hop2FullEnc,
      Expr.eval, Expr.v0, Expr.v3, Env.get]
    let tTr : Ty ESig :=
      .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.opt CryptoVerification.E2E.Costed.BV512)))
    let argE2E : tTr.denote := (e2eGsEnc st, (partyEnc party, (m, optR)))
    have htrStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (drTrArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons
            (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ))
              (.prod .bool (.prod PlainT (.opt BV512))))
            (liftVal (Pt := Pt) (e2eGsEnc st), (ReductionDsl.partyToBool party, (m, optR))) .nil) =
        liftVal (Pt := Pt) <$>
          ((drTrArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
        (drTrArmC hooks coins q (2 + 1) qep
          (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases party <;> cases optR <;> rfl
    dsimp only [Expr.v0] at htrStep
    rw [htrStep]
    have htr := drTrArmC_eval hooks coins q (2 + 1) qep
      (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      idA idB s st party m optR hQ rfl rfl
    dsimp only [Expr.v0] at htr
    rw [htr]
    have hliftP :
        (coinE2EIface CoinI).liftP
          ((transmitR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT)
            (party, m, optR)).run st) =
        (transmitR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m, optR)).run st :=
      coinOnlyIface_liftP (ℓ := ℓ) (Pt := Pt) _
    rw [hliftP, liftM_hop2_map, liftM_hop2_map]
    refine ⟨?_, ?_⟩
    · simp only [hop2Lift, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, Prod.map, Option.map, smRenc, liftVal]
      exact bind_congr fun x => by rcases x with ⟨w, _⟩; rcases w <;> rfl
    · intro r hr
      dsimp only [hop2Lift] at hr
      rw [StateT.run_mk, mem_support_bind_iff] at hr
      obtain ⟨⟨w, gs'⟩, hgs', hr⟩ := hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      rw [← liftComp_eq_liftM, support_liftComp] at hgs'
      exact ⟨smReachBounded_transmitR C K idA idB ℓ 3 qep qRem s
        (configRefuseEarlyBobCorr decT encT) (party, m, optR) hRem hgs',
        hAuxRem.mono (Nat.le_succ qRem)⟩
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
      wk1Comp_eval]
    simp only [comp_eval_ret, stS, stGs, stAux, stChall, stMk, hop2FullEnc,
      Expr.eval, Expr.v2, Expr.v4, Env.get]
    let tCh : Ty ESig :=
      .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
    let argE2E : tCh.denote := (e2eGsEnc st, (partyEnc party, (m0, (m1, optR))))
    have hchStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (drChArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons
            (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ))
              (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
            (liftVal (Pt := Pt) (e2eGsEnc st),
              (ReductionDsl.partyToBool party, (m0, (m1, optR)))) .nil) =
        liftVal (Pt := Pt) <$>
          ((drChArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
        (drChArmC hooks coins q (2 + 1) qep
          (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases party <;> cases optR <;> rfl
    dsimp only [Expr.v0] at hchStep
    rw [hchStep]
    have hch := drChArmC_eval hooks coins q (2 + 1) qep
      (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      idA idB s st party m0 m1 optR hQ rfl rfl
    dsimp only [Expr.v0] at hch
    rw [hch]
    have hliftP :
        (coinE2EIface CoinI).liftP
          ((challR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT)
            (party, m0, m1, optR)).run st) =
        (challR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR)).run st :=
      coinOnlyIface_liftP (ℓ := ℓ) (Pt := Pt) _
    rw [hliftP, liftM_hop2_map, liftM_hop2_map]
    refine ⟨?_, ?_⟩
    · simp only [hop2Lift, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, Prod.map, Option.map, smRenc, liftVal]
      exact bind_congr fun x => by rcases x with ⟨w, _⟩; rcases w <;> rfl
    · intro r hr
      dsimp only [hop2Lift] at hr
      rw [StateT.run_mk, mem_support_bind_iff] at hr
      obtain ⟨⟨w, gs'⟩, hgs', hr⟩ := hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      rw [← liftComp_eq_liftM, support_liftComp] at hgs'
      exact ⟨smReachBounded_challR C K idA idB ℓ 3 qep qRem s
        (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR) hRem hgs',
        hAuxRem.mono (Nat.le_succ qRem)⟩
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc, smRenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, wk1Comp_eval]
    simp only [Expr.eval, Expr.v3, Env.get]
    exact hop2DlArmC_eval_and_inv C K Dh encPt encT decT idA idB lam M hM
      q qRem k s chall st aux party c hQ hRem hAuxQ hAuxRem
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc, smRenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, wk1Comp_eval]
    simp only [Expr.eval, Expr.v4, Env.get]
    exact hop2IjArmC_eval_and_inv C K Dh encPt encT decT idA idB lam M hM
      q qRem qep k s chall st aux party c hQ hRem hAuxQ hAuxRem
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
      wk1Comp_eval]
    simp only [comp_eval_ret, stS, stGs, stAux, stChall, stMk, hop2FullEnc,
      Expr.eval, Expr.v4, Expr.v6, Env.get]
    let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
    let argE2E : tCr.denote := (e2eGsEnc st, partyEnc party)
    have hcrStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
            (decT := decT) (encT := encT) q
            (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) .bool)
            (liftVal (Pt := Pt) (e2eGsEnc st), ReductionDsl.partyToBool party) .nil) =
        liftVal (Pt := Pt) <$>
          ((drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
            (decT := decT) (encT := encT) q
            (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
        (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
          (decT := decT) (encT := encT) q
          (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases party <;> rfl
    dsimp only [Expr.v0] at hcrStep
    rw [hcrStep]
    have hcr := drCrArmC_eval (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q
      (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      st party hQ.lists rfl rfl
    dsimp only [Expr.v0] at hcr
    rw [hcr]
    have hliftP :
        (coinE2EIface CoinI).liftP ((corrR (configRefuseEarlyBobCorr decT encT) party).run st) =
        (corrR (configRefuseEarlyBobCorr decT encT) party).run st :=
      coinOnlyIface_liftP (ℓ := ℓ) (Pt := Pt) _
    rw [hliftP, liftM_hop2_map, liftM_hop2_map]
    refine ⟨?_, ?_⟩
    · simp only [hop2Lift, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, Prod.map, smRenc]
      refine bind_congr fun ⟨st?, s'⟩ => congrArg pure ?_
      cases st? <;> rfl
    · intro r hr
      dsimp only [hop2Lift] at hr
      rw [StateT.run_mk, mem_support_bind_iff] at hr
      obtain ⟨⟨st?, gs'⟩, hgs', hr⟩ := hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      rw [← liftComp_eq_liftM, support_liftComp] at hgs'
      exact ⟨smReachBounded_corrR C K ℓ qRem (configRefuseEarlyBobCorr decT encT) party hRem hgs',
        hAuxRem.mono (Nat.le_succ qRem)⟩


theorem hop2GameRed_eval
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) :
    (hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M q qep k).eval
      (fun _ => A) (s, chall) =
    hop2Game (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      ℓ Dh encT decT qep s ⟨k, chall, stepOf chall.1⟩ A := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let so := hop2Impl (ℓ := ℓ) P Dh encT decT qep s hyb
  let enc := hop2FullEnc (ℓ := ℓ) (Pt := Pt) s chall
  let Inv : ℕ → GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt → Prop :=
    fun m ga => m ≤ q ∧ SmReachBounded C K (q - m) ga.1 ∧ Hop2AuxBounded (q - m) ga.2
  have hinitBoth :=
    hop2InitBodyC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k s chall
  have hinitEval :
      (hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M q qep k).init.eval
        (.cons (s, chall) .nil) =
      Prod.map id enc <$> hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall) := by
    dsimp only [hop2GameRed]
    rw [hM.embedCoin_eq]
    exact hinitBoth.1
  have hsim := eval_eq_simulateQ_of_enc
    (hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M q qep k)
    enc Inv
    (hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k)
    so
    (fun ga _ => (pure ga.2.bad : Hop2Comp Pt Bool))
    q (s, chall)
    hinitEval
    (fun r hr => by
      refine ⟨Nat.le_refl q, ?_⟩
      rw [Nat.sub_self]
      exact hinitBoth.2 r hr)
    (fun _ _ => rfl)
    (fun m sq ga hga => by
      rcases ga with ⟨st, aux⟩
      have hreachQ : SmReachBounded C K q st := hga.2.1.mono (by omega)
      have hauxQ : Hop2AuxBounded q aux := hga.2.2.mono (by omega)
      have hstep := hop2StepC_eval_and_inv C K Dh encPt encT decT idA idB lam M hM
        q (q - (m + 1)) qep k s chall st aux sq hreachQ hga.2.1 hauxQ hga.2.2
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (hop2StepC C K Dh encPt encT decT lam M q qep k).eval
              (.cons (enc (st, aux)) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id enc <$> (so (.inr sq)).run (st, aux)
        rw [hstep.1]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun ⟨ans, ga'⟩ => congrArg pure ?_
        exact Prod.ext (e2eSessionCodec_rdec_liftVal_smRenc Pt sq ans) rfl
      · intro r hr
        have hr' := hstep.2 r hr
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact ⟨by omega, heq ▸ hr'.1, heq ▸ hr'.2⟩)
    (fun _ _ _ => rfl)
    (fun {m n} _ hmn hn => ⟨by omega, hn.2.1.mono (by omega), hn.2.2.mono (by omega)⟩)
    (fun _ => A)
    (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]
  unfold hop2Game hop2InitImpl
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun _ => bind_congr fun _ => bind_congr fun _ =>
      bind_congr fun x => by cases x; rfl


theorem hop2PrgRedK_eval_at (ℓ q qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) (hk : k < 16) :
    (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).eval
      (fun _ => A) (s, chall) =
    CryptoVerification.E2E.hop2PrgRedK
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      ℓ Dh encPt encT decT qep s k A chall := by
  unfold hop2PrgRedK
  simp only [hℓ, hk, and_self, ↓reduceIte, hop2PrgRedKReal]
  let prfReal : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp :=
    fun I => pure ((extractPRF C.F encPt).tag chall.1 I)
  rw [eval_redCoinToPrf
      (hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k)
      prfReal (fun _ => A) (s, chall),
    redCoinToPrf_hop2GameRed_prgCoinMode C K Dh encPt encT decT idA idB lam q qep k,
    hop2GameRed_eval C K Dh encPt encT decT idA idB lam
      (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      prgLiftedMode_evalSpec q qep k s chall A hA]
  rfl

/-- Exact `evalSpkSwapPrgHybrid` agreement of `hop2PrgRedK` for all `k < spkSwapHybridCount`. -/
theorem hop2PrgRedK_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
      (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    CryptoVerification.E2E.hop2PrgRedK
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      ℓ Dh encPt encT decT qep s k A := by
  have hk16 : k < 16 := by unfold spkSwapHybridCount at hk; omega
  funext chall
  exact hop2PrgRedK_eval_at C K Dh encPt encT decT idA idB lam ℓ q qep k s chall A hA hℓ hk16


theorem hop2PrfRedK_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
      (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    CryptoVerification.E2E.hop2PrfRedK
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      ℓ Dh encT decT qep s k A := by
  have hk16 : k < 16 := by unfold spkSwapHybridCount at hk; omega
  dsimp only [evalSpkSwapPrfHybrid]
  unfold hop2PrfRedK
  simp only [hℓ, hk16, and_self, ↓reduceIte]
  let RG := hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k
  have hinit :
      (hop2InitPrfC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).eval
        (.cons s .nil) =
      (do
        let r ← hop2Unif (Pt := Pt)
        let c ← hop2Unif (Pt := Pt)
        RG.init.eval (.cons (s, (r, c)) .nil)) := by
    dsimp only [hop2InitPrfC, RG, hop2GameRed, prfOracleMode, compCoinToPrf]
    rw [compCoinToPrf_wk1Comp]
    simp only [comp_eval_bind,
      compCoinToPrf_eval_eq_liftM, draw256Coin_eval, wk1Comp_eval]
    rfl
  dsimp only [CostedReduction.eval, hop2PrfRedKReal, RG, hop2GameRed] at hinit ⊢
  rw [hinit]
  simp only [bind_assoc]
  unfold CryptoVerification.E2E.hop2PrfRedK
  refine bind_congr fun r => bind_congr fun c => ?_
  exact hop2GameRed_eval C K Dh encPt encT decT idA idB lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    prfOracleMode_evalSpec q qep k s (r, c) A hA


end Hop2Reductions
end Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg

-- AUTO-BRIDGE BEGIN
namespace Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg
export Computational.Proofs.Game.PromotedCostedReds.SessionCostExactDefs (
  BoxEq box_le exprAllOps compAllOps exprAllOps_renExpr exprAllOps_wk1Expr compAllOps_renComp compAllOps_wk1Comp sessionCostExactCryptoOp sessionCostExactOp NoKemKeyGenExpr NoKemKeyGenComp liftExpr_cost_exact liftCompEmpty_cost_exact liftCompCoins_cost_exact noKemKeyGenExpr_renExpr noKemKeyGenExpr_wk1Expr noKemKeyGenComp_renComp noKemKeyGenComp_wk1Comp noKemKeyGenComp_ret noKemKeyGenComp_bind noKemKeyGenComp_ite noKemKeyGenComp_caseOpt noKemKeyGenComp_caseSum noKemKeyGenComp_sample noKemKeyGenComp_query noKemKeyGenComp_iter noKemKeyGenComp_findM noKemKeyGenComp_anyM noKemKeyGenComp_mapM noKemKeyGenComp_consumeFirstM noKemKeyGenComp_foldM noKemKeyGenExpr_optBytes32LitE noKemKeyGenExpr_var noKemKeyGenExpr_v0 noKemKeyGenExpr_v1 noKemKeyGenExpr_v2 noKemKeyGenExpr_v3 noKemKeyGenExpr_v4 noKemKeyGenExpr_v5 noKemKeyGenExpr_v6 noKemKeyGenExpr_unit noKemKeyGenExpr_bool noKemKeyGenExpr_nat noKemKeyGenExpr_none noKemKeyGenExpr_nil noKemKeyGenExpr_add noKemKeyGenExpr_sub noKemKeyGenExpr_mulK noKemKeyGenExpr_divK noKemKeyGenExpr_modK noKemKeyGenExpr_lt noKemKeyGenExpr_eqN noKemKeyGenExpr_not noKemKeyGenExpr_and noKemKeyGenExpr_ite noKemKeyGenExpr_pair noKemKeyGenExpr_fst noKemKeyGenExpr_snd noKemKeyGenExpr_inl noKemKeyGenExpr_inr noKemKeyGenExpr_some noKemKeyGenExpr_caseOpt noKemKeyGenExpr_caseSum noKemKeyGenExpr_letE noKemKeyGenExpr_cons noKemKeyGenExpr_len noKemKeyGenExpr_take noKemKeyGenExpr_appendL noKemKeyGenExpr_findB noKemKeyGenExpr_anyB noKemKeyGenExpr_mapB noKemKeyGenExpr_foldrB noKemKeyGenExpr_tconst noKemKeyGenExpr_tget noKemKeyGenExpr_tset noKemKeyGenExpr_e2ePureOp noKemKeyGenExpr_e2eCurveOp noKemKeyGenExpr_e2eCryptoOp noKemKeyGenExpr_orE noKemKeyGenExpr_boolEq noKemKeyGenExpr_isSomeE noKemKeyGenExpr_otherE noKemKeyGenExpr_pGet noKemKeyGenExpr_sendAddrsE noKemKeyGenExpr_expectedAddrsE noKemKeyGenComp_spqrSendComp noKemKeyGenComp_spqrRecvComp noKemKeyGenExpr_drSendPostE noKemKeyGenComp_drSendC noKemKeyGenExpr_drRecvFinishE noKemKeyGenComp_drReceiveC noKemKeyGenComp_drTrArmC noKemKeyGenComp_drChArmC noKemKeyGenComp_drCrArmC drSendAtomicC_cost_exact drReceiveAtomicC_cost_exact
)
export Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInDefs (
  env_get_zero fst_eval snd_eval env_get_succ compCoinToPrf cost_compCoinToPrf size_compCoinToPrf queries_compCoinToPrf_zero queries_coinOnly_zero redCoinToPrf size_redCoinToPrf atomicPrfIface_liftP coinOnlyIface_liftP eval_compCoinToPrf eval_redCoinToPrf compCoinToPrf_renComp compCoinToPrf_wk1Comp compCoinToPrf_eval_eq_liftM hop2InitArgT hop2InitAliceE2EE eval_hop2InitAliceE2EE cost_hop2InitAliceE2EE size_hop2InitAliceE2EE hop2InitGsE2EE eval_hop2InitGsE2EE cost_hop2InitGsE2EE size_hop2InitGsE2EE dlPreE2EE cost_dlPreE2EE size_dlPreE2EE dlPostE2EE cost_dlPostE2EE size_dlPostE2EE ijPreE2EE cost_ijPreE2EE size_ijPreE2EE ijPostHop2E2EE cost_ijPostHop2E2EE size_ijPostHop2E2EE eval_dlPreE2EE eval_dlPostE2EE eval_ijPreE2EE eval_ijPostHop2E2EE hop2BadAtE2EE cost_hop2BadAtE2EE size_hop2BadAtE2EE eval_hop2BadAtE2EE needsDHE2EE cost_needsDHE2EE size_needsDHE2EE eval_needsDHE2EE hasSenderChainE2EE cost_hasSenderChainE2EE size_hasSenderChainE2EE eval_hasSenderChainE2EE sendHalfRealE2EE cost_sendHalfRealE2EE size_sendHalfRealE2EE eval_sendHalfRealE2EE prepHop2DHState prepHop2DHStateE2EE cost_prepHop2DHStateE2EE size_prepHop2DHStateE2EE eval_prepHop2DHStateE2EE partyReachInv_prepHop2DHState params_receive_prepHop2DHState sPureOp sSymOp sGroupOp sPtDecOp sCurveOp eval_sPureOp cost_sPureOp eval_sSymOp cost_sSymOp eval_sGroupOp cost_sGroupOp eval_sPtDecOp cost_sPtDecOp eval_sCurveOp cost_sCurveOp size_sPureOp size_sSymOp size_sGroupOp size_sPtDecOp size_sCurveOp drawBoolCoin draw256Coin drawBoolCoin_cost draw256Coin_cost drawBoolCoin_size draw256Coin_size atomicDraw256_size drawBoolCoin_eval draw256Coin_eval Hop2Mode prgCoinMode prgLiftedMode prfOracleMode hop2EntryTy hop2AuxTy hop2ChallTy hop2UpdTy hop2OutTy hop2RecvResTy hop2SendHalfResTy hop2FullStTy hop2AuxEnc hop2AuxDec hop2AuxDec_enc hop2UpdEnc hop2UpdDec hop2UpdDec_enc hop2OutEnc pSetLocal auxLazy auxMade auxIdx auxCoins auxBad auxMk auxSetBad auxConsLazy hop2LookupE hop2CommitE cost_auxSetBad cost_auxConsLazy cost_hop2LookupE cost_hop2CommitE size_auxSetBad size_auxConsLazy size_hop2LookupE size_hop2CommitE eval_hop2LookupE eval_hop2CommitE dhTargetPtAtomicE cost_dhTargetPtAtomicE size_dhTargetPtAtomicE eval_dhTargetPtAtomicE finishHop2DHAtomicC queries_finishHop2DHAtomicC cost_finishHop2DHAtomicC size_finishHop2DHAtomicC hop2FinishNoneC queries_hop2FinishNoneC cost_hop2FinishNoneC size_hop2FinishNoneC hop2LazyC queries_hop2LazyC cost_hop2LazyC size_hop2LazyC hop2SendHalfSomeC queries_hop2SendHalfSomeC cost_hop2SendHalfSomeC size_hop2SendHalfSomeC hop2DHC queries_hop2DHC cost_hop2DHC size_hop2DHC hop2RecvC queries_hop2RecvC size_hop2RecvC Hop2EvalSpec prgLiftedMode_evalSpec prfOracleMode_evalSpec compCoinToPrf_finishHop2DHAtomicC compCoinToPrf_hop2FinishNoneC compCoinToPrf_hop2LazyC compCoinToPrf_hop2SendHalfSomeC compCoinToPrf_hop2DHC compCoinToPrf_hop2RecvC Hop2AuxBounded Hop2AuxBounded.mono hop2AuxBounded_commit hop2DecryptOut finishHop2DHAtomicC_eval_and_inv hop2FinishNoneOut hop2FinishNoneC_eval_and_inv hop2LazyC_eval hop2SendHalfSomeC_eval noKemKeyGenExpr_hop2InitGsE2EE noKemKeyGenExpr_dlPreE2EE noKemKeyGenExpr_dlPostE2EE noKemKeyGenExpr_ijPreE2EE noKemKeyGenExpr_ijPostHop2E2EE noKemKeyGenExpr_hop2BadAtE2EE noKemKeyGenExpr_needsDHE2EE noKemKeyGenExpr_hasSenderChainE2EE noKemKeyGenExpr_sendHalfRealE2EE noKemKeyGenExpr_prepHop2DHStateE2EE cost_finishHop2DHAtomicC_tight cost_hop2RecvC stS stGs stAux stChall stMk hop2FullEnc eval_auxSetBad eval_auxBad smReachBounded_accept hop2DlArmC queries_hop2DlArmC size_hop2DlArmC compCoinToPrf_hop2DlArmC hop2IjArmC queries_hop2IjArmC size_hop2IjArmC compCoinToPrf_hop2IjArmC hop2StepC queries_hop2StepC size_hop2StepC compCoinToPrf_hop2StepC hop2InitBodyC hop2InitPrfC queries_hop2InitBodyC queries_hop2InitPrfC cost_hop2InitBodyC cost_hop2InitPrfC size_hop2InitBodyC size_hop2InitPrfC hop2InitImpl hop2InitBodyC_eval_and_inv hop2GameRed redCoinToPrf_hop2GameRed_prgCoinMode cost_hop2DlArmC cost_hop2IjArmC cost_hop2StepC hop2PrgRedKReal hop2PrgRedK hop2PrgRedK_totalQueries_zero hop2PrgRedK_totalCost_le hop2PrgRedK_size_raw_le hop2PrgRedK_size_le_of_clamp hop2PrgRedK_size_le hop2PrgRedK_gRedBounded_of_clamp hop2PrgRedK_gRedBounded_of_le hop2PrgRedK_gRedBounded hop2PrgRedK_gRedBounded_succ hop2PrgRedK_gRedBounded_tier1 hop2PrfRedKReal hop2PrfRedK hop2PrfRedK_totalQueries_le hop2PrfRedK_totalCost_le hop2PrfRedK_size_raw_le hop2PrfRedK_size_le_of_clamp hop2PrfRedK_size_le hop2PrfRedK_gRedBounded_of_clamp hop2PrfRedK_gRedBounded_of_le hop2PrfRedK_gRedBounded hop2PrfRedK_gRedBounded_succ hop2PrfRedK_gRedBounded_tier1
)
end Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg
-- AUTO-BRIDGE END

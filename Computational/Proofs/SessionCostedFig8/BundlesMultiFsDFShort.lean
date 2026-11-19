/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsSlot
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Specifications.Reductions.ReductionDsl.Core

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFShort

public section

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Expr Comp Ops Iface GameCodec CostedReduction
  UniformSamplerTag AtomicUnifBase OTCCATag FSAEADTag bits reductionSizeBudget
  AtomicSort AtomicBaseUnif atomicBaseSamplers unifSamplers
  atomicSig atomicFsOps atomicGroupOps atomicFig8Ops atomicSamplers
  coinOnlyBaseIface slotOtccaTargetIface fsaeadHeaderIface fig8SmCodec fig8SmCodecDF
  BV256 IdKey PlainT fig8HdrT fig8PubAdT lpubT wireSaltCtT lctT slotAdT
  fsSendStT fsRecvStT fsRrT
  salt32V salt32OfV wireSignalHdrV wireSignalHdrOfV lpubV lpubOfV
  wireSaltCtV wireSaltCtOfV lctV lctOfV fig8PubAdV fig8PubAdOfV
  slotAdV slotAdOfV fsSendStV fsSendStOfV fsRecvStV fsRecvStOfV fsRrEnc fsRrDec
  iterM findML anyML mapML consumeFirstML foldML
  liftRen atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun CKASamp)
open _root_.CryptoGames.PRFPRNG (prngSig prngSMCodec prngSMCodecDF fsaeadHeaderAdIface FSHdrTag)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.FSAEAD.Thm5 (hp)
open _root_.CryptoGames.SM.Construction (Header fsaeadMultiHeaderAdIface)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lPubOf lChainPRG lAeadR lIdeal)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession (LCt FsAdv pubToAD ratchetCostBudget GRedBounded)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (multiSessSpec)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec)
open _root_.CryptoVerification.E2E.Signed.SessionFSMix (lSessAdv)
open _root_.CryptoVerification.E2E.Signed.SessionWire (lWireSessAdv)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessFsAdv MultiSessPubFsAdv
  multiSessPubToAD RouterAdvCompat)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal guardRed guardRed_pos
  guardRed_gRedBounded)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (PureAuxBundle compCostW
  coinSimEquiv_liftP compilePureAuxRed compilePureAuxRed_totalCost_le
  compilePureAuxRed_totalQueries_le compilePureAuxRed_coinSimEquiv)
open Computational.Proofs.ReductionDsl.FsAtomicOps (clampedProtoSignalCodec lPubOfExpr
  env_get_zero env_get_succ)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (CoinSimEquiv atomicShortB compilePureExpr
  compilePureComp mapPureEnv compilePureExpr_eval compilePureComp_coinSimEquiv
  salt32OfV_salt32V salt32V_salt32OfV wireSignalHdrOfV_wireSignalHdrV
  wireSaltCtOfV_wireSaltCtV wireSaltCtV_wireSaltCtOfV
  lctOfV_lctV lctV_lctOfV fig8PubAdOfV_fig8PubAdV fig8PubAdV_fig8PubAdOfV
  slotAdOfV_slotAdV fsSendStOfV_fsSendStV fsRecvStOfV_fsRecvStV fsRrDec_fsRrEnc)
open Computational.Proofs.ReductionDsl.FsAtomicBundles (hybBaseTy swBaseTy prgZeroMacroBundle
  multiMacroBundle slotSwMacroBundle hybToDen swToDen)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC ckaSampC)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound)
open Computational.Proofs.SessionCostedFig8.QuerySubsumes (QuerySubsumes)
open Computational.Proofs.SessionCostedFig8.BundlesAdapters (fSortCKA toDenCKA
  ckaToFig8Adapters ckaDFToFig8Adapters fig8SplitIn_eval fig8AdaptQ_eval_cka
  fig8AdaptR_eval_cka fig8AdaptQDF_eval_cka fig8AdaptRDF_eval_cka)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow
  fsSampMacro ckaOpMacro sampBV256Atomic sampBV256Atomic_evalDistEq ckaOpMacro_eval)
open Computational.Proofs.SessionCostedFig8.BundlesAuxSize (compSizeW ckaOpS ckaSampS)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase (
  fsMultiQueryC fsMultiQueryC_tr fsMultiQueryC_ch fsMultiQueryC_cs fsMultiQueryC_cr
  fsMultiQueryC_dl fsMultiQueryC_ij fsMultiQueryS fsMultiQueryS_apply projSessPubFsAdv
  exprWk1 liftEnv1 liftEnv2 liftEnvFst liftEnvFold liftEnvPred2 liftEnvMk3 substExpr
  expr_renameM_cost exprWk1_cost expr_cost_pos envMap_liftEnv1_cost envMap_liftEnv2_cost
  substExpr_cost_le substNoQueryComp renEmpty renId1 renId2 renSwap2 renUnit2 envId1
  envFst2 envSwapFst2 callBinaryComp substQueryComp substQueryRed evalEnvMap envGet_evalEnvMap
  envRen envGet_envRen envRen_succ envRen_liftRen expr_renameM_eval envRen_id envRen_var_succ
  exprWk1_eval evalEnvMap_wk1 evalEnvMap_liftEnv1 evalEnvMap_liftEnv2 evalEnvMap_liftEnvFst
  evalEnvMap_liftEnvFold evalEnvMap_liftEnvPred2 evalEnvMap_liftEnvMk3 substExpr_eval
  comp_renameM_eval callBinaryComp_eval simulateQ_run_iterM simulateQ_run_foldML
  foldML_pure_cons reverse_reverseAux foldML_find_some foldML_any_true foldML_consume_true
  simulateQ_run_findML simulateQ_run_anyML stateT_run_pure stateT_run_lift simulateQ_run_mapML_aux
  simulateQ_run_consumeFirstML_aux simulateQ_run_iterM_const simulateQ_run_foldML_const
  simulateQ_run_findML_const simulateQ_run_anyML_const simulateQ_run_mapML_const
  simulateQ_run_consumeFirstML_const listElemTy compRetTy substNoQueryComp_eval substQueryComp_eval
  substQueryRed_eval compListMNodes comp_renameM_cost comp_renameM_queries callBinaryComp_cost
  callBinaryComp_queries envMap_liftEnvFst_cost envMap_liftEnvFold_cost envMap_liftEnvPred2_cost
  envMap_liftEnvMk3_cost envId1_cost envFst2_cost envSwapFst2_cost substNoQueryComp_queries
  comp_cost_pos substNoQueryComp_cost_le substQueryComp_queries_le findM_cost_arith
  anyM_cost_arith mapM_cost_arith consumeFirstM_cost_arith substQueryComp_cost_le
  substQueryRed_totalQueries_le substQueryRed_totalCost_le liftFsExpr liftBaseSamp
  liftFsCoinComp liftFsSlotComp liftNoQuerySlotComp liftFsExpr_cost liftBaseSamp_cost
  liftBaseSamp_queries liftFsCoinComp_cost liftFsCoinComp_queries liftFsSlotComp_cost
  liftFsSlotComp_queries liftNoQuerySlotComp_cost liftNoQuerySlotComp_queries liftFsExpr_eval
  coinOnlyBaseIface_liftP liftBaseSamp_eval iterM_liftP findML_liftP anyML_liftP
  mapML_liftP consumeFirstML_liftP foldML_liftP liftFsCoinComp_eval coinSimEquiv_liftP_pure
  coinSimEquiv_liftP_map coinSimEquiv_liftP_bind_of_support coinSimEquiv_liftP_map_bind_of_support
  hybSessStTy saltSlotStAtomTy initHybSessStExpr emptySaltSlotAtomExpr realTrStep
  realChStep realCsStep realCrStep realDlStep realIjStep slotOtccaImpl slotSessStTy
  liftSlotHybStep slotTrStep slotChStep slotCsStep slotCrStep slotDlStep slotIjStep
  realEntryTy slotEntryTy routerStTy initRouterStExpr ensureSessInit initRealSessComp
  initSlotSessComp mapRrWithPubExpr runLazyPubSess toFsTag routerQueryMacro fsaeadMultiAtomicIface
  fsMultiSampMacro fsMultiPureAuxBundle compileFsMultiAtomic compileFsMultiDFAtomic)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsSlot (compileFsMultiAtomic_encMsgsOk_base compileFsMultiAtomic_guardedFSInjectShort_base compileFsMultiAtomic_isQueryBoundP_base compileFsMultiAtomic_makesAtMostQueries_base compileFsMultiDFAtomic_encMsgsOk_base compileFsMultiDFAtomic_guardedFSInjectShort_base compileFsMultiDFAtomic_isQueryBoundP_base compileFsMultiDFAtomic_makesAtMostQueries_base)

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

theorem compileFsMultiDFAtomic_encMsgsOk (stage la : Bool) (j qep qR B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (Pmsg : LibsignalMsgPublicPart × Plain ℓ → Bool)
    (hOk : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, q⟩ => decide (s = j) &&
            CryptoGames.FSAEAD.encBadMsg
              (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
              (AD := Header Pt) (C := ℕ × LCt) Pmsg (.inr q)) = true) 0) :
    CryptoGames.FSAEAD.EncMsgsOk Pmsg
      ((compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
        (fun _ => A) ()) := by
  exact compileFsMultiDFAtomic_encMsgsOk_base
    ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R A Pmsg hOk


/-- `GuardedFSInjectShort` transfer from `GuardedMultiInjectShort` on `R.eval` to `compileFsMultiDFAtomic`. -/
theorem compileFsMultiDFAtomic_guardedFSInjectShort (stage la : Bool) (j qep qR B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hG : CryptoVerification.E2E.Signed.SessionWireQueries.GuardedMultiInjectShort
      (R.eval (fun _ => A) ())) :
    CryptoGames.Ratchet.LibsignalInst.GuardedFSInjectShort
      ((compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
        (fun _ => A) ()) := by
  exact compileFsMultiDFAtomic_guardedFSInjectShort_base
    ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R A hG
end

end Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFShort

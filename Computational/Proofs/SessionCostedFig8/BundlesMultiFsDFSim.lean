/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsEval
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsSlot
import Computational.Proofs.HeadlineV1.Stage2RouterHelpers
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Specifications.Reductions.ReductionDsl.Core

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFSim

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
  wireSaltCtV wireSaltCtOfV lctV lctOfV fig8PubAdOfV fig8PubAdV
  slotAdOfV slotAdV fsSendStOfV fsSendStV fsRecvStOfV fsRecvStV fsRrEnc fsRrDec
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
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (LCt FsAdv pubToAD ratchetCostBudget GRedBounded)
open CryptoVerification.E2E.Signed.SessionRouter (multiSessSpec)
open CryptoVerification.E2E.Signed.SessionFS (fsSpec)
open CryptoVerification.E2E.Signed.SessionFSMix (lSessAdv)
open CryptoVerification.E2E.Signed.SessionWire (lWireSessAdv)
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
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase (anyML_liftP anyM_cost_arith callBinaryComp callBinaryComp_cost callBinaryComp_eval callBinaryComp_queries coinOnlyBaseIface_liftP coinSimEquiv_liftP_bind_of_support coinSimEquiv_liftP_map coinSimEquiv_liftP_map_bind_of_support coinSimEquiv_liftP_pure compListMNodes compNodes compQueryCount compRetTy comp_cost_pos comp_renameM_cost comp_renameM_eval comp_renameM_queries compileFsMultiAtomic compileFsMultiDFAtomic consumeFirstML_liftP consumeFirstM_cost_arith emptySaltSlotAtomExpr ensureSessInit envFst2 envFst2_cost envGet_envRen envGet_evalEnvMap envId1 envId1_cost envMap_liftEnv1_cost envMap_liftEnv2_cost envMap_liftEnvFold_cost envMap_liftEnvFst_cost envMap_liftEnvMk3_cost envMap_liftEnvPred2_cost envRen envRen_id envRen_liftRen envRen_succ envRen_var_succ envSwapFst2 envSwapFst2_cost evalEnvMap evalEnvMap_liftEnv1 evalEnvMap_liftEnv2 evalEnvMap_liftEnvFold evalEnvMap_liftEnvFst evalEnvMap_liftEnvMk3 evalEnvMap_liftEnvPred2 evalEnvMap_wk1 exprWk1 exprWk1_cost exprWk1_eval expr_cost_pos expr_renameM_cost expr_renameM_eval findML_liftP findM_cost_arith foldML_any_true foldML_consume_true foldML_find_some foldML_liftP foldML_pure_cons fsMultiPureAuxBundle fsMultiQueryC fsMultiQueryC_ch fsMultiQueryC_cr fsMultiQueryC_cs fsMultiQueryC_dl fsMultiQueryC_ij fsMultiQueryC_tr fsMultiQueryS fsMultiQueryS_apply fsMultiSampMacro fsaeadMultiAtomicIface hybSessStTy initHybSessStExpr initRealSessComp initRouterStExpr initSlotSessComp iterM_liftP liftBaseSamp liftBaseSamp_cost liftBaseSamp_eval liftBaseSamp_queries liftEnv1 liftEnv2 liftEnvFold liftEnvFst liftEnvMk3 liftEnvPred2 liftFsCoinComp liftFsCoinComp_cost liftFsCoinComp_eval liftFsCoinComp_queries liftFsExpr liftFsExpr_cost liftFsExpr_eval liftFsSlotComp liftFsSlotComp_cost liftFsSlotComp_queries liftNoQuerySlotComp liftNoQuerySlotComp_cost liftNoQuerySlotComp_queries liftSlotHybStep listElemTy mapML_liftP mapM_cost_arith mapRrWithPubExpr projSessPubFsAdv realChStep realCrStep realCsStep realDlStep realEntryTy realIjStep realTrStep renEmpty renId1 renId2 renSwap2 renUnit2 reverse_reverseAux routerQueryMacro routerStTy runLazyPubSess saltSlotStAtomTy simulateQ_run_anyML simulateQ_run_anyML_const simulateQ_run_consumeFirstML_aux simulateQ_run_consumeFirstML_const simulateQ_run_findML simulateQ_run_findML_const simulateQ_run_foldML simulateQ_run_foldML_const simulateQ_run_iterM simulateQ_run_iterM_const simulateQ_run_mapML_aux simulateQ_run_mapML_const slotChStep slotCrStep slotCsStep slotDlStep slotEntryTy slotIjStep slotOtccaImpl slotSessStTy slotTrStep stateT_run_lift stateT_run_pure substExpr substExpr_cost_le substExpr_eval substNoQueryComp substNoQueryComp_cost_le substNoQueryComp_eval substNoQueryComp_queries substQueryComp substQueryComp_cost_le substQueryComp_eval substQueryComp_queries_le substQueryRed substQueryRed_eval substQueryRed_totalCost_le substQueryRed_totalQueries_le toFsTag)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsEval (FsPubSpec coinSimEquiv_pubToAD compileFsMultiAtomic_eval_coinSimEquiv compileFsMultiDFAtomic_eval_coinSimEquiv dslRouterImpl dslRouter_coinSimEquiv qIsCr qIsShortBad qOnSess)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsSlot (compileFsMultiAtomic_encMsgsOk_base compileFsMultiAtomic_guardedFSInjectShort_base compileFsMultiAtomic_isQueryBoundP_base compileFsMultiAtomic_makesAtMostQueries_base compileFsMultiDFAtomic_encMsgsOk_base compileFsMultiDFAtomic_guardedFSInjectShort_base compileFsMultiDFAtomic_isQueryBoundP_base compileFsMultiDFAtomic_makesAtMostQueries_base)
open Computational.Proofs.HeadlineV1.Stage2RouterHelpers (lPubSessAdv lPubWireSessAdv pubToAD_lPubSessAdv_eq pubToAD_lPubWireSessAdv_eq)

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

/-- `CoinSimEquiv` between `pubToAD protoSignalCodec` of `(compileFsMultiDFAtomic ...).eval` and the
session router adversary `lSessAdv` (`stage = false`) / `lWireSessAdv` (`stage = true`) on
`multiSessPubToAD protoSignalCodec (R.eval (fun _ => A) ())`. -/
theorem compileFsMultiDFAtomic_coinSimEquiv
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (stage la : Bool) (j qep qR B0 : ℕ)
    (hj : j ≤ (qep + 2) * B0 + B0 * B0) (hqR : qR ≤ B0)
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
    (hSimQ : ∀ s ≠ j,
      (R.eval (fun _ => A) ()).IsQueryBoundP
        (fun t => (match t with
          | .inl _ => false
          | .inr ⟨s', _⟩ => decide (s' = s)) = true) (2 * qR + 4))
    (hNoCr : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inr ⟨_, .inl (.inl (.inr _))⟩ => true
        | _ => false) = true) 0)
    (hShort : ∀ s ≠ j,
      (R.eval (fun _ => A) ()).IsQueryBoundP
        (fun t => (match t with
          | .inl _ => false
          | .inr ⟨s', q⟩ => decide (s' = s) &&
              CryptoGames.FSAEAD.encBadMsg
                (SS := RatchetSenderState (BitVec 256))
                (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                (AD := Header Pt) (C := ℕ × LCt)
                (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr q)) = true) 0) :
    let Adv : Unit → MultiSessFsAdv Pt ℓ :=
      fun _ => multiSessPubToAD protoSignalCodec (R.eval (fun _ => A) ())
    let cut := authHopCutoff maxForwardJumps qR la
    CoinSimEquiv
      (fun n => query (spec := unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      (pubToAD protoSignalCodec
        ((compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
          (fun _ => A) ()))
      (if stage then
        lWireSessAdv C protoSignalCodec ℓ encT (fun _ => idOf) maxForwardJumps cut la Adv
          (hp cut cut la) () j
      else
        lSessAdv C protoSignalCodec ℓ encT (fun _ => idOf) maxForwardJumps cut la Adv () j) := by
  intro Adv cut
  let M : MultiSessPubFsAdv Pt ℓ := R.eval (fun _ => A) ()
  have h₁ := compileFsMultiDFAtomic_eval_coinSimEquiv
    ℓ Pt C Dh encPt encT idOf lam hℓ stage la j qep qR B0 hj hqR R A
  have hSimQ' : ∀ s ≠ j, M.IsQueryBoundP (fun t => qOnSess ℓ Pt s t = true) (2 * qR + 4) := by
    intro s hs
    exact (hSimQ s hs).of_imp (by rintro (_ | ⟨_, _⟩) h <;> exact h)
  have hNoCr' : M.IsQueryBoundP (fun t => qIsCr ℓ Pt t = true) 0 := by
    exact hNoCr.of_imp (by rintro (_ | ⟨_, ((_ | _) | _) | _⟩) h <;> exact h)
  have hShort' : ∀ s ≠ j, M.IsQueryBoundP (fun t => qIsShortBad ℓ Pt s t = true) 0 := by
    intro s hs
    exact (hShort s hs).of_imp (by rintro (_ | ⟨_, _⟩) h <;> exact h)
  have h₂ := coinSimEquiv_pubToAD (ℓ := ℓ) (Pt := Pt)
    (dslRouter_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj stage la j qR M
      hSimQ' hNoCr' hShort')
  have h₃ :
      pubToAD protoSignalCodec
        (if stage then
          lPubWireSessAdv C protoSignalCodec ℓ encT (fun _ => idOf) maxForwardJumps cut la
            (fun _ => M) (hp cut cut la) () j
        else
          lPubSessAdv C protoSignalCodec ℓ encT (fun _ => idOf) maxForwardJumps cut la
            (fun _ => M) () j) =
      (if stage then
        lWireSessAdv C protoSignalCodec ℓ encT (fun _ => idOf) maxForwardJumps cut la Adv
          (hp cut cut la) () j
      else
        lSessAdv C protoSignalCodec ℓ encT (fun _ => idOf) maxForwardJumps cut la Adv () j) := by
    cases stage
    · exact pubToAD_lPubSessAdv_eq C protoSignalCodec ℓ encT (fun _ => idOf)
        maxForwardJumps cut la (fun _ => M) () j
    · exact pubToAD_lPubWireSessAdv_eq C protoSignalCodec ℓ encT (fun _ => idOf)
        maxForwardJumps cut la (fun _ => M) (hp cut cut la) () j
  exact h₁.trans (h₂.trans (CoinSimEquiv.of_eq h₃))

/-- Packaged `RouterAdvCompat` across `(stage, la, j)` for any `oa : ProbComp α` family of
`compileFsMultiAtomic`-lowered reductions. -/

theorem compileFsMultiDFAtomic_routerAdvCompat {α : Type}
    (oa : ProbComp α)
    (idOfF : α → Party → IdentityKey) (lamF : α → Pt)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (qep qR M B0 : ℕ)
    (hMB0 : M ≤ (qep + 2) * B0 + B0 * B0 + 1) (hqR : qR ≤ B0)
    (R : Bool → α →
      (o : α) → CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT (idOfF o) (lamF o) B0)
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
    (A : α → OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hSimQ : ∀ la o, o ∈ support oa → ∀ s,
      ((R la o o).eval (fun _ => A o) ()).IsQueryBoundP
        (fun t => (match t with
          | .inl _ => false
          | .inr ⟨s', _⟩ => decide (s' = s)) = true) (2 * qR + 4))
    (hNoCr : ∀ la o, o ∈ support oa →
      ((R la o o).eval (fun _ => A o) ()).IsQueryBoundP
        (fun t => (match t with
          | .inr ⟨_, .inl (.inl (.inr _))⟩ => true
          | _ => false) = true) 0)
    (hShort : ∀ la o, o ∈ support oa → ∀ s,
      ((R la o o).eval (fun _ => A o) ()).IsQueryBoundP
        (fun t => (match t with
          | .inl _ => false
          | .inr ⟨s', q⟩ => decide (s' = s) &&
              CryptoGames.FSAEAD.encBadMsg
                (SS := RatchetSenderState (BitVec 256))
                (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                (AD := Header Pt) (C := ℕ × LCt)
                (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr q)) = true) 0) :
    RouterAdvCompat C protoSignalCodec ℓ encT oa idOfF maxForwardJumps qR M
      (fun la o => multiSessPubToAD protoSignalCodec ((R la o o).eval (fun _ => A o) ()))
      (fun stage la j o =>
        (compileFsMultiDFAtomic ℓ Pt C Dh encPt encT (idOfF o) (lamF o) stage la j qep qR B0
          (R la o o)).eval (fun _ => A o) ()) := by
  exact
    { saltCompat := fun la j hj o ho =>
        compileFsMultiDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT (idOfF o) (lamF o)
          hℓ hinj false la j qep qR B0 (by omega) hqR (R la o o) (A o)
          (fun s _ => hSimQ la o ho s) (hNoCr la o ho) (fun s _ => hShort la o ho s)
      wireCompat := fun la j hj o ho =>
        compileFsMultiDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT (idOfF o) (lamF o)
          hℓ hinj true la j qep qR B0 (by omega) hqR (R la o o) (A o)
          (fun s _ => hSimQ la o ho s) (hNoCr la o ho) (fun s _ => hShort la o ho s) }

end

end Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFSim

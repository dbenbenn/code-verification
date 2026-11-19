/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsRouterCostA
import Computational.Proofs.SessionCostedFig8.BundlesAdapters
import Computational.Proofs.SessionCostedFig8.BundlesCompilers
import Computational.Proofs.SessionCostedFig8.BundlesAuxSize
import Computational.Proofs.ReductionDsl.FsAtomicBundles
import Computational.Proofs.ReductionDsl.FsAtomicBoundsStage
import Computational.Proofs.ReductionDsl.Fig8Atomic
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.ReductionDsl.FsAtomicOps
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.FSAEAD.HybridCosted
import Computational.Proofs.ReductionDsl.FSAEAD.HybridInv
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedBase
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWireCosted
import Computational.Proofs.ReductionDsl.SM.Engine
import Computational.Proofs.E2E.SessionAuthQueries
import Computational.Proofs.HeadlineV1.Stage2RouterHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Specifications.Reductions.ReductionDsl.Core

public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Expr Comp Ops Iface GameCodec CostedReduction
  UniformSamplerTag AtomicUnifBase OTCCATag FSAEADTag bits reductionSizeBudget
  atomicSig atomicFsOps atomicGroupOps atomicFig8Ops atomicSamplers
  coinOnlyBaseIface slotOtccaTargetIface fsaeadHeaderIface fig8SmCodec fig8SmCodecDF
  BV256 IdKey PlainT fig8HdrT fig8PubAdT lpubT wireSaltCtT lctT slotAdT
  fsSendStT fsRecvStT fsRrT
  lpubV lpubOfV lctV lctOfV fsSendStV fsSendStOfV fsRecvStV fsRecvStOfV fsRrEnc fsRrDec
  iterM findML anyML mapML consumeFirstML foldML
  liftRen atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun CKASamp)
open CryptoGames.PRFPRNG (prngSig prngSMCodec prngSMCodecDF fsaeadHeaderAdIface FSHdrTag)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open CryptoGames.FSAEAD.Thm5 (hp)
open CryptoGames.SM.Construction (Header fsaeadMultiHeaderAdIface)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lPubOf lChainPRG lAeadR lIdeal)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (LCt FsAdv pubToAD ratchetCostBudget GRedBounded)
open CryptoVerification.E2E.Signed.SessionRouter (multiSessSpec)
open CryptoVerification.E2E.Signed.SessionFS (fsSpec)
open CryptoVerification.E2E.Signed.SessionFSMix (lSessAdv)
open CryptoVerification.E2E.Signed.SessionWire (lWireSessAdv)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessFsAdv MultiSessPubFsAdv
  multiSessPubToAD RouterAdvCompat)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (PureAuxBundle compCostW
  coinSimEquiv_liftP compilePureAuxComp compilePureAuxRed compilePureAuxRed_totalCost_le
  compilePureAuxRed_totalQueries_le compilePureAuxRed_coinSimEquiv)
open Computational.Proofs.ReductionDsl.FsAtomicOps (clampedProtoSignalCodec lPubOfExpr)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (CoinSimEquiv atomicShortB compilePureExpr
  compilePureComp)
open Computational.Proofs.ReductionDsl.FsAtomicBundles (hybBaseTy swBaseTy prgZeroMacroBundle
  multiMacroBundle slotSwMacroBundle)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC ckaSampC)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound)
open Computational.Proofs.SessionCostedFig8.QuerySubsumes (QuerySubsumes)
open Computational.Proofs.SessionCostedFig8.BundlesAdapters (fSortCKA toDenCKA
  ckaToFig8Adapters ckaDFToFig8Adapters fig8SplitIn_eval fig8AdaptQ_eval_cka
  fig8AdaptR_eval_cka fig8AdaptQDF_eval_cka fig8AdaptRDF_eval_cka)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow
  fsSampMacro ckaOpMacro sampBV256Atomic sampBV256Atomic_evalDistEq ckaOpMacro_eval)
open Computational.Proofs.SessionCostedFig8.BundlesAuxSize (exprSizeW compSizeW ckaOpS ckaSampS)
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
  substQueryRed_eval compListMNodes compQueryCount comp_renameM_cost comp_renameM_queries callBinaryComp_cost
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
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsRouterCostA
  (compileFsMultiAtomic_size_le compileFsMultiDFAtomic_size_le compileFsMulti_dflt_size_le)

namespace Computational.Proofs.SessionCostedFig8.BundlesMultiFsRouterCostB

/-! ## 9. Concrete Router Cost & Query Bounds + `GRedBounded` (`#1–#2`) -/

section RouterCostBounds

private theorem one_le_exprSizeW {S : Sig} {O : Ops S} (opS : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) : 1 ≤ exprSizeW opS e := by
  induction e with
  | nat n => exact ReductionDsl.one_le_bits n
  | op o a iha => simp only [exprSizeW]; omega
  | _ => simp only [exprSizeW]; omega

@[local simp] private theorem compListMNodes_renameM {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u)
    {t : Ty S} (c : Comp O I Γ t) :
    compListMNodes (c.renameM ξ) = compListMNodes c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compListMNodes, *]

private theorem three_mul_compListMNodes_le_compSizeW {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    3 * compListMNodes c ≤ compSizeW opS sS qS c := by
  induction c with
  | findM K l p ih | anyM K l p ih | mapM K l p ih =>
    have hl := one_le_exprSizeW opS l
    have hk := ReductionDsl.one_le_bits K
    simp only [compListMNodes, compSizeW]; omega
  | consumeFirstM K l p mk ih =>
    have hl := one_le_exprSizeW opS l
    have hmk := one_le_exprSizeW opS mk
    have hk := ReductionDsl.one_le_bits K
    simp only [compListMNodes, compSizeW]; omega
  | _ => simp only [compListMNodes, compSizeW]; omega

private theorem compListMNodes_compilePureAuxComp_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (hSamp : ∀ s, compListMNodes (M.sampMacro s) = 0)
    (hQuery : ∀ g, compListMNodes (M.queryMacro g) = 0)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    compListMNodes (compilePureAuxComp M c) ≤ compListMNodes c := by
  induction c with
  | sample s e =>
    simp only [compilePureAuxComp, compListMNodes,
      Computational.Proofs.ReductionDsl.MacroLift.callMacroAux, compListMNodes_renameM, hSamp s]
    omega
  | query g e =>
    simp only [compilePureAuxComp, compListMNodes,
      Computational.Proofs.ReductionDsl.MacroLift.callMacroAux, compListMNodes_renameM, hQuery g]
    omega
  | _ => simp only [compilePureAuxComp, compListMNodes]; omega

private theorem ite_fallback_gRedBounded {P : Prop} [Decidable P]
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {dfltRTy₁ dfltRTy₂ : Ty S}
    (realR : CostedReduction O I G C .unit .unit .bool .bool)
    (dfltAIn : Expr O [] .unit) (dfltRCostE : Expr O [] dfltRTy₁) (dfltOut : Expr O [] .bool)
    (dfltRSizeE : Expr O [] dfltRTy₂)
    {dfltR_ctx : Expr O [.unit, C.Q] C.R}
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ)
    (hCostPos : P → realR.totalCost q ≤ costBudget)
    (hCostNeg :
      (dfltAIn.cost + 3) + q * max I.uCost (dfltRCostE.cost + 3 + C.codecCost) +
        (dfltOut.cost + 1) ≤ costBudget)
    (hSizePos : P → realR.size ≤ reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hSizeNeg :
      (dfltAIn.size + 3) + (dfltRSizeE.size + 3) + (dfltOut.size + 1) ≤ reductionSizeBudget)
    (hQueriesPos : P → realR.totalQueries wTag wSamp q ≤ qOut)
    (hO : ReductionDsl.OpsSizeHonest O)
    (hS : ReductionDsl.SampSizeHonest I.smp)
    (hdfltAIn : dfltAIn = .unit := by rfl)
    (hdfltOut : dfltOut = .bool false := by rfl)
    (hdfltRCost : dfltR_ctx.cost = dfltRCostE.cost := by rfl)
    (hdfltRSize : dfltR_ctx.size = dfltRSizeE.size := by rfl) :
    GRedBounded
      (if P then realR else
        { σ := .unit
          init := .ret (.pair .unit .unit)
          handle := .ret (.pair dfltR_ctx .unit)
          finish := .ret (.bool false) })
      wTag wSamp q qOut costBudget := by
  subst hdfltAIn; subst hdfltOut
  split_ifs with hP
  · exact CryptoVerification.E2E.Costed.gRedBounded_of_bounds realR wTag wSamp q qOut costBudget
      (hCostPos hP) (hSizePos hP) (hQueriesPos hP) hO hS
  · apply CryptoVerification.E2E.Costed.gRedBounded_of_bounds
    · simp only [CostedReduction.totalCost, Comp.cost, Expr.cost] at hCostNeg ⊢
      rw [hdfltRCost]
      have hmx : max I.uCost ((dfltRCostE.cost + 1 + 1) + 1 + C.codecCost) ≤
          max I.uCost (dfltRCostE.cost + 3 + C.codecCost) :=
        max_le_max_left _ (by omega)
      have hmul := Nat.mul_le_mul_left q hmx
      omega
    · simp only [CostedReduction.size, Comp.size, Expr.size] at hSizeNeg ⊢
      rw [hdfltRSize]
      omega
    · simp only [CostedReduction.totalQueries, Comp.queries]
      exact Nat.zero_le qOut
    · exact hO
    · exact hS

private def compHasListMOrFold {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} : Comp O I Γ t → Bool
  | .ret _ | .sample _ _ | .query _ _ => false
  | .bind c k | .ite _ c k | .caseOpt _ c k | .caseSum _ c k =>
    compHasListMOrFold c || compHasListMOrFold k
  | .iter _ _ body => compHasListMOrFold body
  | .foldM _ _ _ _ | .findM _ _ _ | .anyM _ _ _ | .mapM _ _ _ | .consumeFirstM _ _ _ _ => true

private def compSimpleOvh {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} : Comp O I Γ t → ℕ
  | .ret _ => 1
  | .bind c k => compSimpleOvh c + compSimpleOvh k + 1
  | .ite _ c d | .caseOpt _ c d | .caseSum _ c d => max (compSimpleOvh c) (compSimpleOvh d) + 1
  | .sample _ _ => 5
  | .query _ _ => 8
  | .iter n _ body => n * (compSimpleOvh body + 1)
  | .foldM _ _ _ _ | .findM _ _ _ | .anyM _ _ _ | .mapM _ _ _ | .consumeFirstM _ _ _ _ => 0

private theorem substQueryComp_simple_cost_le {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {rStTy : Ty S}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).cost ≤ e.cost + I₁.smp.sCost s + 1)
    {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2)
    (rExpr : Expr O Δ rStTy)
    (c : Comp O I₁ Γ t) (hSimple : compHasListMOrFold c = false) :
    (substQueryComp mapSamp qImpl envMap rExpr c).cost ≤
      2 * c.cost + rExpr.cost + compSimpleOvh c +
        c.queries (fun g => (qImpl g).cost + 8) (fun _ => 0) := by
  induction c generalizing Δ with
  | ret e =>
    have he := substExpr_cost_le envMap hEnv e
    simp only [substQueryComp, Comp.cost, Expr.cost, compSimpleOvh, Comp.queries]; omega
  | bind c k ihc ihk =>
    simp only [compHasListMOrFold, Bool.or_eq_false_iff] at hSimple
    have hc := ihc envMap hEnv rExpr hSimple.1
    have hk := ihk (liftEnvFst envMap) (envMap_liftEnvFst_cost hEnv) (.snd (.var .zero)) hSimple.2
    simp only [substQueryComp, Comp.cost, Expr.cost, compSimpleOvh, Comp.queries] at hc hk ⊢
    omega
  | ite b c d ihc ihd =>
    simp only [compHasListMOrFold, Bool.or_eq_false_iff] at hSimple
    have hb := substExpr_cost_le envMap hEnv b
    have hc := ihc envMap hEnv rExpr hSimple.1
    have hd := ihd envMap hEnv rExpr hSimple.2
    simp only [substQueryComp, Comp.cost, compSimpleOvh, Comp.queries]; omega
  | caseOpt e n s ihn ihs =>
    simp only [compHasListMOrFold, Bool.or_eq_false_iff] at hSimple
    have he := substExpr_cost_le envMap hEnv e
    have hn := ihn envMap hEnv rExpr hSimple.1
    have hs := ihs (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (exprWk1 rExpr) hSimple.2
    simp only [substQueryComp, Comp.cost, exprWk1_cost, compSimpleOvh, Comp.queries] at hs ⊢
    omega
  | caseSum e l r ihl ihr =>
    simp only [compHasListMOrFold, Bool.or_eq_false_iff] at hSimple
    have he := substExpr_cost_le envMap hEnv e
    have hl := ihl (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (exprWk1 rExpr) hSimple.1
    have hr := ihr (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (exprWk1 rExpr) hSimple.2
    simp only [substQueryComp, Comp.cost, exprWk1_cost, compSimpleOvh, Comp.queries] at hl hr ⊢
    omega
  | sample s e =>
    have he := substExpr_cost_le envMap hEnv e
    have hs := hSamp s (substExpr envMap e)
    simp only [substQueryComp, Comp.cost, Expr.cost, exprWk1_cost, compSimpleOvh, Comp.queries]
    omega
  | query g e =>
    have he := substExpr_cost_le envMap hEnv e
    simp only [substQueryComp, Comp.cost, Expr.cost, callBinaryComp_cost, compSimpleOvh,
      Comp.queries]
    omega
  | iter n e body ih =>
    simp only [compHasListMOrFold] at hSimple
    have he := substExpr_cost_le envMap hEnv e
    have hb := ih (liftEnvFst envMap) (envMap_liftEnvFst_cost hEnv) (.snd (.var .zero)) hSimple
    simp only [Expr.cost] at hb
    set qf : I₁.Tag → ℕ := fun g => (qImpl g).cost + 8
    have hm : n * ((substQueryComp mapSamp qImpl (liftEnvFst envMap) (.snd (.var .zero)) body).cost + 1) ≤
        n * (2 * (body.cost + 1) + (compSimpleOvh body + 1) + body.queries qf (fun _ => 0)) :=
      Nat.mul_le_mul_left n (by omega)
    have hr : n * (2 * (body.cost + 1) + (compSimpleOvh body + 1) + body.queries qf (fun _ => 0)) =
        2 * (n * (body.cost + 1)) + n * (compSimpleOvh body + 1) +
          n * body.queries qf (fun _ => 0) := by ring
    simp only [substQueryComp, Comp.cost, Expr.cost, compSimpleOvh, Comp.queries]; omega
  | foldM _ _ _ _ | findM _ _ _ | anyM _ _ _ | mapM _ _ _ | consumeFirstM _ _ _ _ =>
    simp [compHasListMOrFold] at hSimple

private theorem compHasListMOrFold_renameM {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) (c : Comp O I Γ t) :
    compHasListMOrFold (c.renameM f) = compHasListMOrFold c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compHasListMOrFold, *]

private theorem compSimpleOvh_renameM {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) (c : Comp O I Γ t) :
    compSimpleOvh (c.renameM f) = compSimpleOvh c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compSimpleOvh, *]

private theorem compHasListMOrFold_liftFsSlotComp {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)}
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    compHasListMOrFold (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c) =
      compHasListMOrFold c := by
  induction c <;> simp [liftFsSlotComp, compHasListMOrFold, *]

private theorem compSimpleOvh_liftFsSlotComp {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)}
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    compSimpleOvh (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c) =
      compSimpleOvh c := by
  induction c <;> simp [liftFsSlotComp, compSimpleOvh, *]

private theorem compHasListMOrFold_compilePureComp {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : Computational.Proofs.ReductionDsl.FsAtomicMacros.PureMacroBundle O₁ O₂ I₁ I₂)
    (hSamp : ∀ s, compHasListMOrFold (M.sampMacro s) = false)
    (hQuery : ∀ g, compHasListMOrFold (M.queryMacro g) = false)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    compHasListMOrFold (compilePureComp M c) = compHasListMOrFold c := by
  induction c with
  | sample s _ =>
    simp [compilePureComp, compHasListMOrFold,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, compHasListMOrFold_renameM,
      hSamp s]
  | query g _ =>
    simp [compilePureComp, compHasListMOrFold,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, compHasListMOrFold_renameM,
      hQuery g]
  | _ => simp [compilePureComp, compHasListMOrFold, *]

private theorem compSimpleOvh_compilePureComp_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : Computational.Proofs.ReductionDsl.FsAtomicMacros.PureMacroBundle O₁ O₂ I₁ I₂)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    compSimpleOvh (compilePureComp M c) ≤
      compSimpleOvh c +
        c.queries (fun g => compSimpleOvh (M.queryMacro g))
          (fun s => compSimpleOvh (M.sampMacro s)) := by
  induction c with
  | ret _ => simp only [compilePureComp, compSimpleOvh, Comp.queries]; omega
  | bind _ _ ih1 ih2 => simp only [compilePureComp, compSimpleOvh, Comp.queries]; omega
  | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp only [compilePureComp, compSimpleOvh, Comp.queries]; omega
  | sample s _ =>
    simp only [compilePureComp, compSimpleOvh, Comp.queries,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, compSimpleOvh_renameM]
    omega
  | query g _ =>
    simp only [compilePureComp, compSimpleOvh, Comp.queries,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, compSimpleOvh_renameM]
    omega
  | iter n _ body ih =>
    set qM := fun g => compSimpleOvh (M.queryMacro g)
    set sM := fun s => compSimpleOvh (M.sampMacro s)
    have hm : n * (compSimpleOvh (compilePureComp M body) + 1) ≤
        n * ((compSimpleOvh body + 1) + body.queries qM sM) :=
      Nat.mul_le_mul_left n (by omega)
    have hr : n * ((compSimpleOvh body + 1) + body.queries qM sM) =
        n * (compSimpleOvh body + 1) + n * body.queries qM sM := by ring
    simp only [compilePureComp, compSimpleOvh, Comp.queries]; omega
  | foldM _ _ _ _ | findM _ _ _ | anyM _ _ _ | mapM _ _ _ | consumeFirstM _ _ _ _ =>
    simp [compilePureComp, compSimpleOvh]

private theorem comp_queries_mono {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {w₁ w₂ : I.Tag → ℕ} {s₁ s₂ : I.smp.Samp → ℕ}
    (hw : ∀ g, w₁ g ≤ w₂ g) (hs : ∀ s, s₁ s ≤ s₂ s)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    c.queries w₁ s₁ ≤ c.queries w₂ s₂ := by
  induction c with
  | ret _ => rfl
  | sample s _ => exact hs s
  | query g _ => exact hw g
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp only [Comp.queries]; omega
  | iter n _ _ ih | foldM n _ _ _ ih | findM n _ _ ih | anyM n _ _ ih
  | mapM n _ _ ih | consumeFirstM n _ _ _ ih =>
    simp only [Comp.queries]; exact Nat.mul_le_mul_left n ih

-- Verified tight router step & GRedBounded cost bounds
section HybTightCost

open _root_.CryptoGames.FSAEAD.Thm5.Costed (aeadDecE aeadEncE anyInTransitBody anyInTransitE appendKcE
  callC callE chainFromBody chainFromC challengeBody challsContainsBody challsContainsE
  corruptSenderBody decIdxBody deliverBody encIdxBody eqAdE eqCE eqME findInTransitBody
  findInTransitE genStepKcBody genUpToBody genUpToC hsB hsChalls hsCorrAt hsCorrKey hsEnded
  hsInTransit hsKeysT hsLastSent hsLf hsNKeys hsRecvIdx hsSkipped hsTy hsWin initHSE injectBody
  isCompromisedBody isCompromisedE isSomeE maxNatE mkHS orE prependNewSkippedBody prgGenE recAd
  recCt recIdx recMatchesE recMsg receiveBody removeFromTransitBody removeFromTransitE revealBody
  senderKeyBody skippedContainsE skippedRemoveBody skippedRemoveE stTy transmitBody withKcE
  withSkippedE)
open Computational.Proofs.ReductionDsl.FsAtomicBounds (exprCostBoundUB compCostBoundUB
  exprCostBound_le_UB compCostBound_le_UB hybOpCU prgSC multiSC multiQC swOpCU slotSwSC slotSwQC
  hybOpMacro_cost_le prgSampMacro_cost_le multiSampMacro_cost_le multiQueryMacro_cost_le
  swOpMacro_cost_le slotSwSampMacro_cost_le slotSwQueryMacro_cost_le
  slotSaltEncC_cost_le slotSaltDecC_cost_le bits_le_qR_add_15)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (compCostBound compilePureExpr_cost_le
  compilePureComp_cost_le compilePureComp_queries_le)

local macro "unfold_hyb_vars" : tactic =>
  `(tactic| try dsimp only [Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, Expr.v7])

private abbrev HSigR (Pt : Type) (ℓ : ℕ) :=
  CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt

private abbrev HSampR (Pt : Type) (ℓ : ℕ) :=
  ReductionDsl.unifSamplers (S := HSigR Pt ℓ) CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)

private def optPred {α : Type _} (o : Option α) (P : α → Prop) : Prop :=
  match o with
  | none => True
  | some f => P f

private lemma genUpToC_tight_ub_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    {sC : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ}
    (hsMK : sC (Sum.inr (UniformSamplerTag.base false)) ≤ 10)
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 10)
    {jPos qR : ℕ} (hj : jPos ≤ qR + 25002)
    (i : Expr _ Γ .nat) (s : Expr _ Γ stTy) :
    compCostBoundUB hybOpCU sC qC
      (genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos i s) ≤
      exprCostBoundUB hybOpCU i + exprCostBoundUB hybOpCU s + 23000000 + 2 * qR := by
  have hbJ := bits_le_qR_add_15 hj
  have hb1 : bits 1 = 1 := rfl
  have hstep : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (genStepKcBody (I₀ := I₀) (Γ := Δ)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1) ≤ 900 := by
    intro Δ
    dsimp only [genStepKcBody, appendKcE, prgGenE, Ops.sum,
      CryptoGames.PRG.Costed.prgOps, CryptoGames.OTCCA.Costed.otccaOps, Iface.withSamp]
    unfold_hyb_vars
    dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
    simp only [hb1]
    omega
  have hmfj : maxForwardJumps = 25000 := rfl
  dsimp only [genUpToC, genUpToBody, withKcE, hsNKeys, hsKeysT, callC]
  generalize hbs : genStepKcBody (I₀ := I₀)
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 (Γ := _) = bs
  have hstep' : compCostBoundUB hybOpCU sC qC bs ≤ 900 := by rw [← hbs]; exact hstep
  unfold_hyb_vars
  dsimp only [compCostBoundUB, exprCostBoundUB]
  simp only [hmfj]
  omega

private lemma genUpToC_simple_and_ovh {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    (jPos : ℕ) (i : Expr _ Γ .nat) (s : Expr _ Γ stTy) :
    compHasListMOrFold
      (genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos i s) = false ∧
    compSimpleOvh
      (genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos i s) ≤ 600000 := by
  have hmfj : maxForwardJumps = 25000 := rfl
  refine ⟨rfl, ?_⟩
  dsimp only [genUpToC, genUpToBody, genStepKcBody, callC, compSimpleOvh]
  simp only [hmfj]
  omega

private lemma genUpToC_queries_zero {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    (w : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ)
    {sO : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    (hsO : ∀ u, sO (Sum.inr u) ≤ 20)
    (jPos : ℕ) (i : Expr _ Γ .nat) (s : Expr _ Γ stTy) :
    (genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps jPos i s).queries w (fun _ => 0) = 0 ∧
    (genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps jPos i s).queries (fun _ => 20) sO ≤ 1000100 := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hstep0 : ∀ {Δ},
      (genStepKcBody (I₀ := I₀) (Γ := Δ)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1).queries
        w (fun _ => 0) = 0 := by
    intro Δ; dsimp only [genStepKcBody, Comp.queries]; omega
  have hstepO : ∀ {Δ},
      (genStepKcBody (I₀ := I₀) (Γ := Δ)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1).queries
        (fun _ => 20) sO ≤ 40 := by
    intro Δ
    have h1 := hsO (.base false)
    have h2 := hsO (.base true)
    dsimp only [genStepKcBody, Iface.withSamp, Comp.queries]
    omega
  dsimp only [genUpToC, genUpToBody, callC, Comp.queries]
  generalize hbs : genStepKcBody (I₀ := I₀)
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 (Γ := _) = bs
  have hs0 : bs.queries w (fun _ => 0) = 0 := by rw [← hbs]; exact hstep0
  have hs1 : bs.queries (fun _ => 20) sO ≤ 40 := by rw [← hbs]; exact hstepO
  rw [hs0, hmfj]
  refine ⟨rfl, ?_⟩
  generalize bs.queries (fun _ => 20) sO = bq at hs1 ⊢
  omega

private lemma decIdxBody_tight_ub_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    {sC : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ}
    {mSlot qR : ℕ} (hm : mSlot ≤ qR + 25002)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hDec : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ exprCostBoundUB hybOpCU x + 70000)) :
    compCostBoundUB hybOpCU sC qC
      (decIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
        (Γ := Γ)) ≤ 600000 + 2 * qR := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hbM := bits_le_qR_add_15 hm
  dsimp only [decIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt, aeadDecE, callE]
  cases specialDec with
  | none =>
    unfold_hyb_vars
    dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
    simp only [hb0, hb1]; omega
  | some sD =>
    have hs := hDec (Δ := .prod (.prod (.opt (CryptoGames.FSAEAD.Costed.bt .msg))
      (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (CryptoGames.FSAEAD.Costed.bt .ct)))) hsTy :: Γ)
      (.pair (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))
        (.snd (.snd (.snd (.fst .v0)))))
    dsimp only [Expr.v0, exprCostBoundUB] at hs
    unfold_hyb_vars
    dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
    simp only [hb0, hb1]
    generalize hsdx : compCostBoundUB hybOpCU sC qC (sD _) = sdx at hs ⊢
    omega

private lemma encIdxBody_tight_ub_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    {sC : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ}
    {mSlot qR : ℕ} (hm : mSlot ≤ qR + 25002)
    (sampleIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _)
    (specialEnc : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hId : ∀ {Δ} (ia : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (sampleIdeal ia) ≤ exprCostBoundUB hybOpCU ia + 3000000)
    (hEnc : optPred specialEnc (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ 2 * exprCostBoundUB hybOpCU x + 3100000)) :
    compCostBoundUB hybOpCU sC qC
      (encIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot
        sampleIdeal specialEnc (Γ := Γ)) ≤ 12000000 + 2 * qR := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hbM := bits_le_qR_add_15 hm
  let Δ0 : List (Ty (HSigR Pt ℓ)) :=
    .prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
      (CryptoGames.FSAEAD.Costed.bt .msg))) hsTy :: Γ
  have hi1 := hId (Δ := Δ0) (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
  dsimp only [Δ0, encIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt,
    aeadEncE, callE, Expr.v0, exprCostBoundUB] at hi1 ⊢
  cases specialEnc with
  | none =>
    unfold_hyb_vars
    dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
    generalize hidx : compCostBoundUB hybOpCU sC qC (sampleIdeal _) = idx at hi1 ⊢
    simp only [hb0, hb1]; omega
  | some sE =>
    have hs := hEnc (Δ := Δ0) (.pair (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
      (.snd (.snd (.fst .v0))))
    dsimp only [Δ0, Expr.v0, exprCostBoundUB] at hs
    unfold_hyb_vars
    dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
    generalize hidx : compCostBoundUB hybOpCU sC qC (sampleIdeal _) = idx at hi1 ⊢
    generalize hsex : compCostBoundUB hybOpCU sC qC (sE _) = sex at hs ⊢
    simp only [hb0, hb1]; omega

private lemma receiveBody_tight_ub_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    {sC : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ}
    (hsMK : sC (Sum.inr (UniformSamplerTag.base false)) ≤ 10)
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 10)
    {jPos mSlot qR : ℕ} (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002) (la : Bool)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hDec : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ exprCostBoundUB hybOpCU x + 70000)) :
    compCostBoundUB hybOpCU sC qC
      (receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos mSlot la specialDec (Γ := Γ)) ≤ 28000000 + 10 * qR := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hbS : bits 25000 ≤ 16 := Computational.Proofs.ReductionDsl.FsAtomicBounds.bits_25000_le
  dsimp only [receiveBody, skippedContainsE, skippedRemoveE, skippedRemoveBody, withSkippedE,
    isCompromisedE, isCompromisedBody, prependNewSkippedBody,
    orE, hsLastSent, hsCorrAt, hsRecvIdx, hsSkipped, callE, callC]
  generalize hgc :
    genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps jPos _ _ = gc
  have hg' : compCostBoundUB hybOpCU sC qC gc ≤ 23000050 + 2 * qR := by
    rw [← hgc]
    refine (genUpToC_tight_ub_le (I₀ := I₀) (sC := sC) (qC := qC) C ℓ encT idOf hsMK hsCK hj _ _).trans ?_
    unfold_hyb_vars; dsimp only [Expr.v0, exprCostBoundUB]; omega
  unfold_hyb_vars
  dsimp only [Expr.v0, compCostBoundUB, exprCostBoundUB]
  generalize hd1x : compCostBoundUB hybOpCU sC qC
    (decIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
      (Γ := stTy :: _)) = d1x
  have hd1 : d1x ≤ 600000 + 2 * qR := by
    rw [← hd1x]; exact decIdxBody_tight_ub_le C ℓ encT idOf hm specialDec hDec
  generalize hd2x : compCostBoundUB hybOpCU sC qC
    (decIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
      (Γ := _)) = d2x
  have hd2 : d2x ≤ 600000 + 2 * qR := by
    rw [← hd2x]; exact decIdxBody_tight_ub_le C ℓ encT idOf hm specialDec hDec
  simp only [hmfj, hb1, Nat.reduceAdd]
  omega


private lemma decIdxBody_simple_and_queries {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    (w : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ)
    (sO : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ) (mSlot : ℕ)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hDec : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 20 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 20)) :
    compHasListMOrFold
      (decIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
        (Γ := Γ)) = false ∧
    compSimpleOvh
      (decIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
        (Γ := Γ)) ≤ 60 ∧
    (decIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
      (Γ := Γ)).queries w (fun _ => 0) ≤ 1 ∧
    (decIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
      (Γ := Γ)).queries (fun _ => 20) sO ≤ 20 := by
  dsimp only [decIdxBody]
  cases specialDec with
  | none => refine ⟨rfl, ?_, ?_, ?_⟩ <;> (dsimp only [compSimpleOvh, Comp.queries]; omega)
  | some sD =>
    have ⟨hs1, hs2, hs3, hs4⟩ := hDec (Δ := .prod (.prod (.opt (CryptoGames.FSAEAD.Costed.bt .msg))
      (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (CryptoGames.FSAEAD.Costed.bt .ct)))) hsTy :: Γ)
      (.pair (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))
        (.snd (.snd (.snd (.fst .v0)))))
    dsimp only [compHasListMOrFold, compSimpleOvh, Comp.queries]
    simp only [hs1]
    generalize compSimpleOvh (sD _) = so at hs2 ⊢
    generalize (sD _).queries w (fun _ => 0) = sq at hs3 ⊢
    generalize (sD _).queries (fun _ => 20) sO = sqO at hs4 ⊢
    refine ⟨by simp, by omega, by omega, by omega⟩

private lemma encIdxBody_simple_and_queries {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    (w : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ)
    (sO : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ) (mSlot : ℕ)
    (sampleIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _)
    (specialEnc : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hId : ∀ {Δ} (ia : Expr _ Δ _),
      compHasListMOrFold (sampleIdeal ia) = false ∧ compSimpleOvh (sampleIdeal ia) ≤ 20 ∧
      (sampleIdeal ia).queries w (fun _ => 0) = 0 ∧
      (sampleIdeal ia).queries (fun _ => 20) sO ≤ 500100)
    (hEnc : optPred specialEnc (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 30 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 500120)) :
    compHasListMOrFold
      (encIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot
        sampleIdeal specialEnc (Γ := Γ)) = false ∧
    compSimpleOvh
      (encIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot
        sampleIdeal specialEnc (Γ := Γ)) ≤ 80 ∧
    (encIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot
      sampleIdeal specialEnc (Γ := Γ)).queries w (fun _ => 0) ≤ 1 ∧
    (encIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot
      sampleIdeal specialEnc (Γ := Γ)).queries (fun _ => 20) sO ≤ 1000300 := by
  let Δ0 : List (Ty (HSigR Pt ℓ)) :=
    .prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
      (CryptoGames.FSAEAD.Costed.bt .msg))) hsTy :: Γ
  have ⟨hi1, hi2, hi3, hi4⟩ := hId (Δ := Δ0) (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
  dsimp only [Δ0, encIdxBody] at hi1 hi2 hi3 hi4 ⊢
  cases specialEnc with
  | none =>
    dsimp only [compHasListMOrFold, compSimpleOvh, Comp.queries]
    simp only [hi1, hi3]
    generalize compSimpleOvh (sampleIdeal _) = io at hi2 ⊢
    generalize (sampleIdeal _).queries (fun _ => 20) sO = iqO at hi4 ⊢
    refine ⟨by simp, by omega, by omega, by omega⟩
  | some sE =>
    have ⟨hs1, hs2, hs3, hs4⟩ := hEnc (Δ := Δ0)
      (.pair (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0)))) (.snd (.snd (.fst .v0))))
    dsimp only [Δ0, compHasListMOrFold, compSimpleOvh, Comp.queries] at hs1 hs2 hs3 hs4 ⊢
    simp only [hi1, hi3, hs1]
    generalize compSimpleOvh (sampleIdeal _) = io at hi2 ⊢
    generalize (sampleIdeal _).queries (fun _ => 20) sO = iqO at hi4 ⊢
    generalize compSimpleOvh (sE _) = so at hs2 ⊢
    generalize (sE _).queries w (fun _ => 0) = sq at hs3 ⊢
    generalize (sE _).queries (fun _ => 20) sO = sqO at hs4 ⊢
    refine ⟨by simp, by omega, by omega, by omega⟩

private lemma receiveBody_simple_and_queries {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    (w : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ)
    {sO : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    (hsO : ∀ u, sO (Sum.inr u) ≤ 20)
    (jPos mSlot : ℕ) (la : Bool)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hDec : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 20 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 20)) :
    compHasListMOrFold
      (receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos mSlot la specialDec (Γ := Γ)) = false ∧
    compSimpleOvh
      (receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos mSlot la specialDec (Γ := Γ)) ≤ 700000 ∧
    (receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps jPos mSlot la specialDec (Γ := Γ)).queries w (fun _ => 0) ≤ 1 ∧
    (receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps jPos mSlot la specialDec (Γ := Γ)).queries (fun _ => 20) sO ≤ 1000200 := by
  have hmfj : maxForwardJumps = 25000 := rfl
  dsimp only [receiveBody, prependNewSkippedBody, callC]
  generalize hgc : genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) 1 1 maxForwardJumps jPos _ _ = gc
  have ⟨hg1, hg2⟩ : compHasListMOrFold gc = false ∧ compSimpleOvh gc ≤ 600000 := by
    rw [← hgc]; exact genUpToC_simple_and_ovh C ℓ encT idOf jPos _ _
  have ⟨hg3, hg4⟩ : gc.queries w (fun _ => 0) = 0 ∧ gc.queries (fun _ => 20) sO ≤ 1000100 := by
    rw [← hgc]; exact genUpToC_queries_zero C ℓ encT idOf w hsO jPos _ _
  generalize hd1 : decIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
    (Γ := stTy :: _) = d1
  have ⟨hd1a, hd1b, hd1c, hd1d⟩ : compHasListMOrFold d1 = false ∧ compSimpleOvh d1 ≤ 60 ∧
      d1.queries w (fun _ => 0) ≤ 1 ∧ d1.queries (fun _ => 20) sO ≤ 20 := by
    rw [← hd1]; exact decIdxBody_simple_and_queries C ℓ encT idOf w sO mSlot specialDec hDec
  generalize hd2 : decIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
    (Γ := _) = d2
  have ⟨hd2a, hd2b, hd2c, hd2d⟩ : compHasListMOrFold d2 = false ∧ compSimpleOvh d2 ≤ 60 ∧
      d2.queries w (fun _ => 0) ≤ 1 ∧ d2.queries (fun _ => 20) sO ≤ 20 := by
    rw [← hd2]; exact decIdxBody_simple_and_queries C ℓ encT idOf w sO mSlot specialDec hDec
  dsimp only [compHasListMOrFold, compSimpleOvh, Comp.queries]
  generalize compSimpleOvh gc = ogc at hg2 ⊢
  generalize compSimpleOvh d1 = od1 at hd1b ⊢
  generalize compSimpleOvh d2 = od2 at hd2b ⊢
  generalize d1.queries w (fun _ => 0) = qd1 at hd1c ⊢
  generalize d2.queries w (fun _ => 0) = qd2 at hd2c ⊢
  generalize gc.queries (fun _ => 20) sO = qgcO at hg4 ⊢
  generalize d1.queries (fun _ => 20) sO = qd1O at hd1d ⊢
  generalize d2.queries (fun _ => 20) sO = qd2O at hd2d ⊢
  refine ⟨by simp [hg1, hd1a, hd2a], ?_, ?_, ?_⟩
  · clear *- hmfj hg2 hd1b hd2b; rw [hmfj]; omega
  · rw [hg3]; clear *- hd1c hd2c; simp only [Nat.mul_zero]; omega
  · clear *- hg4 hd1d hd2d; simp only [Nat.mul_zero]; omega


private lemma transmitBody_tight {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    {sC sO : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    {qC w : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ}
    (hsMK : sC (Sum.inr (UniformSamplerTag.base false)) ≤ 10)
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 10)
    (hsO : ∀ u, sO (Sum.inr u) ≤ 20)
    {jPos mSlot qR : ℕ} (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002)
    (sampleIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _)
    (specialEnc : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hId : ∀ {Δ} (ia : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (sampleIdeal ia) ≤ exprCostBoundUB hybOpCU ia + 3000000 ∧
      compHasListMOrFold (sampleIdeal ia) = false ∧ compSimpleOvh (sampleIdeal ia) ≤ 20 ∧
      (sampleIdeal ia).queries w (fun _ => 0) = 0 ∧
      (sampleIdeal ia).queries (fun _ => 20) sO ≤ 500100)
    (hEnc : optPred specialEnc (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ 2 * exprCostBoundUB hybOpCU x + 3100000 ∧
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 30 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 500120)) :
    compCostBoundUB hybOpCU sC qC
      (transmitBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) ≤ 35500000 + 10 * qR ∧
    compHasListMOrFold
      (transmitBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) = false ∧
    compSimpleOvh
      (transmitBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) ≤ 650000 ∧
    (transmitBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)).queries w (fun _ => 0) ≤ 1 ∧
    (transmitBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)).queries (fun _ => 20) sO ≤ 2000500 := by
  have hb1 : bits 1 = 1 := rfl
  have hEnc1 : optPred specialEnc (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ 2 * exprCostBoundUB hybOpCU x + 3100000) := by
    cases specialEnc with | none => trivial | some f => exact fun x => (hEnc x).1
  have hEnc2 : optPred specialEnc (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 30 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 500120) := by
    cases specialEnc with | none => trivial | some f => exact fun x => (hEnc x).2
  dsimp only [transmitBody, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf,
    hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
  generalize hgc : genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) 1 1 maxForwardJumps jPos _ _ = gc
  have hgU : compCostBoundUB hybOpCU sC qC gc ≤ 23000050 + 2 * qR := by
    rw [← hgc]
    refine (genUpToC_tight_ub_le C ℓ encT idOf hsMK hsCK hj _ _).trans ?_
    unfold_hyb_vars; dsimp only [Expr.v0, hsLastSent, exprCostBoundUB]; simp only [hb1]; omega
  have ⟨hgS, hgO⟩ : compHasListMOrFold gc = false ∧ compSimpleOvh gc ≤ 600000 := by
    rw [← hgc]; exact genUpToC_simple_and_ovh C ℓ encT idOf jPos _ _
  have ⟨hgQ, hgQO⟩ : gc.queries w (fun _ => 0) = 0 ∧ gc.queries (fun _ => 20) sO ≤ 1000100 := by
    rw [← hgc]; exact genUpToC_queries_zero C ℓ encT idOf w hsO jPos _ _
  generalize hex : encIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot sampleIdeal
    specialEnc (Γ := _) = ex
  have heU : compCostBoundUB hybOpCU sC qC ex ≤ 12000000 + 2 * qR := by
    rw [← hex]
    exact encIdxBody_tight_ub_le C ℓ encT idOf hm sampleIdeal specialEnc (fun ia => (hId ia).1) hEnc1
  have ⟨heS, heO, heQ, heQO⟩ : compHasListMOrFold ex = false ∧ compSimpleOvh ex ≤ 80 ∧
      ex.queries w (fun _ => 0) ≤ 1 ∧ ex.queries (fun _ => 20) sO ≤ 1000300 := by
    rw [← hex]
    exact encIdxBody_simple_and_queries C ℓ encT idOf w sO mSlot sampleIdeal specialEnc
      (fun ia => (hId ia).2) hEnc2
  unfold_hyb_vars
  dsimp only [Expr.v0, hsLastSent, compCostBoundUB, exprCostBoundUB,
    compHasListMOrFold, compSimpleOvh, Comp.queries]
  rw [hgQ]
  simp only [hb1, hgS, heS]
  generalize compCostBoundUB hybOpCU sC qC gc = ugc at hgU ⊢
  generalize compCostBoundUB hybOpCU sC qC ex = uex at heU ⊢
  generalize compSimpleOvh gc = ogc at hgO ⊢
  generalize compSimpleOvh ex = oex at heO ⊢
  generalize ex.queries w (fun _ => 0) = qex at heQ ⊢
  generalize gc.queries (fun _ => 20) sO = qgcO at hgQO ⊢
  generalize ex.queries (fun _ => 20) sO = qexO at heQO ⊢
  clear hgc hex hId hEnc hEnc1 hEnc2 hsO
  refine ⟨by omega, by simp, by omega, by omega, by omega⟩

private lemma challengeBody_tight {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    {sC sO : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    {qC w : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ}
    (hsMK : sC (Sum.inr (UniformSamplerTag.base false)) ≤ 10)
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 10)
    (hsO : ∀ u, sO (Sum.inr u) ≤ 20)
    {jPos mSlot qR : ℕ} (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002)
    (sampleIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _)
    (specialEnc : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hId : ∀ {Δ} (ia : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (sampleIdeal ia) ≤ exprCostBoundUB hybOpCU ia + 3000000 ∧
      compHasListMOrFold (sampleIdeal ia) = false ∧ compSimpleOvh (sampleIdeal ia) ≤ 20 ∧
      (sampleIdeal ia).queries w (fun _ => 0) = 0 ∧
      (sampleIdeal ia).queries (fun _ => 20) sO ≤ 500100)
    (hEnc : optPred specialEnc (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ 2 * exprCostBoundUB hybOpCU x + 3100000 ∧
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 30 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 500120)) :
    compCostBoundUB hybOpCU sC qC
      (challengeBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) ≤ 35500000 + 10 * qR ∧
    compHasListMOrFold
      (challengeBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) = false ∧
    compSimpleOvh
      (challengeBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) ≤ 650000 ∧
    (challengeBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)).queries w (fun _ => 0) ≤ 1 ∧
    (challengeBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)).queries (fun _ => 20) sO ≤ 2000500 := by
  have hb1 : bits 1 = 1 := rfl
  have hEnc1 : optPred specialEnc (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ 2 * exprCostBoundUB hybOpCU x + 3100000) := by
    cases specialEnc with | none => trivial | some f => exact fun x => (hEnc x).1
  have hEnc2 : optPred specialEnc (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 30 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 500120) := by
    cases specialEnc with | none => trivial | some f => exact fun x => (hEnc x).2
  dsimp only [challengeBody, isSomeE, orE, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded,
    hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
  generalize hgc : genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) 1 1 maxForwardJumps jPos _ _ = gc
  have hgU : compCostBoundUB hybOpCU sC qC gc ≤ 23000050 + 2 * qR := by
    rw [← hgc]
    refine (genUpToC_tight_ub_le C ℓ encT idOf hsMK hsCK hj _ _).trans ?_
    unfold_hyb_vars; dsimp only [Expr.v0, hsLastSent, exprCostBoundUB]; simp only [hb1]; omega
  have ⟨hgS, hgO⟩ : compHasListMOrFold gc = false ∧ compSimpleOvh gc ≤ 600000 := by
    rw [← hgc]; exact genUpToC_simple_and_ovh C ℓ encT idOf jPos _ _
  have ⟨hgQ, hgQO⟩ : gc.queries w (fun _ => 0) = 0 ∧ gc.queries (fun _ => 20) sO ≤ 1000100 := by
    rw [← hgc]; exact genUpToC_queries_zero C ℓ encT idOf w hsO jPos _ _
  generalize hex : encIdxBody (I := I₀.withSamp (HSampR Pt ℓ))
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot sampleIdeal
    specialEnc (Γ := _) = ex
  have heU : compCostBoundUB hybOpCU sC qC ex ≤ 12000000 + 2 * qR := by
    rw [← hex]
    exact encIdxBody_tight_ub_le C ℓ encT idOf hm sampleIdeal specialEnc (fun ia => (hId ia).1) hEnc1
  have ⟨heS, heO, heQ, heQO⟩ : compHasListMOrFold ex = false ∧ compSimpleOvh ex ≤ 80 ∧
      ex.queries w (fun _ => 0) ≤ 1 ∧ ex.queries (fun _ => 20) sO ≤ 1000300 := by
    rw [← hex]
    exact encIdxBody_simple_and_queries C ℓ encT idOf w sO mSlot sampleIdeal specialEnc
      (fun ia => (hId ia).2) hEnc2
  unfold_hyb_vars
  dsimp only [Expr.v0, hsLastSent, compCostBoundUB, exprCostBoundUB, hybOpCU,
    compHasListMOrFold, compSimpleOvh, Comp.queries]
  rw [hgQ]
  simp only [hb1, hgS, heS]
  generalize compCostBoundUB hybOpCU sC qC gc = ugc at hgU ⊢
  generalize compCostBoundUB hybOpCU sC qC ex = uex at heU ⊢
  generalize compSimpleOvh gc = ogc at hgO ⊢
  generalize compSimpleOvh ex = oex at heO ⊢
  generalize ex.queries w (fun _ => 0) = qex at heQ ⊢
  generalize gc.queries (fun _ => 20) sO = qgcO at hgQO ⊢
  generalize ex.queries (fun _ => 20) sO = qexO at heQO ⊢
  clear hgc hex hId hEnc hEnc1 hEnc2 hsO
  refine ⟨by omega, by simp, by omega, by omega, by omega⟩


private lemma corruptSenderBody_tight {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    {sC : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ}
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 260)
    (qSim : ℕ) (la : Bool) :
    compCostBoundUB hybOpCU sC qC
      (corruptSenderBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 qSim la (Γ := Γ)) ≤ 5000 + 200 * qSim := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hsk : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (senderKeyBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 qSim (Γ := Δ)) ≤ 2000 + 150 * qSim := by
    intro Δ
    dsimp only [senderKeyBody, revealBody, chainFromC, chainFromBody, hsCorrAt, hsCorrKey,
      hsLastSent, prgGenE, callC, Ops.sum,
      CryptoGames.PRG.Costed.prgOps, CryptoGames.OTCCA.Costed.otccaOps, Iface.withSamp]
    unfold_hyb_vars
    dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
    simp only [hb0, hb1, Nat.reduceAdd]; omega
  dsimp only [corruptSenderBody, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin,
    hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
  unfold_hyb_vars
  dsimp only [compCostBoundUB, exprCostBoundUB]
  generalize hsx : compCostBoundUB hybOpCU sC qC (senderKeyBody _ _ _ _ _) = sx
  have hs1 : sx ≤ 2000 + 150 * qSim := by rw [← hsx]; exact hsk
  omega

private lemma deliverBody_tight {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    {sC sO : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    {qC w : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ}
    (hsMK : sC (Sum.inr (UniformSamplerTag.base false)) ≤ 10)
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 10)
    (hsO : ∀ u, sO (Sum.inr u) ≤ 20)
    {qSim jPos mSlot qR : ℕ} (hqS : qSim ≤ 2 * qR + 4)
    (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002) (la : Bool)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hDec : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ exprCostBoundUB hybOpCU x + 70000 ∧
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 20 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 20)) :
    compCostBoundUB hybOpCU sC qC
      (deliverBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) ≤ 29100000 + 950 * qR ∧
    compHasListMOrFold
      (deliverBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) = false ∧
    compSimpleOvh
      (deliverBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) ≤ 750000 ∧
    (deliverBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)).queries w (fun _ => 0) ≤ 1 ∧
    (deliverBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)).queries (fun _ => 20) sO ≤ 1000300 := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hbS : bits 25000 ≤ 16 := Computational.Proofs.ReductionDsl.FsAtomicBounds.bits_25000_le
  have hDec1 : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ exprCostBoundUB hybOpCU x + 70000) := by
    cases specialDec with | none => trivial | some f => exact fun x => (hDec x).1
  have hDec2 : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 20 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 20) := by
    cases specialDec with | none => trivial | some f => exact fun x => (hDec x).2
  dsimp only [deliverBody, findInTransitE, findInTransitBody, recMatchesE, challsContainsE,
    challsContainsBody, removeFromTransitE, removeFromTransitBody, isCompromisedE,
    isCompromisedBody, eqAdE, eqME, eqCE, orE, maxNatE, mkHS, hsB, hsLastSent, hsCorrAt,
    hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey,
    hsSkipped, recIdx, recAd, recMsg, recCt, callE, callC]
  generalize hrx : receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) 1 1 maxForwardJumps jPos mSlot la specialDec (Γ := _) = rx
  have hrU : compCostBoundUB hybOpCU sC qC rx ≤ 28000000 + 10 * qR := by
    rw [← hrx]; exact receiveBody_tight_ub_le C ℓ encT idOf hsMK hsCK hj hm la specialDec hDec1
  have ⟨hrS, hrO, hrQ, hrQO⟩ : compHasListMOrFold rx = false ∧ compSimpleOvh rx ≤ 700000 ∧
      rx.queries w (fun _ => 0) ≤ 1 ∧ rx.queries (fun _ => 20) sO ≤ 1000200 := by
    rw [← hrx]; exact receiveBody_simple_and_queries C ℓ encT idOf w hsO jPos mSlot la specialDec hDec2
  unfold_hyb_vars
  dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU,
    compHasListMOrFold, compSimpleOvh, Comp.queries]
  generalize compCostBoundUB hybOpCU sC qC rx = urx at hrU ⊢
  generalize compSimpleOvh rx = orx at hrO ⊢
  generalize rx.queries w (fun _ => 0) = qrx at hrQ ⊢
  generalize rx.queries (fun _ => 20) sO = qrxO at hrQO ⊢
  clear hrx hDec hDec1 hDec2 hsO
  refine ⟨by simp only [hmfj, hb1, hb2, Nat.reduceAdd]; omega, by simp [hrS], by omega, by omega, by omega⟩

private lemma injectBody_tight {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSigR Pt ℓ) T} {Γ}
    {sC sO : (I₀.withSamp (HSampR Pt ℓ)).smp.Samp → ℕ}
    {qC w : (I₀.withSamp (HSampR Pt ℓ)).Tag → ℕ}
    (hsMK : sC (Sum.inr (UniformSamplerTag.base false)) ≤ 10)
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 10)
    (hsO : ∀ u, sO (Sum.inr u) ≤ 20)
    {qSim jPos mSlot qR : ℕ} (hqS : qSim ≤ 2 * qR + 4)
    (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002) (la : Bool)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSampR Pt ℓ)) Δ _))
    (hDec : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ exprCostBoundUB hybOpCU x + 70000 ∧
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 20 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 20)) :
    compCostBoundUB hybOpCU sC qC
      (injectBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) ≤ 29100000 + 950 * qR ∧
    compHasListMOrFold
      (injectBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) = false ∧
    compSimpleOvh
      (injectBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) ≤ 750000 ∧
    (injectBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)).queries w (fun _ => 0) ≤ 1 ∧
    (injectBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)).queries (fun _ => 20) sO ≤ 1000300 := by
  have hb1 : bits 1 = 1 := rfl
  have hbS : bits 25000 ≤ 16 := Computational.Proofs.ReductionDsl.FsAtomicBounds.bits_25000_le
  have hDec1 : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (f x) ≤ exprCostBoundUB hybOpCU x + 70000) := by
    cases specialDec with | none => trivial | some f => exact fun x => (hDec x).1
  have hDec2 : optPred specialDec (fun f => ∀ {Δ} (x : Expr _ Δ _),
      compHasListMOrFold (f x) = false ∧ compSimpleOvh (f x) ≤ 20 ∧
      (f x).queries w (fun _ => 0) ≤ 1 ∧ (f x).queries (fun _ => 20) sO ≤ 20) := by
    cases specialDec with | none => trivial | some f => exact fun x => (hDec x).2
  dsimp only [injectBody, anyInTransitE, anyInTransitBody, recMatchesE, removeFromTransitE,
    removeFromTransitBody, isCompromisedE, isCompromisedBody, eqAdE, eqCE, orE, maxNatE,
    mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls,
    hsNKeys, hsKeysT, hsCorrKey, hsSkipped, recIdx, recAd, recCt, callE, callC]
  generalize hrx : receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) 1 1 maxForwardJumps jPos mSlot la specialDec (Γ := _) = rx
  have hrU : compCostBoundUB hybOpCU sC qC rx ≤ 28000000 + 10 * qR := by
    rw [← hrx]; exact receiveBody_tight_ub_le C ℓ encT idOf hsMK hsCK hj hm la specialDec hDec1
  have ⟨hrS, hrO, hrQ, hrQO⟩ : compHasListMOrFold rx = false ∧ compSimpleOvh rx ≤ 700000 ∧
      rx.queries w (fun _ => 0) ≤ 1 ∧ rx.queries (fun _ => 20) sO ≤ 1000200 := by
    rw [← hrx]; exact receiveBody_simple_and_queries C ℓ encT idOf w hsO jPos mSlot la specialDec hDec2
  unfold_hyb_vars
  dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU,
    compHasListMOrFold, compSimpleOvh, Comp.queries]
  generalize compCostBoundUB hybOpCU sC qC rx = urx at hrU ⊢
  generalize compSimpleOvh rx = orx at hrO ⊢
  generalize rx.queries w (fun _ => 0) = qrx at hrQ ⊢
  generalize rx.queries (fun _ => 20) sO = qrxO at hrQO ⊢
  clear hrx hDec hDec1 hDec2 hsO
  refine ⟨by simp only [hb1, Nat.reduceAdd]; omega, by simp [hrS], by omega, by omega, by omega⟩

end HybTightCost


section StepCostBounds

open Computational.Proofs.ReductionDsl.FsAtomicBounds (exprCostBoundUB compCostBoundUB
  exprCostBound_le_UB compCostBound_le_UB hybOpCU prgSC multiSC multiQC swOpCU slotSwSC slotSwQC
  hybOpMacro_cost_le prgSampMacro_cost_le multiSampMacro_cost_le multiQueryMacro_cost_le
  swOpMacro_cost_le slotSwSampMacro_cost_le slotSwQueryMacro_cost_le
  slotSaltEncC_cost_le slotSaltDecC_cost_le)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (exprCostBound compCostBound
  compilePureExpr_cost_le compilePureComp_cost_le compilePureComp_queries_le)

private abbrev HOpsR (Pt : Type) [DecidableEq Pt] (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :=
  Ops.sum
    (CryptoGames.PRG.Costed.prgOps (S := HSigR Pt ℓ)
      (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
      (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
    (SpecLemmas.Reductions.Primitives.OTCCA.CostedTables.otccaOps (S := HSigR Pt ℓ)
      (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))

private theorem initHybSessStExpr_cost_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6) :
    (initHybSessStExpr ℓ Pt C Dh encPt encT idOf lam).cost ≤ 100 := by
  have hb0 : bits 0 = 1 := rfl
  dsimp only [initHybSessStExpr]
  let e0 : Expr (HOpsR Pt C ℓ encT idOf) [.bool] CryptoGames.FSAEAD.Thm5.Costed.stTy :=
    (CryptoGames.FSAEAD.Thm5.Costed.initHSE (.var .zero)).pair (Expr.inl .unit)
  have h1 := (liftFsExpr_cost (Dh := Dh) (encPt := encPt) (lam := lam)
    (compilePureExpr (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) e0)).le
  have h2 := compilePureExpr_cost_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
    hybOpCU (hybOpMacro_cost_le C ℓ encT idOf hℓ) e0
  have h3 := exprCostBound_le_UB hybOpCU e0
  refine (h1.trans (h2.trans h3)).trans ?_
  dsimp only [e0, CryptoGames.FSAEAD.Thm5.Costed.initHSE, CryptoGames.FSAEAD.Thm5.Costed.mkHS,
    exprCostBoundUB]
  simp only [hb0]; omega

private theorem slotOtccaImpl_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (nf : Bool) (qSim : ℕ)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) (g : OTCCATag) :
    (slotOtccaImpl ℓ Pt C Dh encPt encT idOf lam nf qSim g).cost ≤
      (match g with | .enc => 3000300 | .dec => 1000300) + 50 * qSim ∧
    (slotOtccaImpl ℓ Pt C Dh encPt encT idOf lam nf qSim g).queries w (fun _ => 0) = 0 := by
  cases g with
  | enc =>
    let inner := liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
      (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC (Γ := [])
          C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim))
    have hc : inner.cost ≤ 3000000 + 50 * qSim :=
      (liftNoQuerySlotComp_cost .none .none rfl rfl _).trans
        ((compilePureComp_cost_le (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
          swOpCU slotSwSC slotSwQC
          (swOpMacro_cost_le C ℓ encT idOf hℓ)
          (slotSwSampMacro_cost_le C ℓ encT idOf hℓ)
          (slotSwQueryMacro_cost_le C ℓ encT idOf hℓ) _).trans
          (slotSaltEncC_cost_le C ℓ encT idOf false qSim))
    have hq : inner.queries w (fun _ => 0) = 0 :=
      liftNoQuerySlotComp_queries (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none _ w
    dsimp +zetaDelta only [inner] at hc hq
    dsimp only [slotOtccaImpl]
    generalize (liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
      (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC (Γ := [])
          C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim))) = innerF at hc hq ⊢
    dsimp only [slotSwMacroBundle, ReductionDsl.FsAtomicMacros.mapPureCtx] at hc hq innerF ⊢
    simp only [Comp.cost, Expr.cost, Comp.queries]
    rw [comp_renameM_cost, comp_renameM_queries, hq]
    exact ⟨by omega, by omega⟩
  | dec =>
    let inner := liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
      (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC (Γ := [])
          C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim))
    have hc : inner.cost ≤ 1000000 + 50 * qSim :=
      (liftNoQuerySlotComp_cost .none .none rfl rfl _).trans
        ((compilePureComp_cost_le (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
          swOpCU slotSwSC slotSwQC
          (swOpMacro_cost_le C ℓ encT idOf hℓ)
          (slotSwSampMacro_cost_le C ℓ encT idOf hℓ)
          (slotSwQueryMacro_cost_le C ℓ encT idOf hℓ) _).trans
          (slotSaltDecC_cost_le C ℓ encT idOf nf false qSim))
    have hq : inner.queries w (fun _ => 0) = 0 :=
      liftNoQuerySlotComp_queries (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none _ w
    dsimp +zetaDelta only [inner] at hc hq
    dsimp only [slotOtccaImpl]
    generalize (liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
      (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC (Γ := [])
          C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim))) = innerF at hc hq ⊢
    dsimp only [slotSwMacroBundle, ReductionDsl.FsAtomicMacros.mapPureCtx] at hc hq innerF ⊢
    simp only [Comp.cost, Expr.cost, Comp.queries]
    rw [comp_renameM_cost, comp_renameM_queries, hq]
    exact ⟨by omega, by omega⟩

private theorem liftSlotHybStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (nf : Bool) (qSim : ℕ)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ)
    {qTy rTy : Ty (atomicSig ℓ Pt)}
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt)
      [qTy, hybSessStTy ℓ Pt] (.prod rTy (hybSessStTy ℓ Pt)))
    (hSimple : compHasListMOrFold c = false) :
    (liftSlotHybStep ℓ Pt C Dh encPt encT idOf lam nf qSim c).cost ≤
      2 * c.cost + compSimpleOvh c +
        c.queries (fun g => (match g with | .enc => 3000308 | .dec => 1000308) + 50 * qSim)
          (fun _ => 0) + 50 ∧
    (liftSlotHybStep ℓ Pt C Dh encPt encT idOf lam nf qSim c).queries w (fun _ => 0) = 0 := by
  have hQ0 : ∀ {Γ t} (c' : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t),
      c'.queries (fun _ => 0) (fun _ => 0) = 0 := by
    intro Γ t c'; induction c' <;> simp [Comp.queries, *]
  dsimp only [liftSlotHybStep]
  generalize hqI : slotOtccaImpl ℓ Pt C Dh encPt encT idOf lam nf qSim = qI
  have hQmono : c.queries (fun g => (qI g).cost + 8) (fun _ => 0) ≤
      c.queries (fun g => (match g with | .enc => 3000308 | .dec => 1000308) + 50 * qSim)
        (fun _ => 0) :=
    comp_queries_mono (fun g => by
      have hg := (slotOtccaImpl_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ nf qSim w g).1
      rw [hqI] at hg
      cases g <;> (dsimp only at hg ⊢; omega)) (fun _ => le_rfl) c
  simp only [Comp.cost, Expr.cost, Comp.queries, Nat.add_zero]
  refine ⟨?_, Nat.eq_zero_of_le_zero ((substQueryComp_queries_le
    (I₁ := slotOtccaTargetIface ℓ Pt) (I₂ := fsaeadHeaderIface ℓ Pt)
    (fun s {_} e => liftBaseSamp s e) qI (fun _ => 0) w
    (fun s {_} e => liftBaseSamp_queries s e w)
    (fun g => by
      have hg2 := (slotOtccaImpl_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ nf qSim w g).2
      rw [hqI] at hg2; rw [hg2])
    envSwapFst2 (.snd (.var (.succ .zero)))
    (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c)).trans
    (by rw [liftFsSlotComp_queries, hQ0 c]))⟩
  refine (Nat.add_le_add_right (Nat.add_le_add_right (substQueryComp_simple_cost_le
    (I₁ := slotOtccaTargetIface ℓ Pt) (I₂ := fsaeadHeaderIface ℓ Pt)
    (fun s {_} e => liftBaseSamp s e) qI
    (fun s {_} e => by rw [liftBaseSamp_cost]; dsimp [slotOtccaTargetIface]; omega)
    envSwapFst2 envSwapFst2_cost (.snd (.var (.succ .zero)))
    (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c)
    (by rw [compHasListMOrFold_liftFsSlotComp]; exact hSimple)) _) _).trans ?_
  simp only [Expr.cost]
  rw [liftFsSlotComp_cost (Dh := Dh) (encPt := encPt) (lam := lam),
    compSimpleOvh_liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam),
    liftFsSlotComp_queries (Dh := Dh) (encPt := encPt) (lam := lam)]
  dsimp only [slotOtccaTargetIface] at hQmono ⊢
  omega


private theorem exprCostBoundUB_renameM {S : Sig} {O : Ops S} (oC : O.Op → ℕ)
    {Γ Δ : List (Ty S)} {t : Ty S} (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) (e : Expr O Γ t) :
    exprCostBoundUB oC (e.renameM f) = exprCostBoundUB oC e := by
  induction e generalizing Δ <;> simp [Expr.renameM, exprCostBoundUB, *]

private abbrev I₀PR (Pt : Type) [DecidableEq Pt] (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) :=
  Iface.withSamp
    (CryptoGames.PRG.Costed.prgIface
      (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
    (CryptoGames.OTCCA.Costed.idealSamplers
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ct) (lIdeal C clampedProtoSignalCodec ℓ encT) 1)

private lemma ub_sample_3m {n : ℕ} : n + 2190000 ≤ n + 3000000 := by omega
private lemma ub_fst_sample_le {n : ℕ} : (n + 1) + 2190000 ≤ 2 * n + 3100000 := by omega

private theorem realTrStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) {jPos mSlot qR : ℕ} (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (realTrStep ℓ Pt C Dh encPt encT idOf lam jPos mSlot).cost ≤ 35600000 + 10 * qR ∧
    (realTrStep ℓ Pt C Dh encPt encT idOf lam jPos mSlot).queries w (fun _ => 0) = 0 := by
  refine ⟨?_, liftFsCoinComp_queries _ w⟩
  dsimp only [realTrStep]
  refine (liftFsCoinComp_cost (Dh := Dh) (encPt := encPt) (lam := lam) _).le.trans
    ((compilePureComp_cost_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      hybOpCU prgSC Empty.elim
      (hybOpMacro_cost_le C ℓ encT idOf hℓ) (prgSampMacro_cost_le C ℓ encT idOf hℓ)
      (fun e => nomatch e) _).trans
      ((compCostBound_le_UB _ _ _ _).trans ?_))
  dsimp only [compCostBoundUB, exprCostBoundUB]
  refine (Nat.add_le_add_right (Nat.add_le_add_left
    ((transmitBody_tight C ℓ encT idOf (I₀ := I₀PR Pt C ℓ encT)
      (sC := prgSC) (sO := fun _ => 0) (qC := Empty.elim) (w := Empty.elim)
      (by dsimp [prgSC]; omega) (by dsimp [prgSC]; omega) (fun _ => by omega) hj hm
      (fun a => Comp.sample
        (I := (I₀PR Pt C ℓ encT).withSamp (HSampR Pt ℓ)) (Sum.inl (Sum.inr ())) a)
      (some (fun x => Comp.sample
        (I := (I₀PR Pt C ℓ encT).withSamp (HSampR Pt ℓ)) (Sum.inl (Sum.inr ())) (.fst x)))
      (fun ia => ⟨by exact ub_sample_3m,
        rfl, by dsimp only [compSimpleOvh]; omega, rfl, by dsimp only [Comp.queries]; omega⟩)
      (by
        intro Δ x
        exact ⟨by exact ub_fst_sample_le,
          rfl, by dsimp only [compSimpleOvh]; omega, by dsimp only [Comp.queries]; omega,
          by dsimp only [Comp.queries]; omega⟩)).1) _) _).trans (by omega)

private theorem realChStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) {jPos mSlot qR : ℕ} (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (realChStep ℓ Pt C Dh encPt encT idOf lam jPos mSlot).cost ≤ 35600000 + 10 * qR ∧
    (realChStep ℓ Pt C Dh encPt encT idOf lam jPos mSlot).queries w (fun _ => 0) = 0 := by
  refine ⟨?_, liftFsCoinComp_queries _ w⟩
  dsimp only [realChStep]
  refine (liftFsCoinComp_cost (Dh := Dh) (encPt := encPt) (lam := lam) _).le.trans
    ((compilePureComp_cost_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      hybOpCU prgSC Empty.elim
      (hybOpMacro_cost_le C ℓ encT idOf hℓ) (prgSampMacro_cost_le C ℓ encT idOf hℓ)
      (fun e => nomatch e) _).trans
      ((compCostBound_le_UB _ _ _ _).trans ?_))
  dsimp only [compCostBoundUB, exprCostBoundUB]
  refine (Nat.add_le_add_right (Nat.add_le_add_left
    ((challengeBody_tight C ℓ encT idOf (I₀ := I₀PR Pt C ℓ encT)
      (sC := prgSC) (sO := fun _ => 0) (qC := Empty.elim) (w := Empty.elim)
      (by dsimp [prgSC]; omega) (by dsimp [prgSC]; omega) (fun _ => by omega) hj hm
      (fun a => Comp.sample
        (I := (I₀PR Pt C ℓ encT).withSamp (HSampR Pt ℓ)) (Sum.inl (Sum.inr ())) a)
      (some (fun x => Comp.sample
        (I := (I₀PR Pt C ℓ encT).withSamp (HSampR Pt ℓ)) (Sum.inl (Sum.inr ())) (.fst x)))
      (fun ia => ⟨by exact ub_sample_3m,
        rfl, by dsimp only [compSimpleOvh]; omega, rfl, by dsimp only [Comp.queries]; omega⟩)
      (by
        intro Δ x
        exact ⟨by exact ub_fst_sample_le,
          rfl, by dsimp only [compSimpleOvh]; omega, by dsimp only [Comp.queries]; omega,
          by dsimp only [Comp.queries]; omega⟩)).1) _) _).trans (by omega)

private theorem realCsStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (qSim : ℕ) (la : Bool) (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la).cost ≤ 5100 + 200 * qSim ∧
    (realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la).queries w (fun _ => 0) = 0 := by
  refine ⟨?_, liftFsCoinComp_queries _ w⟩
  dsimp only [realCsStep]
  refine (liftFsCoinComp_cost (Dh := Dh) (encPt := encPt) (lam := lam) _).le.trans
    ((compilePureComp_cost_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      hybOpCU prgSC Empty.elim
      (hybOpMacro_cost_le C ℓ encT idOf hℓ) (prgSampMacro_cost_le C ℓ encT idOf hℓ)
      (fun e => nomatch e) _).trans
      ((compCostBound_le_UB _ _ _ _).trans ?_))
  dsimp only [compCostBoundUB, exprCostBoundUB]
  exact (Nat.add_le_add_right (Nat.add_le_add_left
    (corruptSenderBody_tight C ℓ encT idOf (I₀ := I₀PR Pt C ℓ encT)
      (sC := prgSC) (qC := Empty.elim) (by dsimp [prgSC]; omega) qSim la) _) _).trans (by omega)

private theorem realDlStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) {qSim jPos mSlot qR : ℕ} (hqS : qSim ≤ 2 * qR + 4)
    (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002) (la : Bool)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (realDlStep ℓ Pt C Dh encPt encT idOf lam qSim jPos mSlot la).cost ≤ 29200000 + 950 * qR ∧
    (realDlStep ℓ Pt C Dh encPt encT idOf lam qSim jPos mSlot la).queries w (fun _ => 0) = 0 := by
  refine ⟨?_, liftFsCoinComp_queries _ w⟩
  dsimp only [realDlStep]
  refine (liftFsCoinComp_cost (Dh := Dh) (encPt := encPt) (lam := lam) _).le.trans
    ((compilePureComp_cost_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      hybOpCU prgSC Empty.elim
      (hybOpMacro_cost_le C ℓ encT idOf hℓ) (prgSampMacro_cost_le C ℓ encT idOf hℓ)
      (fun e => nomatch e) _).trans
      ((compCostBound_le_UB _ _ _ _).trans ?_))
  dsimp only [compCostBoundUB, exprCostBoundUB]
  exact (Nat.add_le_add_right (Nat.add_le_add_left
    ((deliverBody_tight C ℓ encT idOf (I₀ := I₀PR Pt C ℓ encT)
      (sC := prgSC) (sO := fun _ => 0) (qC := Empty.elim) (w := Empty.elim)
      (by dsimp [prgSC]; omega) (by dsimp [prgSC]; omega) (fun _ => by omega) hqS hj hm la
      (some (fun _ => Comp.ret (O := HOpsR Pt C ℓ encT idOf)
        (I := (I₀PR Pt C ℓ encT).withSamp (HSampR Pt ℓ)) .none))
      (fun {Δ} x =>
        ⟨by dsimp only [compCostBoundUB, exprCostBoundUB]; omega,
         rfl, by dsimp only [compSimpleOvh]; omega, by dsimp only [Comp.queries]; omega,
         by dsimp only [Comp.queries]; omega⟩)).1) _) _).trans (by omega)

private theorem realIjStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) {qSim jPos mSlot qR : ℕ} (hqS : qSim ≤ 2 * qR + 4)
    (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002) (la : Bool)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (realIjStep ℓ Pt C Dh encPt encT idOf lam qSim jPos mSlot la).cost ≤ 29200000 + 950 * qR ∧
    (realIjStep ℓ Pt C Dh encPt encT idOf lam qSim jPos mSlot la).queries w (fun _ => 0) = 0 := by
  refine ⟨?_, liftFsCoinComp_queries _ w⟩
  dsimp only [realIjStep]
  refine (liftFsCoinComp_cost (Dh := Dh) (encPt := encPt) (lam := lam) _).le.trans
    ((compilePureComp_cost_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      hybOpCU prgSC Empty.elim
      (hybOpMacro_cost_le C ℓ encT idOf hℓ) (prgSampMacro_cost_le C ℓ encT idOf hℓ)
      (fun e => nomatch e) _).trans
      ((compCostBound_le_UB _ _ _ _).trans ?_))
  dsimp only [compCostBoundUB, exprCostBoundUB]
  exact (Nat.add_le_add_right (Nat.add_le_add_left
    ((injectBody_tight C ℓ encT idOf (I₀ := I₀PR Pt C ℓ encT)
      (sC := prgSC) (sO := fun _ => 0) (qC := Empty.elim) (w := Empty.elim)
      (by dsimp [prgSC]; omega) (by dsimp [prgSC]; omega) (fun _ => by omega) hqS hj hm la
      (some (fun _ => Comp.ret (O := HOpsR Pt C ℓ encT idOf)
        (I := (I₀PR Pt C ℓ encT).withSamp (HSampR Pt ℓ)) .none))
      (fun {Δ} x =>
        ⟨by dsimp only [compCostBoundUB, exprCostBoundUB]; omega,
         rfl, by dsimp only [compSimpleOvh]; omega, by dsimp only [Comp.queries]; omega,
         by dsimp only [Comp.queries]; omega⟩)).1) _) _).trans (by omega)


private theorem runLazyPubSess_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    {sTy : Ty (atomicSig ℓ Pt)}
    (mkInit : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt) [] sTy)
    (trS : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      [.prod fig8PubAdT PlainT, sTy] (.prod (.opt lctT) sTy))
    (chS : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      [.prod fig8PubAdT (.prod PlainT PlainT), sTy] (.prod (.opt lctT) sTy))
    (csS : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      [.unit, sTy] (.prod (.opt fsSendStT) sTy))
    (crS : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      [.unit, sTy] (.prod (.opt (.prod fsSendStT fsRecvStT)) sTy))
    (dlS : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy))
    (ijS : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy))
    (stepB : FSAEADTag → ℕ)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ)
    (hInit : mkInit.cost ≤ 150 ∧ mkInit.queries w (fun _ => 0) = 0)
    (hTr : trS.cost ≤ stepB .tr ∧ trS.queries w (fun _ => 0) = 0)
    (hCh : chS.cost ≤ stepB .ch ∧ chS.queries w (fun _ => 0) = 0)
    (hCs : csS.cost ≤ stepB .cs ∧ csS.queries w (fun _ => 0) = 0)
    (hCr : crS.cost ≤ stepB .cr ∧ crS.queries w (fun _ => 0) = 0)
    (hDl : dlS.cost ≤ stepB .dl ∧ dlS.queries w (fun _ => 0) = 0)
    (hIj : ijS.cost ≤ stepB .ij ∧ ijS.queries w (fun _ => 0) = 0)
    (g : FSAEADTag) :
    (runLazyPubSess ℓ Pt C Dh encPt encT lam mkInit trS chS csS crS dlS ijS g).cost ≤
      stepB g + 32000 ∧
    (runLazyPubSess ℓ Pt C Dh encPt encT lam mkInit trS chS csS crS dlS ijS g).queries
      w (fun _ => 0) = 0 := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  have hpub : (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam)
      (lPubOfExpr ℓ Pt C encT (Γ := [(fsaeadHeaderIface ℓ Pt).dom .dl, .prod .bool (.opt sTy)])
        (.snd (.snd (.var .zero))))).cost ≤ 31320 := by
    refine (liftFsExpr_cost (Dh := Dh) (encPt := encPt) (lam := lam) _).le.trans ?_
    have hp := Computational.Proofs.ReductionDsl.FsAtomicOps.lPubOfExpr_cost ℓ Pt C encT
      (Γ := [(fsaeadHeaderIface ℓ Pt).dom .dl, .prod .bool (.opt sTy)]) (.snd (.snd (.var .zero)))
    simp only [Expr.cost] at hp; omega
  cases g <;>
    (dsimp only [runLazyPubSess, ensureSessInit, mapRrWithPubExpr, exprWk1]
     simp only [Comp.cost, Expr.cost, Expr.renameM_cost, comp_renameM_cost,
       Comp.queries, comp_renameM_queries,
       hInit.2, hTr.2, hCh.2, hCs.2, hCr.2, hDl.2, hIj.2]
     exact ⟨by omega, by omega⟩)

private theorem comp_queries_const_mul {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (K : ℕ) {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    c.queries (fun _ => K) (fun _ => 0) = K * c.queries (fun _ => 1) (fun _ => 0) := by
  induction c with
  | ret _ | sample _ _ => simp [Comp.queries]
  | query _ _ => simp [Comp.queries]
  | bind _ _ ih1 ih2 => simp only [Comp.queries, ih1, ih2]; ring
  | ite _ c d ih1 ih2 | caseOpt _ c d ih1 ih2 | caseSum _ c d ih1 ih2 =>
    simp only [Comp.queries, ih1, ih2]
    rcases le_total (c.queries (fun _ => 1) (fun _ => 0)) (d.queries (fun _ => 1) (fun _ => 0)) with h | h
    · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_left K h)]
    · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul_left K h)]
  | iter n _ _ ih | foldM n _ _ _ ih | findM n _ _ ih | anyM n _ _ ih
  | mapM n _ _ ih | consumeFirstM n _ _ _ ih =>
    simp only [Comp.queries, ih]; ring

private def multiSampOvh {Pt : Type} {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} :
    ((CryptoGames.OTCCA.Costed.otccaIface
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .msg)
      (CryptoGames.FSAEAD.Costed.bt .ct) (lIdeal C clampedProtoSignalCodec ℓ encT) 1).withSamp
      (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))).smp.Samp → ℕ
  | Sum.inl _ => 500100
  | Sum.inr _ => 20

private theorem slotBind_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (nf : Bool) (qSim : ℕ)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ)
    {τ₁ τ₂ : Ty (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)}
    {U_b O_b QO_b : ℕ}
    (body : Comp _ ((CryptoGames.OTCCA.Costed.otccaIface
        (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
          (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .msg)
        (CryptoGames.FSAEAD.Costed.bt .ct) (lIdeal C clampedProtoSignalCodec ℓ encT) 1).withSamp
        (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)))
      [.prod τ₁ CryptoGames.FSAEAD.Thm5.Costed.stTy, τ₁, CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt τ₂) CryptoGames.FSAEAD.Thm5.Costed.stTy))
    (hBody : compCostBoundUB hybOpCU multiSC multiQC body ≤ U_b ∧
      compHasListMOrFold body = false ∧ compSimpleOvh body ≤ O_b ∧
      body.queries (fun _ => 1) (fun _ => 0) ≤ 1 ∧
      body.queries (fun _ => 20) (multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT)) ≤ QO_b) :
    (liftSlotHybStep ℓ Pt C Dh encPt encT idOf lam nf qSim
      (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
        (.bind (.ret (.pair (.var .zero) (.var (.succ .zero)))) body))).cost ≤
      2 * (U_b + 5) + (O_b + QO_b + 2) + (3000308 + 50 * qSim) + 50 ∧
    (liftSlotHybStep ℓ Pt C Dh encPt encT idOf lam nf qSim
      (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
        (.bind (.ret (.pair (.var .zero) (.var (.succ .zero)))) body))).queries
      w (fun _ => 0) = 0 := by
  rcases hBody with ⟨hU, hS, hO, hQ, hQO⟩
  have hnb : CryptoGames.CBC.nBlocks ℓ ≤ 62502 := by unfold CryptoGames.CBC.nBlocks; omega
  have hSampS : ∀ s, compHasListMOrFold ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s) = false := by
    intro s; rcases s with ⟨⟨⟩⟩ | (_ | _ | (_ | _)) <;>
      (dsimp [multiMacroBundle, Iface.withSamp, ReductionDsl.Samplers.sum, Sum.elim,
        CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleU64Comp,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleMsgKeyComp,
        slotOtccaTargetIface, ReductionDsl.atomicBaseSamplers, ReductionDsl.unifSamplers,
        compHasListMOrFold]; try rfl)
  have hQueryS : ∀ g, compHasListMOrFold ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g) = false := by
    intro g; cases g <;>
      (dsimp [multiMacroBundle, Iface.withSamp, CryptoGames.OTCCA.Costed.otccaIface, compHasListMOrFold]; try rfl)
  have hSampO : ∀ s, compSimpleOvh ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s) ≤
      multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT) s := by
    intro s; rcases s with ⟨⟨⟩⟩ | (_ | _ | (_ | _)) <;>
      (dsimp [multiMacroBundle, Iface.withSamp, ReductionDsl.Samplers.sum, Sum.elim,
        CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleU64Comp,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleMsgKeyComp,
        slotOtccaTargetIface, ReductionDsl.atomicBaseSamplers, ReductionDsl.unifSamplers,
        compSimpleOvh, multiSampOvh]; omega)
  have hQueryO : ∀ g, compSimpleOvh ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g) ≤ 20 := by
    intro g; cases g <;>
      (dsimp [multiMacroBundle, Iface.withSamp, CryptoGames.OTCCA.Costed.otccaIface, compSimpleOvh]; omega)
  let src := Comp.bind (.ret (.pair (.var .zero) (.var (.succ .zero)))) body
  generalize hcP : compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src = cP
  have hSimpleC : compHasListMOrFold cP = false := by
    rw [← hcP, compHasListMOrFold_compilePureComp _ hSampS hQueryS]
    dsimp [src, compHasListMOrFold]; exact hS
  have ⟨hLC, hLQ⟩ := liftSlotHybStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ nf qSim w cP hSimpleC
  refine ⟨hLC.trans ?_, hLQ⟩
  have hCostC : cP.cost ≤ U_b + 5 := by
    rw [← hcP]
    refine (compilePureComp_cost_le (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
      hybOpCU multiSC multiQC
      (hybOpMacro_cost_le C ℓ encT idOf hℓ) (multiSampMacro_cost_le C ℓ encT idOf hℓ)
      (multiQueryMacro_cost_le C ℓ encT idOf hℓ) src).trans ?_
    refine (compCostBound_le_UB _ _ _ src).trans ?_
    dsimp only [src, compCostBoundUB, exprCostBoundUB]
    omega
  have hOvhC : compSimpleOvh cP ≤ O_b + QO_b + 2 := by
    rw [← hcP]
    refine (compSimpleOvh_compilePureComp_le _ src).trans ?_
    refine (Nat.add_le_add
      (show compSimpleOvh src ≤ O_b + 2 by dsimp only [src, compSimpleOvh]; omega)
      ((comp_queries_mono hQueryO hSampO src).trans
        (show src.queries (fun _ => 20) (multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT)) ≤ QO_b by
          dsimp only [src, Comp.queries]; omega))).trans (by omega)
  have hQC : cP.queries
      (fun g => (match g with | .enc => 3000308 | .dec => 1000308) + 50 * qSim) (fun _ => 0) ≤
      3000308 + 50 * qSim := by
    rw [← hcP]
    refine (comp_queries_mono (w₂ := fun _ => 3000308 + 50 * qSim)
      (fun g => by cases g <;> dsimp <;> omega)
      (fun _ => le_rfl) _).trans ?_
    refine (compilePureComp_queries_le (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
      (fun _ => 3000308 + 50 * qSim) (fun _ => 0) (fun _ => 3000308 + 50 * qSim) (fun _ => 0)
      (fun s => by
        rcases s with ⟨⟨⟩⟩ | (_ | _ | (_ | _)) <;>
          (dsimp [multiMacroBundle, Iface.withSamp, ReductionDsl.Samplers.sum, Sum.elim,
            CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
            Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp,
            Computational.Proofs.ReductionDsl.FsAtomicOps.sampleU64Comp,
            Computational.Proofs.ReductionDsl.FsAtomicOps.sampleMsgKeyComp,
            slotOtccaTargetIface, ReductionDsl.atomicBaseSamplers, ReductionDsl.unifSamplers,
            Comp.queries]
           omega))
      (fun g => by
        cases g <;>
          (dsimp [multiMacroBundle, Iface.withSamp, CryptoGames.OTCCA.Costed.otccaIface,
            Comp.queries]; omega))
      src).trans ?_
    rw [comp_queries_const_mul]
    have hSrc1 : src.queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
      dsimp only [src, Comp.queries]; omega
    nlinarith
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hCostC) hOvhC) hQC) le_rfl


private theorem bits_j_le_qep_B0 {j qep B0 : ℕ} (hj : j ≤ (qep + 2) * B0 + B0 * B0) :
    bits j ≤ bits (qep + 1) + 2 * B0 + 4 := by
  open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_mul_le) in
  open Computational.Proofs.ReductionDsl.Fig8WeightedParts (bits_le_add_one) in
  have hmul : j ≤ B0 * ((qep + 1) * (B0 + 2)) := by nlinarith
  have h1 := (bits_mono hmul).trans (bits_mul_le B0 ((qep + 1) * (B0 + 2)))
  have h2 := bits_mul_le (qep + 1) (B0 + 2)
  have h3 := bits_le_add_one B0
  have h4 := bits_le_add_one (B0 + 2)
  omega

private abbrev slotI₀S (Pt : Type) [DecidableEq Pt] (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) :=
  CryptoGames.OTCCA.Costed.otccaIface (S := HSigR Pt ℓ)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) (lIdeal C clampedProtoSignalCodec ℓ encT) 1

private def slotSIdeal {Pt : Type} [DecidableEq Pt] {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {Δ}
    (a : Expr (HOpsR Pt C ℓ encT idOf) Δ (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))) :
    Comp (HOpsR Pt C ℓ encT idOf) ((slotI₀S Pt C ℓ encT).withSamp (HSampR Pt ℓ)) Δ
      (CryptoGames.FSAEAD.Costed.bt .ct) :=
  Comp.sample (O := HOpsR Pt C ℓ encT idOf)
    (I := (slotI₀S Pt C ℓ encT).withSamp (HSampR Pt ℓ)) (Sum.inl ()) a

private def slotSEnc {Pt : Type} [DecidableEq Pt] {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {Δ}
    (iam : Expr (HOpsR Pt C ℓ encT idOf) Δ
      (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad)) (CryptoGames.FSAEAD.Costed.bt .msg))) :
    Comp (HOpsR Pt C ℓ encT idOf) ((slotI₀S Pt C ℓ encT).withSamp (HSampR Pt ℓ)) Δ
      (CryptoGames.FSAEAD.Costed.bt .ct) :=
  .bind (Comp.query (O := HOpsR Pt C ℓ encT idOf)
      (I := (slotI₀S Pt C ℓ encT).withSamp (HSampR Pt ℓ))
      CryptoGames.OTCCA.Costed.OtccaTag.enc iam)
    (.caseOpt (.var .zero) (slotSIdeal (.fst (exprWk1 iam))) (.ret (.var .zero)))

private def slotSDec {Pt : Type} [DecidableEq Pt] {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {Δ}
    (iae : Expr (HOpsR Pt C ℓ encT idOf) Δ
      (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad)) (CryptoGames.FSAEAD.Costed.bt .ct))) :
    Comp (HOpsR Pt C ℓ encT idOf) ((slotI₀S Pt C ℓ encT).withSamp (HSampR Pt ℓ)) Δ
      (.opt (CryptoGames.FSAEAD.Costed.bt .msg)) :=
  Comp.query (O := HOpsR Pt C ℓ encT idOf)
    (I := (slotI₀S Pt C ℓ encT).withSamp (HSampR Pt ℓ))
    CryptoGames.OTCCA.Costed.OtccaTag.dec iae

private theorem hyb_exprCostBoundUB_wk1 {Pt : Type} [DecidableEq Pt] {C : Crypto} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {Δ} {a t : Ty (HSigR Pt ℓ)}
    (e : Expr (HOpsR Pt C ℓ encT idOf) Δ t) :
    exprCostBoundUB hybOpCU (exprWk1 (a := a) e) = exprCostBoundUB hybOpCU e :=
  exprCostBoundUB_renameM (O := HOpsR Pt C ℓ encT idOf) hybOpCU _ e

private lemma ub_slotSEnc_le {a b : ℕ} (h : b = a) :
    (a + 63000) + (1 + ((b + 1) + 2190000) + (1 + 1) + 1) + 1 ≤ 2 * a + 3100000 := by omega

private theorem slotSIdeal_tight {Pt : Type} [DecidableEq Pt] {C : Crypto} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {Δ}
    (ia : Expr (HOpsR Pt C ℓ encT idOf) Δ (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))) :
    compCostBoundUB hybOpCU multiSC multiQC (slotSIdeal ia) ≤
      exprCostBoundUB hybOpCU ia + 3000000 ∧
    compHasListMOrFold (slotSIdeal ia) = false ∧ compSimpleOvh (slotSIdeal ia) ≤ 20 ∧
    (slotSIdeal ia).queries (fun _ => 1) (fun _ => 0) = 0 ∧
    (slotSIdeal ia).queries (fun _ => 20) (multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT)) ≤ 500100 :=
  ⟨ub_sample_3m,
    rfl, by dsimp only [slotSIdeal, compSimpleOvh]; omega, rfl,
    by dsimp only [slotSIdeal, Comp.queries, multiSampOvh]; omega⟩

private theorem slotSEnc_tight {Pt : Type} [DecidableEq Pt] {C : Crypto} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {Δ}
    (x : Expr (HOpsR Pt C ℓ encT idOf) Δ
      (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad)) (CryptoGames.FSAEAD.Costed.bt .msg))) :
    compCostBoundUB hybOpCU multiSC multiQC (slotSEnc x) ≤
      2 * exprCostBoundUB hybOpCU x + 3100000 ∧
    compHasListMOrFold (slotSEnc x) = false ∧ compSimpleOvh (slotSEnc x) ≤ 30 ∧
    (slotSEnc x).queries (fun _ => 1) (fun _ => 0) ≤ 1 ∧
    (slotSEnc x).queries (fun _ => 20) (multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT)) ≤ 500120 :=
  ⟨ub_slotSEnc_le (hyb_exprCostBoundUB_wk1 (a := .opt (CryptoGames.FSAEAD.Costed.bt .ct)) x),
    rfl, by dsimp only [slotSEnc, slotSIdeal, compSimpleOvh]; omega,
    by dsimp only [slotSEnc, slotSIdeal, Comp.queries]; omega,
    by dsimp only [slotSEnc, slotSIdeal, Comp.queries, multiSampOvh]; omega⟩

private theorem slotSDec_tight {Pt : Type} [DecidableEq Pt] {C : Crypto} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {Δ}
    (x : Expr (HOpsR Pt C ℓ encT idOf) Δ
      (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad)) (CryptoGames.FSAEAD.Costed.bt .ct))) :
    compCostBoundUB hybOpCU multiSC multiQC (slotSDec x) ≤
      exprCostBoundUB hybOpCU x + 70000 ∧
    compHasListMOrFold (slotSDec x) = false ∧ compSimpleOvh (slotSDec x) ≤ 20 ∧
    (slotSDec x).queries (fun _ => 1) (fun _ => 0) ≤ 1 ∧
    (slotSDec x).queries (fun _ => 20) (multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT)) ≤ 20 :=
  ⟨Nat.add_le_add_left (by decide) (exprCostBoundUB hybOpCU x),
    rfl, by dsimp only [slotSDec, compSimpleOvh]; omega,
    by dsimp only [slotSDec, Comp.queries]; omega,
    by dsimp only [slotSDec, Comp.queries]; omega⟩

private theorem slotTrStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (stage : Bool) {qSim N qR : ℕ} (hqS : qSim ≤ 2 * qR + 4) (hN : N ≤ qR + 25002)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (slotTrStep ℓ Pt C Dh encPt encT idOf lam stage qSim N).cost ≤ 76700000 + 120 * qR ∧
    (slotTrStep ℓ Pt C Dh encPt encT idOf lam stage qSim N).queries w (fun _ => 0) = 0 := by
  dsimp only [slotTrStep]
  refine And.imp_left (fun h => h.trans (by omega))
    (slotBind_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage qSim w
      (U_b := 35500000 + 10 * qR) (O_b := 650000) (QO_b := 2000500) _
      (transmitBody_tight C ℓ encT idOf (I₀ := slotI₀S Pt C ℓ encT) (sC := multiSC)
        (sO := multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT)) (qC := multiQC) (w := fun _ => 1)
        (by dsimp [multiSC]; omega) (by dsimp [multiSC]; omega)
        (fun _ => by dsimp [multiSampOvh]; omega) hN hN
        (@slotSIdeal Pt _ C ℓ encT idOf) (some (@slotSEnc Pt _ C ℓ encT idOf))
        (@slotSIdeal_tight Pt _ C ℓ encT idOf) (@slotSEnc_tight Pt _ C ℓ encT idOf)))

private theorem slotChStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (stage : Bool) {qSim N qR : ℕ} (hqS : qSim ≤ 2 * qR + 4) (hN : N ≤ qR + 25002)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (slotChStep ℓ Pt C Dh encPt encT idOf lam stage qSim N).cost ≤ 76700000 + 120 * qR ∧
    (slotChStep ℓ Pt C Dh encPt encT idOf lam stage qSim N).queries w (fun _ => 0) = 0 := by
  dsimp only [slotChStep]
  refine And.imp_left (fun h => h.trans (by omega))
    (slotBind_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage qSim w
      (U_b := 35500000 + 10 * qR) (O_b := 650000) (QO_b := 2000500) _
      (challengeBody_tight C ℓ encT idOf (I₀ := slotI₀S Pt C ℓ encT) (sC := multiSC)
        (sO := multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT)) (qC := multiQC) (w := fun _ => 1)
        (by dsimp [multiSC]; omega) (by dsimp [multiSC]; omega)
        (fun _ => by dsimp [multiSampOvh]; omega) hN hN
        (@slotSIdeal Pt _ C ℓ encT idOf) (some (@slotSEnc Pt _ C ℓ encT idOf))
        (@slotSIdeal_tight Pt _ C ℓ encT idOf) (@slotSEnc_tight Pt _ C ℓ encT idOf)))

private theorem slotCsStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) {qSim qR : ℕ} (hqS : qSim ≤ 2 * qR + 4) (la : Bool)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (slotCsStep ℓ Pt C Dh encPt encT idOf lam qSim la).cost ≤ 6000 + 400 * qR ∧
    (slotCsStep ℓ Pt C Dh encPt encT idOf lam qSim la).queries w (fun _ => 0) = 0 := by
  have hRCs := realCsStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ qSim la w
  dsimp only [slotCsStep]
  simp only [Comp.cost, Expr.cost, Comp.queries]
  rw [comp_renameM_cost, comp_renameM_queries, hRCs.2]
  exact ⟨by omega, by omega⟩

private theorem slotDlStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (stage la : Bool) {qSim N qR : ℕ} (hqS : qSim ≤ 2 * qR + 4) (hN : N ≤ qR + 25002)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (slotDlStep ℓ Pt C Dh encPt encT idOf lam stage qSim N la).cost ≤ 63500000 + 2000 * qR ∧
    (slotDlStep ℓ Pt C Dh encPt encT idOf lam stage qSim N la).queries w (fun _ => 0) = 0 := by
  dsimp only [slotDlStep]
  refine And.imp_left (fun h => h.trans (by omega))
    (slotBind_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage qSim w
      (U_b := 29100000 + 950 * qR) (O_b := 750000) (QO_b := 1000300) _
      (deliverBody_tight C ℓ encT idOf (I₀ := slotI₀S Pt C ℓ encT) (sC := multiSC)
        (sO := multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT)) (qC := multiQC) (w := fun _ => 1)
        (by dsimp [multiSC]; omega) (by dsimp [multiSC]; omega)
        (fun _ => by dsimp [multiSampOvh]; omega) hqS hN hN la
        (some (@slotSDec Pt _ C ℓ encT idOf)) (@slotSDec_tight Pt _ C ℓ encT idOf)))

private theorem slotIjStep_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (stage la : Bool) {qSim N qR : ℕ} (hqS : qSim ≤ 2 * qR + 4) (hN : N ≤ qR + 25002)
    (w : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (slotIjStep ℓ Pt C Dh encPt encT idOf lam stage qSim N la).cost ≤ 63500000 + 2000 * qR ∧
    (slotIjStep ℓ Pt C Dh encPt encT idOf lam stage qSim N la).queries w (fun _ => 0) = 0 := by
  dsimp only [slotIjStep]
  refine And.imp_left (fun h => h.trans (by omega))
    (slotBind_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage qSim w
      (U_b := 29100000 + 950 * qR) (O_b := 750000) (QO_b := 1000300) _
      (injectBody_tight C ℓ encT idOf (I₀ := slotI₀S Pt C ℓ encT) (sC := multiSC)
        (sO := multiSampOvh (Pt := Pt) (C := C) (ℓ := ℓ) (encT := encT)) (qC := multiQC) (w := fun _ => 1)
        (by dsimp [multiSC]; omega) (by dsimp [multiSC]; omega)
        (fun _ => by dsimp [multiSampOvh]; omega) hqS hN hN la
        (some (@slotSDec Pt _ C ℓ encT idOf)) (@slotSDec_tight Pt _ C ℓ encT idOf)))

private def routerStepB (qR : ℕ) : FSAEADTag → ℕ
  | .tr => 76700000 + 120 * qR
  | .ch => 76700000 + 120 * qR
  | .cs => 6000 + 400 * qR
  | .cr => 6000 + 400 * qR
  | .dl => 63500000 + 2000 * qR
  | .ij => 63500000 + 2000 * qR

private theorem routerRealLazy_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (stage la : Bool) (qR : ℕ) (g : FSHdrTag) :
    (runLazyPubSess ℓ Pt C Dh encPt encT lam
      (initRealSessComp ℓ Pt C Dh encPt encT idOf lam)
      (realTrStep ℓ Pt C Dh encPt encT idOf lam
        (if stage then authHopCutoff maxForwardJumps qR la else 0)
        (if stage then authHopCutoff maxForwardJumps qR la else 0))
      (realChStep ℓ Pt C Dh encPt encT idOf lam
        (if stage then authHopCutoff maxForwardJumps qR la else 0)
        (if stage then authHopCutoff maxForwardJumps qR la else 0))
      (realCsStep ℓ Pt C Dh encPt encT idOf lam (2 * qR + 4) la)
      (realCrStep ℓ Pt C Dh encPt encT lam)
      (realDlStep ℓ Pt C Dh encPt encT idOf lam (2 * qR + 4)
        (if stage then authHopCutoff maxForwardJumps qR la else 0)
        (if stage then authHopCutoff maxForwardJumps qR la else 0) la)
      (realIjStep ℓ Pt C Dh encPt encT idOf lam (2 * qR + 4)
        (if stage then authHopCutoff maxForwardJumps qR la else 0)
        (if stage then authHopCutoff maxForwardJumps qR la else 0) la)
      (toFsTag g)).cost ≤ routerStepB qR (toFsTag g) + 32000 ∧
    (runLazyPubSess ℓ Pt C Dh encPt encT lam
      (initRealSessComp ℓ Pt C Dh encPt encT idOf lam)
      (realTrStep ℓ Pt C Dh encPt encT idOf lam
        (if stage then authHopCutoff maxForwardJumps qR la else 0)
        (if stage then authHopCutoff maxForwardJumps qR la else 0))
      (realChStep ℓ Pt C Dh encPt encT idOf lam
        (if stage then authHopCutoff maxForwardJumps qR la else 0)
        (if stage then authHopCutoff maxForwardJumps qR la else 0))
      (realCsStep ℓ Pt C Dh encPt encT idOf lam (2 * qR + 4) la)
      (realCrStep ℓ Pt C Dh encPt encT lam)
      (realDlStep ℓ Pt C Dh encPt encT idOf lam (2 * qR + 4)
        (if stage then authHopCutoff maxForwardJumps qR la else 0)
        (if stage then authHopCutoff maxForwardJumps qR la else 0) la)
      (realIjStep ℓ Pt C Dh encPt encT idOf lam (2 * qR + 4)
        (if stage then authHopCutoff maxForwardJumps qR la else 0)
        (if stage then authHopCutoff maxForwardJumps qR la else 0) la)
      (toFsTag g)).queries (fun _ => 1) (fun _ => 0) = 0 := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hjPos : (if stage then authHopCutoff maxForwardJumps qR la else 0) ≤ qR + 25002 := by
    dsimp [authHopCutoff]; rw [hmfj]; split_ifs <;> omega
  have hInitR : (initRealSessComp ℓ Pt C Dh encPt encT idOf lam).cost ≤ 150 ∧
      (initRealSessComp ℓ Pt C Dh encPt encT idOf lam).queries (fun _ => 1) (fun _ => 0) = 0 := by
    have := initHybSessStExpr_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ
    dsimp only [initRealSessComp, fsaeadHeaderIface, atomicSamplers, ReductionDsl.unifSamplers]
    simp only [Comp.cost, Expr.cost, Comp.queries]; exact ⟨by omega, trivial⟩
  have hRTr := realTrStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ hjPos hjPos (fun _ => 1)
  have hRCh := realChStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ hjPos hjPos (fun _ => 1)
  have hRCs := realCsStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ (2 * qR + 4) la (fun _ => 1)
  have hRDl := realDlStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ (le_refl _) hjPos hjPos la (fun _ => 1)
  have hRIj := realIjStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ (le_refl _) hjPos hjPos la (fun _ => 1)
  exact runLazyPubSess_cost_queries ℓ Pt C Dh encPt encT lam hℓ _ _ _ _ _ _ _
    (routerStepB qR) (fun _ => 1) hInitR
    ⟨hRTr.1.trans (by dsimp [routerStepB]; omega), hRTr.2⟩
    ⟨hRCh.1.trans (by dsimp [routerStepB]; omega), hRCh.2⟩
    ⟨hRCs.1.trans (by dsimp [routerStepB]; omega), hRCs.2⟩
    ⟨by dsimp [realCrStep, Comp.cost, Expr.cost, routerStepB]; omega, rfl⟩
    ⟨hRDl.1.trans (by dsimp [routerStepB]; omega), hRDl.2⟩
    ⟨hRIj.1.trans (by dsimp [routerStepB]; omega), hRIj.2⟩ (toFsTag g)

private theorem routerSlotLazy_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (stage la : Bool) (qR : ℕ) (g : FSHdrTag) :
    (runLazyPubSess ℓ Pt C Dh encPt encT lam
      (initSlotSessComp ℓ Pt C Dh encPt encT idOf lam)
      (slotTrStep ℓ Pt C Dh encPt encT idOf lam stage (2 * qR + 4) (authHopCutoff maxForwardJumps qR la))
      (slotChStep ℓ Pt C Dh encPt encT idOf lam stage (2 * qR + 4) (authHopCutoff maxForwardJumps qR la))
      (slotCsStep ℓ Pt C Dh encPt encT idOf lam (2 * qR + 4) la)
      (slotCrStep ℓ Pt C Dh encPt encT lam)
      (slotDlStep ℓ Pt C Dh encPt encT idOf lam stage (2 * qR + 4) (authHopCutoff maxForwardJumps qR la) la)
      (slotIjStep ℓ Pt C Dh encPt encT idOf lam stage (2 * qR + 4) (authHopCutoff maxForwardJumps qR la) la)
      (toFsTag g)).cost ≤ routerStepB qR (toFsTag g) + 32000 ∧
    (runLazyPubSess ℓ Pt C Dh encPt encT lam
      (initSlotSessComp ℓ Pt C Dh encPt encT idOf lam)
      (slotTrStep ℓ Pt C Dh encPt encT idOf lam stage (2 * qR + 4) (authHopCutoff maxForwardJumps qR la))
      (slotChStep ℓ Pt C Dh encPt encT idOf lam stage (2 * qR + 4) (authHopCutoff maxForwardJumps qR la))
      (slotCsStep ℓ Pt C Dh encPt encT idOf lam (2 * qR + 4) la)
      (slotCrStep ℓ Pt C Dh encPt encT lam)
      (slotDlStep ℓ Pt C Dh encPt encT idOf lam stage (2 * qR + 4) (authHopCutoff maxForwardJumps qR la) la)
      (slotIjStep ℓ Pt C Dh encPt encT idOf lam stage (2 * qR + 4) (authHopCutoff maxForwardJumps qR la) la)
      (toFsTag g)).queries (fun _ => 1) (fun _ => 0) = 0 := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hN : authHopCutoff maxForwardJumps qR la ≤ qR + 25002 := by
    dsimp [authHopCutoff]; rw [hmfj]; split_ifs <;> omega
  have hInitS : (initSlotSessComp ℓ Pt C Dh encPt encT idOf lam).cost ≤ 150 ∧
      (initSlotSessComp ℓ Pt C Dh encPt encT idOf lam).queries (fun _ => 1) (fun _ => 0) = 0 := by
    have := initHybSessStExpr_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ
    dsimp only [initSlotSessComp, emptySaltSlotAtomExpr, fsaeadHeaderIface, atomicSamplers,
      ReductionDsl.unifSamplers]
    simp only [Comp.cost, Expr.cost, Comp.queries]; exact ⟨by omega, trivial⟩
  exact runLazyPubSess_cost_queries ℓ Pt C Dh encPt encT lam hℓ _ _ _ _ _ _ _
    (routerStepB qR) (fun _ => 1) hInitS
    (slotTrStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage (le_refl _) hN (fun _ => 1))
    (slotChStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage (le_refl _) hN (fun _ => 1))
    (slotCsStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ (le_refl _) la (fun _ => 1))
    ⟨by dsimp [slotCrStep, Comp.cost, Expr.cost, routerStepB]; omega, rfl⟩
    (slotDlStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage la (le_refl _) hN (fun _ => 1))
    (slotIjStep_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage la (le_refl _) hN (fun _ => 1))
    (toFsTag g)

private lemma add_max_eq (a b c : ℕ) : a + max b c = max (a + b) (a + c) := by omega
private lemma max_add_eq (a b c : ℕ) : max a b + c = max (a + c) (b + c) := by omega

private theorem routerQueryMacro_cost_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (stage la : Bool) {j qep qR B0 : ℕ}
    (hj : j ≤ (qep + 2) * B0 + B0 * B0) (g : FSHdrTag) :
    (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR g).cost + 10 ≤
      3 * (fsMultiQueryC qep qR B0 g / 3) + 76000000 ∧
    (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR g).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  have hbj := bits_j_le_qep_B0 hj
  have hInitE := initHybSessStExpr_cost_le ℓ Pt C Dh encPt encT idOf lam hℓ
  have ⟨hRL1, hRL2⟩ := routerRealLazy_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage la qR g
  have ⟨hSL1, hSL2⟩ := routerSlotLazy_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage la qR g
  have hqC : (fsaeadHeaderIface ℓ Pt).qCost (toFsTag g) ≤ 150000 := by
    cases g <;> (dsimp [toFsTag, fsaeadHeaderIface]; omega)
  have hRHS : fsMultiQueryC qep qR B0 g + 75999995 ≤
      3 * (fsMultiQueryC qep qR B0 g / 3) + 76000000 := by omega
  refine ⟨Nat.le_trans ?_ hRHS, ?_⟩
  · cases stage <;> cases g <;>
      (dsimp only [routerQueryMacro, toFsTag, routerStepB] at hRL1 hSL1 hqC ⊢
       simp only [fsMultiQueryC_tr, fsMultiQueryC_ch, fsMultiQueryC_cs, fsMultiQueryC_cr,
         fsMultiQueryC_dl, fsMultiQueryC_ij, Bool.false_eq_true, ite_true, ite_false,
         Comp.cost, Expr.cost] at hRL1 hSL1 hqC ⊢
       repeat rw [comp_renameM_cost]
       simp only [add_max_eq, max_add_eq, max_le_iff]
       repeat' constructor <;> omega)
  · cases stage <;> cases g <;>
      (dsimp only [routerQueryMacro]
       simp only [toFsTag, Bool.false_eq_true, ite_true, ite_false,
         Comp.queries] at hRL2 hSL2 ⊢
       repeat rw [comp_renameM_queries]
       rw [hRL2]; try rw [hSL2]
       simp only [max_le_iff]
       repeat' constructor <;> omega)

end StepCostBounds

end RouterCostBounds


section GRedBoundedProofs

private theorem ckaOpMacro_cost_le_local (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (B0 : ℕ) (o : CryptoGames.CKA.CKAOp) :
    (ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0 o).cost + 1 ≤ ckaOpC B0 o := by
  have h1 := Computational.Proofs.ReductionDsl.Fig8Atomic.ckaInitAExpr_cost ℓ Pt C Dh encPt encT lam
  have h2 := Computational.Proofs.ReductionDsl.Fig8Atomic.ckaInitBExpr_cost ℓ Pt C Dh encPt encT lam
  have h3 := Computational.Proofs.ReductionDsl.Fig8Atomic.ckaSendExpr_cost ℓ Pt C Dh encPt encT lam
  have h4 := Computational.Proofs.ReductionDsl.Fig8Atomic.ckaRecvExpr_cost ℓ Pt C Dh encPt encT lam
  have h5 := Computational.Proofs.ReductionDsl.Fig8Atomic.prngInitExpr_cost ℓ Pt C Dh encPt encT lam
  have h6 := Computational.Proofs.ReductionDsl.Fig8Atomic.prngUpExpr_cost ℓ Pt C Dh encPt encT lam
  have h7 := Computational.Proofs.ReductionDsl.Fig8Atomic.fsInitSendExpr_cost ℓ Pt C Dh encPt encT lam
  have h8 := Computational.Proofs.ReductionDsl.Fig8Atomic.fsInitRecvExpr_cost ℓ Pt C Dh encPt encT lam
  have h9 := Computational.Proofs.ReductionDsl.Fig8Atomic.fsSendExpr_cost ℓ Pt C Dh encPt encT lam
  have h10 := Computational.Proofs.ReductionDsl.Fig8Atomic.eqPtExpr_cost ℓ Pt C Dh encPt encT lam
  have h11 := Computational.Proofs.ReductionDsl.Fig8Atomic.eqMExpr_cost ℓ Pt C Dh encPt encT lam
  have h12 := Computational.Proofs.ReductionDsl.Fig8Atomic.eqEExpr_cost ℓ Pt C Dh encPt encT lam
  have h13 := Computational.Proofs.ReductionDsl.Fig8Atomic.lamIExpr_cost ℓ Pt C Dh encPt encT lam
  have h14 := Computational.Proofs.ReductionDsl.Fig8Atomic.defaultEExpr_cost ℓ Pt C Dh encPt encT lam
  cases o with
  | fsReceive B' =>
    have h15 := Computational.Proofs.ReductionDsl.Fig8Atomic.fsRecvExpr_cost ℓ Pt C Dh encPt encT lam B0 B'
    simp only [ckaOpMacro, ckaOpC]; omega
  | _ => simp only [ckaOpMacro, ckaOpC]; omega

private theorem bits_ratchetCostBudget_le (q qep : ℕ) :
    bits (ratchetCostBudget q qep) ≤ 32 + 2 * q + bits qep := by
  open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_mul_le) in
  open Computational.Proofs.ReductionDsl.Fig8WeightedParts (bits_le_add_one) in
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbq1 : 1 ≤ bits qep := ReductionDsl.one_le_bits qep
  have hle : ratchetCostBudget q qep ≤ (4096 * 25001) * ((q + 1) * ((q + 1) * bits qep)) := by
    unfold ratchetCostBudget; rw [hmfj]; nlinarith
  have h1 := (bits_mono hle).trans (bits_mul_le (4096 * 25001) ((q + 1) * ((q + 1) * bits qep)))
  have h2 := bits_mul_le (q + 1) ((q + 1) * bits qep)
  have h3 := bits_mul_le (q + 1) (bits qep)
  have h4 := bits_le_add_one (q + 1)
  have h5 := bits_le_add_one (bits qep)
  have h6 : bits (4096 * 25001) = 27 := by decide
  omega

private theorem red_totalQueries_const_mul {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {κ : Type} {G : OracleSpec κ} {C_game : GameCodec S G}
    {rIn aIn aOut out : Ty S} (K : ℕ)
    (R : CostedReduction O I G C_game rIn aIn aOut out) (q : ℕ) :
    R.totalQueries (fun _ => K) (fun _ => 0) q =
      K * R.totalQueries (fun _ => 1) (fun _ => 0) q := by
  unfold CostedReduction.totalQueries
  rw [comp_queries_const_mul K R.init, comp_queries_const_mul K R.handle,
    comp_queries_const_mul K R.finish]
  ring

private theorem multi_totalCost_arith {q qep qOut tc₁ Q₁ N : ℕ}
    (hqOut : qOut ≤ 2 * q)
    (hQ₁ : Q₁ ≤ qOut)
    (htc₁ : tc₁ ≤ (q + 1) * fig8AtomicStepBound q qep)
    (h3N : 3 * N ≤ 524288 + 128 * bits (ratchetCostBudget q qep))
    (tc₂ : ℕ)
    (htc₂ : 2 * tc₂ ≤ 7 * tc₁ + 2 * 10 + 60 + 28 * q + 2 * (76000000 * Q₁) + 96 * N * Q₁) :
    tc₂ ≤ ratchetCostBudget q qep := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbB := bits_ratchetCostBudget_le q qep
  have h96N : 96 * N ≤ 16908288 + 8192 * q + 4096 * bits qep := by omega
  have h96NQ : 96 * N * Q₁ ≤ (16908288 + 8192 * q + 4096 * bits qep) * (2 * q) :=
    Nat.mul_le_mul h96N (hQ₁.trans hqOut)
  have hExQ : 2 * (76000000 * Q₁) ≤ 304000000 * q := by omega
  have hStep : fig8AtomicStepBound q qep =
      3100180 * (q + 1) + 3 * (q + 1) * bits qep + 200 * bits qep + 25000000 := by
    unfold fig8AtomicStepBound; dsimp only; rw [hmfj]; ring
  have hBud : 2 * ratchetCostBudget q qep =
      204800000 * (q + 1) ^ 2 + 8192 * (q + 1) ^ 2 * bits qep := by
    unfold ratchetCostBudget; rw [hmfj]; ring
  rw [hStep] at htc₁
  suffices h2 : 2 * tc₂ ≤ 2 * ratchetCostBudget q qep by omega
  rw [hBud]
  generalize bits qep = bq at htc₁ h96NQ ⊢
  cases q with
  | zero => nlinarith
  | succ q =>
    have : 0 ≤ q * bq := Nat.zero_le _
    have : 0 ≤ q ^ 2 * bq := Nat.zero_le _
    nlinarith

private theorem compileFsMulti_dflt_cost_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {κ : Type} {G : OracleSpec κ} {C_game : GameCodec (atomicSig ℓ Pt) G}
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {lam : Pt}
    (hcc : C_game.codecCost ≤ 1000) (q qep : ℕ) :
    ((Expr.unit (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (Γ := [])).cost + 3) +
      q * max (fsaeadHeaderIface ℓ Pt).uCost
        ((@Expr.inl _ (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [] (.opt .unit) C_game.R .none).cost +
          3 + C_game.codecCost) +
      ((Expr.bool (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (Γ := []) false).cost + 1) ≤
      ratchetCostBudget q qep := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hm : max (fsaeadHeaderIface ℓ Pt).uCost
      ((@Expr.inl _ (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [] (.opt .unit) C_game.R .none).cost +
        3 + C_game.codecCost) ≤ 1010 := by
    dsimp [fsaeadHeaderIface, Expr.cost]; omega
  have hmul := Nat.mul_le_mul_left q hm
  have hBud : 102400000 * (q + 1) ^ 2 ≤ ratchetCostBudget q qep := by
    unfold ratchetCostBudget; rw [hmfj]
    calc 102400000 * (q + 1) ^ 2
      _ = 2 ^ 12 * (q + 1) ^ 2 * 25000 := by ring
      _ ≤ 2 ^ 12 * (q + 1) ^ 2 * (25000 + bits qep) :=
          Nat.mul_le_mul_left _ (Nat.le_add_right 25000 _)
  have hsq : q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  dsimp only [fsaeadHeaderIface, Expr.cost] at hmul ⊢
  omega

end GRedBoundedProofs



section RouterPublicTheorems

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

/-- `GRedBounded` within `ratchetCostBudget q qep` for `compileFsMultiAtomic`. -/
theorem compileFsMultiAtomic_gRedBounded_base (stage la : Bool) (j qep qR B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (q qOut : ℕ)
    (_hB0 : B0 ≤ (2 * q + 2) * (maxForwardJumps + 1))
    (hparts : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.init +
        compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.finish + 100000 ≤
          fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.handle + 200000 ≤
        fig8AtomicStepBound q qep)
    (hSize : compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.finish + 400 ≤
        1400000 + 585 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut)
    (hqOut : qOut ≤ 2 * q := by omega)
    (hListM : compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish ≤ 50 :=
      by simp [compListMNodes])
    (hqCount : compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish ≤ 60 :=
      by simp [compQueryCount])
    (hqR : qR ≤ 2 * q + 2 := by omega) :
    GRedBounded (compileFsMultiAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  let _ := hqR
  unfold compileFsMultiAtomic
  let M := fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256))
  let A := ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam
  let R' := compilePureAuxRed M A R
  have hQ' : R'.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut :=
    (compilePureAuxRed_totalQueries_le M A R (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
      (fun s => by cases s <;> rfl)
      (fun g => by cases g <;> (dsimp [M, fsMultiPureAuxBundle, Comp.queries]; omega)) q).trans hQ
  let R_inner := substQueryRed
    (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := fsaeadHeaderIface ℓ Pt)
    (initRouterStExpr ℓ Pt C Dh encPt encT lam)
    (fun s {_} e => Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (I := fsaeadHeaderIface ℓ Pt) s e)
    (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR) R'
  refine ite_fallback_gRedBounded R_inner _ _ _ _ _ _ q qOut _
    (fun ⟨hℓ, hj, _⟩ => ?_)
    (compileFsMulti_dflt_cost_le (C_game := fig8SmCodec ℓ Pt)
      (by dsimp [fig8SmCodec, GameCodec.codecCost, Expr.cost]; omega) q qep)
    (fun hP => compileFsMultiAtomic_size_le ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 q R hSize hP hListM hqCount)
    (compileFsMulti_dflt_size_le (rTy := .unit) (uTy := .unit))
    (fun ⟨hℓ, hj, _⟩ =>
      (substQueryRed_totalQueries_le
        (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := fsaeadHeaderIface ℓ Pt)
        (initRouterStExpr ℓ Pt C Dh encPt encT lam)
        (fun s {_} e => Comp.sample (I := fsaeadHeaderIface ℓ Pt) s e)
        (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR)
        (fun _ => 1) (fun _ => 1)
        (fun _ {_} _ => rfl)
        (fun g => (routerQueryMacro_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage la hj g).2)
        R' q).trans hQ')
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  have htc₁ : R'.totalCost q ≤ (q + 1) * fig8AtomicStepBound q qep := by
    refine (compilePureAuxRed_totalCost_le M A R
      (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (ckaOpMacro_cost_le_local ℓ Pt C Dh encPt encT idOf lam hℓ B0)
      (fun s => by
        cases s <;>
          (dsimp [M, fsMultiPureAuxBundle, fsMultiSampMacro, fsaeadMultiAtomicIface,
            atomicSamplers, ReductionDsl.unifSamplers, ckaSampC, Comp.cost, Expr.cost,
            AtomicUnifBase.cost]; omega))
      (fun g => by
        cases g <;>
          (dsimp [M, fsMultiPureAuxBundle, fsaeadMultiAtomicIface]
           simp only [Comp.cost, Expr.cost, fsMultiQueryC_tr, fsMultiQueryC_ch,
             fsMultiQueryC_cs, fsMultiQueryC_cr, fsMultiQueryC_dl, fsMultiQueryC_ij]; omega)) q).trans ?_
    have hsI : A.splitIn.cost ≤ _ :=
      Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
    have haQ : A.adaptQ.cost ≤ _ :=
      Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8AdaptQ_cost ℓ Pt C Dh encPt encT lam
    have haR : A.adaptR.cost ≤ _ :=
      Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8AdaptR_cost ℓ Pt C Dh encPt encT lam
    have haAI : A.adaptAIn.cost ≤ 20 := by dsimp [A, ckaToFig8Adapters, Expr.cost]; omega
    have haAO : A.adaptAOut.cost ≤ 20 := by dsimp [A, ckaToFig8Adapters, Expr.cost]; omega
    have haO : A.adaptOut.cost ≤ 20 := by dsimp [A, ckaToFig8Adapters, Expr.cost]; omega
    have huC : (fsaeadMultiAtomicIface ℓ Pt qep qR B0).uCost = 1 := rfl
    have hcC : (fig8SmCodec ℓ Pt).codecCost ≤ 500 := by
      dsimp [fig8SmCodec, GameCodec.codecCost, Expr.cost]; omega
    have h200k : 200000 ≤ fig8AtomicStepBound q qep := by unfold fig8AtomicStepBound; dsimp only; omega
    have hmax : max (fsaeadMultiAtomicIface ℓ Pt qep qR B0).uCost
        (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.handle +
          A.adaptQ.cost + A.adaptR.cost + (fig8SmCodec ℓ Pt).codecCost + 28) ≤
        fig8AtomicStepBound q qep := max_le (by omega) (by omega)
    refine (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left q hmax) _) _).trans ?_
    have hrng : (q + 1) * fig8AtomicStepBound q qep =
        fig8AtomicStepBound q qep + q * fig8AtomicStepBound q qep := by ring
    rw [hrng]; omega
  have h3N : 3 * (compListMNodes R'.init + compListMNodes R'.handle + compListMNodes R'.finish) ≤
      524288 + 128 * bits (ratchetCostBudget q qep) := by
    have hSL : ∀ s, compListMNodes (M.sampMacro s) = 0 := fun s => by cases s <;> rfl
    have hQL : ∀ g, compListMNodes (M.queryMacro g) = 0 := fun g => by cases g <;> rfl
    have hLi : compListMNodes R'.init ≤ compListMNodes R.init := by
      dsimp [R', compilePureAuxRed, Comp.wkTop2]
      simp only [compListMNodes_renameM, zero_add]
      exact compListMNodes_compilePureAuxComp_le M hSL hQL R.init
    have hLh : compListMNodes R'.handle ≤ compListMNodes R.handle := by
      dsimp [R', compilePureAuxRed, Comp.wkTop3]
      simp only [compListMNodes_renameM, zero_add]
      exact compListMNodes_compilePureAuxComp_le M hSL hQL R.handle
    have hLf : compListMNodes R'.finish ≤ compListMNodes R.finish := by
      dsimp [R', compilePureAuxRed, Comp.wkTop3]
      simp only [compListMNodes_renameM, zero_add]
      exact compListMNodes_compilePureAuxComp_le M hSL hQL R.finish
    omega
  have hSub : 2 * R_inner.totalCost q ≤ _ := substQueryRed_totalCost_le
    (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := fsaeadHeaderIface ℓ Pt)
    (initRouterStExpr ℓ Pt C Dh encPt encT lam)
    (fun s {_} e => Comp.sample (I := fsaeadHeaderIface ℓ Pt) s e)
    (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR)
    (fun _ => 76000000)
    (by dsimp [fsaeadHeaderIface, fsaeadMultiAtomicIface]; omega)
    (fun s => by
      rcases s with _ | N | (_ | _) <;>
        (dsimp [fsaeadMultiAtomicIface, atomicSamplers, ReductionDsl.unifSamplers,
          AtomicUnifBase.cost]
         try have := ReductionDsl.one_le_bits N
         omega))
    (fun s {_} e => by
      dsimp [Comp.cost, fsaeadHeaderIface, fsaeadMultiAtomicIface]; omega)
    (fun g => (routerQueryMacro_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage la hj g).1)
    R' q
  have hQM := red_totalQueries_const_mul 76000000 R' q
  have hrInit : (initRouterStExpr ℓ Pt C Dh encPt encT lam (Γ := [.unit])).cost ≤ 10 := by
    dsimp [initRouterStExpr, Expr.cost]; omega
  exact multi_totalCost_arith hqOut hQ' htc₁ h3N (R_inner.totalCost q) (by omega)

/-- `GRedBounded` within `ratchetCostBudget q qep` for `compileFsMultiDFAtomic`. -/
theorem compileFsMultiDFAtomic_gRedBounded_base (stage la : Bool) (j qep qR B0 : ℕ)
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
    (q qOut : ℕ)
    (_hB0 : B0 ≤ (2 * q + 2) * (maxForwardJumps + 1))
    (hparts : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.init +
        compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.finish + 100000 ≤
          fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.handle + 200000 ≤
        fig8AtomicStepBound q qep)
    (hSize : compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.finish + 400 ≤
        1400000 + 810 * bits (ratchetCostBudget q qep))
    (hQ : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut)
    (hqOut : qOut ≤ 2 * q := by omega)
    (hListM : compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish ≤ 50 :=
      by simp [compListMNodes])
    (hqCount : compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish ≤ 60 :=
      by simp [compQueryCount])
    (hqR : qR ≤ 2 * q + 2 := by omega) :
    GRedBounded (compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  let _ := hqR
  unfold compileFsMultiDFAtomic
  let M := fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256))
  let A := ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam
  let R' := compilePureAuxRed M A R
  have hQ' : R'.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut :=
    (compilePureAuxRed_totalQueries_le M A R (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
      (fun s => by cases s <;> rfl)
      (fun g => by cases g <;> (dsimp [M, fsMultiPureAuxBundle, Comp.queries]; omega)) q).trans hQ
  let R_inner := substQueryRed
    (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := fsaeadHeaderIface ℓ Pt)
    (initRouterStExpr ℓ Pt C Dh encPt encT lam)
    (fun s {_} e => Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (I := fsaeadHeaderIface ℓ Pt) s e)
    (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR) R'
  refine ite_fallback_gRedBounded R_inner _ _ _ _ _ _ q qOut _
    (fun ⟨hℓ, hj, _⟩ => ?_)
    (compileFsMulti_dflt_cost_le (C_game := fig8SmCodecDF ℓ Pt)
      (by dsimp [fig8SmCodecDF, GameCodec.codecCost, Expr.cost]; omega) q qep)
    (fun hP => compileFsMultiDFAtomic_size_le ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 q R hSize hP hListM hqCount)
    (compileFsMulti_dflt_size_le (rTy := .unit) (uTy := .unit))
    (fun ⟨hℓ, hj, _⟩ =>
      (substQueryRed_totalQueries_le
        (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := fsaeadHeaderIface ℓ Pt)
        (initRouterStExpr ℓ Pt C Dh encPt encT lam)
        (fun s {_} e => Comp.sample (I := fsaeadHeaderIface ℓ Pt) s e)
        (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR)
        (fun _ => 1) (fun _ => 1)
        (fun _ {_} _ => rfl)
        (fun g => (routerQueryMacro_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage la hj g).2)
        R' q).trans hQ')
    (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  have htc₁ : R'.totalCost q ≤ (q + 1) * fig8AtomicStepBound q qep := by
    refine (compilePureAuxRed_totalCost_le M A R
      (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (ckaOpMacro_cost_le_local ℓ Pt C Dh encPt encT idOf lam hℓ B0)
      (fun s => by
        cases s <;>
          (dsimp [M, fsMultiPureAuxBundle, fsMultiSampMacro, fsaeadMultiAtomicIface,
            atomicSamplers, ReductionDsl.unifSamplers, ckaSampC, Comp.cost, Expr.cost,
            AtomicUnifBase.cost]; omega))
      (fun g => by
        cases g <;>
          (dsimp [M, fsMultiPureAuxBundle, fsaeadMultiAtomicIface]
           simp only [Comp.cost, Expr.cost, fsMultiQueryC_tr, fsMultiQueryC_ch,
             fsMultiQueryC_cs, fsMultiQueryC_cr, fsMultiQueryC_dl, fsMultiQueryC_ij]; omega)) q).trans ?_
    have hsI : A.splitIn.cost ≤ _ :=
      Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8SplitIn_cost ℓ Pt C Dh encPt encT idOf lam
    have haQ : A.adaptQ.cost ≤ _ :=
      Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8AdaptQDF_cost ℓ Pt C Dh encPt encT lam
    have haR : A.adaptR.cost ≤ _ :=
      Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8AdaptRDF_cost ℓ Pt C Dh encPt encT lam
    have haAI : A.adaptAIn.cost ≤ 20 := by dsimp [A, ckaDFToFig8Adapters, Expr.cost]; omega
    have haAO : A.adaptAOut.cost ≤ 20 := by dsimp [A, ckaDFToFig8Adapters, Expr.cost]; omega
    have haO : A.adaptOut.cost ≤ 20 := by dsimp [A, ckaDFToFig8Adapters, Expr.cost]; omega
    have huC : (fsaeadMultiAtomicIface ℓ Pt qep qR B0).uCost = 1 := rfl
    have hcC : (fig8SmCodecDF ℓ Pt).codecCost ≤ 500 := by
      dsimp [fig8SmCodecDF, GameCodec.codecCost, Expr.cost]; omega
    have h200k : 200000 ≤ fig8AtomicStepBound q qep := by unfold fig8AtomicStepBound; dsimp only; omega
    have hmax : max (fsaeadMultiAtomicIface ℓ Pt qep qR B0).uCost
        (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.handle +
          A.adaptQ.cost + A.adaptR.cost + (fig8SmCodecDF ℓ Pt).codecCost + 28) ≤
        fig8AtomicStepBound q qep := max_le (by omega) (by omega)
    refine (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left q hmax) _) _).trans ?_
    have hrng : (q + 1) * fig8AtomicStepBound q qep =
        fig8AtomicStepBound q qep + q * fig8AtomicStepBound q qep := by ring
    rw [hrng]; omega
  have h3N : 3 * (compListMNodes R'.init + compListMNodes R'.handle + compListMNodes R'.finish) ≤
      524288 + 128 * bits (ratchetCostBudget q qep) := by
    have hSL : ∀ s, compListMNodes (M.sampMacro s) = 0 := fun s => by cases s <;> rfl
    have hQL : ∀ g, compListMNodes (M.queryMacro g) = 0 := fun g => by cases g <;> rfl
    have hLi : compListMNodes R'.init ≤ compListMNodes R.init := by
      dsimp [R', compilePureAuxRed, Comp.wkTop2]
      simp only [compListMNodes_renameM, zero_add]
      exact compListMNodes_compilePureAuxComp_le M hSL hQL R.init
    have hLh : compListMNodes R'.handle ≤ compListMNodes R.handle := by
      dsimp [R', compilePureAuxRed, Comp.wkTop3]
      simp only [compListMNodes_renameM, zero_add]
      exact compListMNodes_compilePureAuxComp_le M hSL hQL R.handle
    have hLf : compListMNodes R'.finish ≤ compListMNodes R.finish := by
      dsimp [R', compilePureAuxRed, Comp.wkTop3]
      simp only [compListMNodes_renameM, zero_add]
      exact compListMNodes_compilePureAuxComp_le M hSL hQL R.finish
    omega
  have hSub : 2 * R_inner.totalCost q ≤ _ := substQueryRed_totalCost_le
    (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := fsaeadHeaderIface ℓ Pt)
    (initRouterStExpr ℓ Pt C Dh encPt encT lam)
    (fun s {_} e => Comp.sample (I := fsaeadHeaderIface ℓ Pt) s e)
    (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR)
    (fun _ => 76000000)
    (by dsimp [fsaeadHeaderIface, fsaeadMultiAtomicIface]; omega)
    (fun s => by
      rcases s with _ | N | (_ | _) <;>
        (dsimp [fsaeadMultiAtomicIface, atomicSamplers, ReductionDsl.unifSamplers,
          AtomicUnifBase.cost]
         try have := ReductionDsl.one_le_bits N
         omega))
    (fun s {_} e => by
      dsimp [Comp.cost, fsaeadHeaderIface, fsaeadMultiAtomicIface]; omega)
    (fun g => (routerQueryMacro_cost_queries ℓ Pt C Dh encPt encT idOf lam hℓ stage la hj g).1)
    R' q
  have hQM := red_totalQueries_const_mul 76000000 R' q
  have hrInit : (initRouterStExpr ℓ Pt C Dh encPt encT lam (Γ := [.unit])).cost ≤ 10 := by
    dsimp [initRouterStExpr, Expr.cost]; omega
  exact multi_totalCost_arith hqOut hQ' htc₁ h3N (R_inner.totalCost q) (by omega)

end RouterPublicTheorems

end Computational.Proofs.SessionCostedFig8.BundlesMultiFsRouterCostB

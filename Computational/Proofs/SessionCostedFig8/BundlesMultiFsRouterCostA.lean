/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase
import Computational.Proofs.SessionCostedFig8.BundlesAdapters
import Computational.Proofs.SessionCostedFig8.BundlesCompilers
import Computational.Proofs.SessionCostedFig8.BundlesAuxSize
import Computational.Proofs.ReductionDsl.FsAtomicBoundsStage
import Computational.Proofs.ReductionDsl.Fig8Atomic
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.MacroLift
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
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal guardRed guardRed_pos
  guardRed_gRedBounded)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (PureAuxBundle compCostW
  coinSimEquiv_liftP compilePureAuxRed compilePureAuxRed_totalCost_le
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

namespace Computational.Proofs.SessionCostedFig8.BundlesMultiFsRouterCostA

/-! ## 8. AST `.size` Bounds (Slice 1B) -/

section SizeBounds

open Computational.Proofs.ReductionDsl.PureAuxMacroLift (compilePureAuxExpr compilePureAuxComp)
open Computational.Proofs.SessionCostedFig8.BundlesAdapters (fig8SplitIn_size
  fig8AdaptQ_size fig8AdaptR_size fig8AdaptQDF_size fig8AdaptRDF_size)
open Computational.Proofs.SessionCostedFig8.BundlesAuxSize (exprSizeW compilePureAuxRed_size_le
  compilePureAuxComp_size_le ckaOpMacro_size_le)

private theorem one_le_exprSize {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) : 1 ≤ e.size := by
  cases e with
  | nat n => exact ReductionDsl.one_le_bits n
  | mulK k a | divK k a | modK k a =>
    have hk := ReductionDsl.one_le_bits k
    simp only [Expr.size]; omega
  | _ => simp only [Expr.size]; omega

private theorem one_le_compSize {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) : 1 ≤ c.size := by
  cases c <;> simp only [Comp.size] <;> omega

private theorem one_le_exprSizeW {S : Sig} {O : Ops S} (opS : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) : 1 ≤ exprSizeW opS e := by
  induction e with
  | nat n => exact ReductionDsl.one_le_bits n
  | op o a iha => simp only [exprSizeW]; omega
  | _ => simp only [exprSizeW]; omega

private theorem one_le_compSizeW {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) : 1 ≤ compSizeW opS sS qS c := by
  cases c with
  | sample s e =>
    have := one_le_exprSizeW opS e
    simp only [compSizeW]; omega
  | query g e =>
    have := one_le_exprSizeW opS e
    simp only [compSizeW]; omega
  | _ => simp only [compSizeW]; omega

@[simp] private theorem exprWk1_size {S : Sig} {O : Ops S} {a t : Ty S} {Γ : List (Ty S)}
    (e : Expr O Γ t) : (exprWk1 (a := a) e).size = e.size :=
  Expr.renameM_size _ e

private theorem liftEnv1_size_le {S : Sig} {O : Ops S} {a : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: Γ) u), (liftEnv1 envMap v).size ≤ 2
  | _, .zero => by simp [liftEnv1, Expr.size]
  | _, .succ w => by simp only [liftEnv1, exprWk1_size]; exact hEnv w

private theorem liftEnv2_size_le {S : Sig} {O : Ops S} {a b : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: b :: Γ) u), (liftEnv2 envMap v).size ≤ 2
  | _, .zero => by simp [liftEnv2, Expr.size]
  | _, .succ .zero => by simp [liftEnv2, Expr.size]
  | _, .succ (.succ w) => by simp only [liftEnv2, exprWk1_size]; exact hEnv w

private theorem liftEnvFst_size_le {S : Sig} {O : Ops S} {a rStTy : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: Γ) u), (liftEnvFst (rStTy := rStTy) envMap v).size ≤ 2
  | _, .zero => by simp [liftEnvFst, Expr.size]
  | _, .succ w => by simp only [liftEnvFst, exprWk1_size]; exact hEnv w

private theorem liftEnvFold_size_le {S : Sig} {O : Ops S} {a b rStTy : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: b :: Γ) u), (liftEnvFold (rStTy := rStTy) envMap v).size ≤ 2
  | _, .zero => by simp [liftEnvFold, Expr.size]
  | _, .succ .zero => by simp [liftEnvFold, Expr.size]
  | _, .succ (.succ w) => by simp only [liftEnvFold, exprWk1_size]; exact hEnv w

private theorem liftEnvPred2_size_le {S : Sig} {O : Ops S} {a x : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: Γ) u), (liftEnvPred2 (x := x) envMap v).size ≤ 2
  | _, .zero => by simp [liftEnvPred2, Expr.size]
  | _, .succ w => by simp only [liftEnvPred2, exprWk1_size]; exact hEnv w

private theorem liftEnvMk3_size_le {S : Sig} {O : Ops S} {a y x : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: Γ) u), (liftEnvMk3 (y := y) (x := x) envMap v).size ≤ 2
  | _, .zero => by simp [liftEnvMk3, Expr.size]
  | _, .succ w => by simp only [liftEnvMk3, exprWk1_size]; exact hEnv w

private theorem substExpr_size_le {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2)
    {t : Ty S} (e : Expr O Γ t) :
    (substExpr envMap e).size ≤ 2 * e.size := by
  induction e generalizing Δ with
  | var v =>
    have hv := hEnv v
    simp only [substExpr, Expr.size]; omega
  | unit | bool _ | nat _ | none | nil =>
    simp only [substExpr, Expr.size]; omega
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2
  | and _ _ ih1 ih2 | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2
  | appendL _ _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    have h1 := ih1 hEnv; have h2 := ih2 hEnv
    simp only [substExpr, Expr.size]; omega
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih | op _ _ ih =>
    have h1 := ih hEnv
    simp only [substExpr, Expr.size]; omega
  | ite _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    have hc := ihc hEnv; have ha := iha hEnv; have hb := ihb hEnv
    simp only [substExpr, Expr.size]; omega
  | caseOpt _ _ _ ihe ihn ihs =>
    have he := ihe hEnv; have hn := ihn hEnv; have hs := ihs (liftEnv1_size_le hEnv)
    simp only [substExpr, Expr.size]; omega
  | caseSum _ _ _ ihe ihl ihr =>
    have he := ihe hEnv; have hl := ihl (liftEnv1_size_le hEnv); have hr := ihr (liftEnv1_size_le hEnv)
    simp only [substExpr, Expr.size]; omega
  | letE _ _ ihe ihb =>
    have he := ihe hEnv; have hb := ihb (liftEnv1_size_le hEnv)
    simp only [substExpr, Expr.size]; omega
  | findB _ _ _ ihl ihp | anyB _ _ _ ihl ihp | mapB _ _ _ ihl ihp =>
    have hl := ihl hEnv; have hp := ihp (liftEnv1_size_le hEnv)
    simp only [substExpr, Expr.size]; omega
  | foldrB _ _ _ _ ihl ihz ihf =>
    have hl := ihl hEnv; have hz := ihz hEnv; have hf := ihf (liftEnv2_size_le hEnv)
    simp only [substExpr, Expr.size]; omega

@[simp] private theorem callBinaryComp_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {a b c : Ty S} {Δ : List (Ty S)} (m : Comp O I [a, b] c) :
    (callBinaryComp (Δ := Δ) m).size = m.size + 8 := by
  simp only [callBinaryComp, Comp.size, Comp.renameM_size, Expr.size]; omega

@[simp] private theorem liftFsExpr_size {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (e : Expr (atomicFsOps ℓ Pt C encT) Γ t) :
    (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam) e).size = e.size := by
  induction e with
  | op o a ih =>
    change (liftFsExpr a).size + (atomicFsOps ℓ Pt C encT).opSize o + 1 =
      a.size + (atomicFsOps ℓ Pt C encT).opSize o + 1
    rw [ih]
  | _ => simp only [liftFsExpr, Expr.size, *]

@[simp] private theorem liftBaseSamp_size {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    (s : UniformSamplerTag ReductionDsl.AtomicBaseUnif)
    (e : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ
      ((ReductionDsl.atomicBaseSamplers ℓ Pt).sDom s)) :
    (liftBaseSamp s e).size = e.size + 1 := by
  rcases s with _ | _ | (_ | _ | _) <;> simp [liftBaseSamp, Comp.size]

@[simp] private theorem liftFsCoinComp_size {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp (atomicFsOps ℓ Pt C encT) (coinOnlyBaseIface ℓ Pt) Γ t) :
    (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) c).size = c.size := by
  induction c with
  | query g _ => exact nomatch g
  | _ => simp [liftFsCoinComp, Comp.size, *]

@[simp] private theorem liftFsSlotComp_size {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c).size = c.size := by
  induction c <;> simp [liftFsSlotComp, Comp.size, *]

private theorem liftNoQuerySlotComp_none_size_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    (liftNoQuerySlotComp (Dh := Dh) (encPt := encPt) (lam := lam) .none .none c).size ≤ c.size := by
  induction c with
  | query g e =>
    have he := one_le_exprSize e
    cases g <;> (simp only [liftNoQuerySlotComp, Comp.size, Expr.renameM_size, Expr.size]; omega)
  | _ =>
    simp only [liftNoQuerySlotComp, Comp.size, liftFsExpr_size, liftBaseSamp_size]; omega

private theorem compilePureExpr_sizeW_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : Computational.Proofs.ReductionDsl.FsAtomicMacros.PureMacroBundle O₁ O₂ I₁ I₂)
    (opS : O₁.Op → ℕ) (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureExpr M e).size ≤ exprSizeW opS e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp only [compilePureExpr, Expr.size, exprSizeW]; omega
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | tget _ _ ih1 ih2 | letE _ _ ih1 ih2 | findB _ _ _ ih1 ih2 | anyB _ _ _ ih1 ih2
  | mapB _ _ _ ih1 ih2 =>
    simp only [compilePureExpr, Expr.size, exprSizeW]; omega
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [compilePureExpr, Expr.size, exprSizeW]; omega
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb
  | foldrB _ _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp only [compilePureExpr, Expr.size, exprSizeW]; omega
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureExpr, Expr.size, Expr.wkTop1, Expr.renameM_size, exprSizeW]; omega

private theorem compilePureComp_sizeW_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : Computational.Proofs.ReductionDsl.FsAtomicMacros.PureMacroBundle O₁ O₂ I₁ I₂)
    (opS : O₁.Op → ℕ) (sS : I₁.smp.Samp → ℕ) (qS : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ sS s)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ qS g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureComp M c).size ≤ compSizeW opS sS qS c := by
  induction c with
  | ret e =>
    have he := compilePureExpr_sizeW_le M opS hOp e
    simp only [compilePureComp, Comp.size, compSizeW]; omega
  | bind _ _ ihc ihk =>
    simp only [compilePureComp, Comp.size, compSizeW]; omega
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := compilePureExpr_sizeW_le M opS hOp b
    simp only [compilePureComp, Comp.size, compSizeW]; omega
  | sample s e =>
    have he := compilePureExpr_sizeW_le M opS hOp e
    have hs := hSamp s
    simp only [compilePureComp, Comp.size,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, Comp.renameM_size, compSizeW]
    omega
  | query g e =>
    have he := compilePureExpr_sizeW_le M opS hOp e
    have hq := hQuery g
    simp only [compilePureComp, Comp.size,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, Comp.renameM_size, compSizeW]
    omega
  | iter _ e _ ihb | findM _ e _ ihb | anyM _ e _ ihb | mapM _ e _ ihb =>
    have he := compilePureExpr_sizeW_le M opS hOp e
    simp only [compilePureComp, Comp.size, compSizeW]; omega
  | consumeFirstM _ l _ mk ihp =>
    have hl := compilePureExpr_sizeW_le M opS hOp l
    have hmk := compilePureExpr_sizeW_le M opS hOp mk
    simp only [compilePureComp, Comp.size, compSizeW]; omega
  | foldM _ l z _ ihf =>
    have hl := compilePureExpr_sizeW_le M opS hOp l
    have hz := compilePureExpr_sizeW_le M opS hOp z
    simp only [compilePureComp, Comp.size, compSizeW]; omega

private def compQuerySum {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (qW : I.Tag → ℕ) : {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret _ | _, _, .sample _ _ => 0
  | _, _, .query g _ => qW g
  | _, _, .bind c k | _, _, .ite _ c k | _, _, .caseOpt _ c k | _, _, .caseSum _ c k =>
    compQuerySum qW c + compQuerySum qW k
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => compQuerySum qW b

@[simp] private theorem compQuerySum_renameM {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (qW : I.Tag → ℕ) {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u)
    {t : Ty S} (c : Comp O I Γ t) :
    compQuerySum qW (c.renameM ξ) = compQuerySum qW c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compQuerySum, *]

@[simp] private theorem compQuerySum_liftFsSlotComp {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} (qW : OTCCATag → ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    compQuerySum qW (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c) =
      compQuerySum qW c := by
  induction c <;> simp [liftFsSlotComp, compQuerySum, *]

private theorem compQuerySum_compilePureComp_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : Computational.Proofs.ReductionDsl.FsAtomicMacros.PureMacroBundle O₁ O₂ I₁ I₂)
    (qW₁ : I₁.Tag → ℕ) (qW₂ : I₂.Tag → ℕ)
    (hSamp : ∀ s, compQuerySum qW₂ (M.sampMacro s) = 0)
    (hQuery : ∀ g, compQuerySum qW₂ (M.queryMacro g) ≤ qW₁ g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    compQuerySum qW₂ (compilePureComp M c) ≤ compQuerySum qW₁ c := by
  induction c with
  | sample s e =>
    simp only [compilePureComp, compQuerySum,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, compQuerySum_renameM, hSamp s]
    omega
  | query g e =>
    have hq := hQuery g
    simp only [compilePureComp, compQuerySum,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, compQuerySum_renameM]
    omega
  | _ => simp only [compilePureComp, compQuerySum]; omega



@[simp] private theorem compListMNodes_renameM {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u)
    {t : Ty S} (c : Comp O I Γ t) :
    compListMNodes (c.renameM ξ) = compListMNodes c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compListMNodes, *]

@[simp] private theorem compListMNodes_liftFsSlotComp {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    compListMNodes (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c) =
      compListMNodes c := by
  induction c <;> simp [liftFsSlotComp, compListMNodes, *]

private theorem compListMNodes_compilePureComp_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : Computational.Proofs.ReductionDsl.FsAtomicMacros.PureMacroBundle O₁ O₂ I₁ I₂)
    (hSamp : ∀ s, compListMNodes (M.sampMacro s) = 0)
    (hQuery : ∀ g, compListMNodes (M.queryMacro g) = 0)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    compListMNodes (compilePureComp M c) ≤ compListMNodes c := by
  induction c with
  | sample s e =>
    simp only [compilePureComp, compListMNodes,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, compListMNodes_renameM, hSamp s]
    omega
  | query g e =>
    simp only [compilePureComp, compListMNodes,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1, compListMNodes_renameM, hQuery g]
    omega
  | _ => simp only [compilePureComp, compListMNodes]; omega

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

private theorem substNoQueryComp_size_le {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).size ≤ e.size + 2)
    {Γ Δ : List (Ty S)} {t : Ty S}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2)
    (c : Comp O I₁ Γ t) (hc : c.queries (fun _ => 1) (fun _ => 0) = 0) :
    (substNoQueryComp mapSamp envMap c hc).size ≤ 4 * c.size := by
  induction c generalizing Δ with
  | ret e =>
    have he := substExpr_size_le hEnv e; simp only [substNoQueryComp, Comp.size]; omega
  | bind c k ihc ihk =>
    have hc1 := ihc hEnv (by simp [Comp.queries] at hc; omega)
    have hk1 := ihk (liftEnv1_size_le hEnv) (by simp [Comp.queries] at hc; omega)
    simp only [substNoQueryComp, Comp.size]; omega
  | ite b c d ihc ihd =>
    have hb := substExpr_size_le hEnv b
    have hc1 := ihc hEnv (by simp [Comp.queries] at hc; omega)
    have hd1 := ihd hEnv (by simp [Comp.queries] at hc; omega)
    simp only [substNoQueryComp, Comp.size]; omega
  | caseOpt e n s ihn ihs =>
    have he := substExpr_size_le hEnv e
    have hn1 := ihn hEnv (by simp [Comp.queries] at hc; omega)
    have hs1 := ihs (liftEnv1_size_le hEnv) (by simp [Comp.queries] at hc; omega)
    simp only [substNoQueryComp, Comp.size]; omega
  | caseSum e l r ihl ihr =>
    have he := substExpr_size_le hEnv e
    have hl1 := ihl (liftEnv1_size_le hEnv) (by simp [Comp.queries] at hc; omega)
    have hr1 := ihr (liftEnv1_size_le hEnv) (by simp [Comp.queries] at hc; omega)
    simp only [substNoQueryComp, Comp.size]; omega
  | sample s e =>
    have he := substExpr_size_le hEnv e
    have he1 := one_le_exprSize e
    have hs := hSamp s (substExpr envMap e)
    simp only [substNoQueryComp, Comp.size]; omega
  | query _ _ => exfalso; simp [Comp.queries] at hc
  | iter n e body ih =>
    have he := substExpr_size_le hEnv e
    cases n with
    | zero => simp only [substNoQueryComp, Comp.size, Expr.size]; omega
    | succ n =>
      have hb := ih (liftEnv1_size_le hEnv) (by simp [Comp.queries] at hc; omega)
      simp only [substNoQueryComp, Comp.size]; omega
  | foldM K l z f ih =>
    have hl := substExpr_size_le hEnv l
    have hz := substExpr_size_le hEnv z
    cases K with
    | zero => simp only [substNoQueryComp, Comp.size, Expr.size]; omega
    | succ K =>
      have hf := ih (liftEnv2_size_le hEnv) (by simp [Comp.queries] at hc; omega)
      simp only [substNoQueryComp, Comp.size]; omega
  | findM K l p ih | anyM K l p ih | mapM K l p ih =>
    have hl := substExpr_size_le hEnv l
    cases K with
    | zero => simp only [substNoQueryComp, Comp.size, Expr.size]; omega
    | succ K =>
      have hp := ih (liftEnv1_size_le hEnv) (by simp [Comp.queries] at hc; omega)
      simp only [substNoQueryComp, Comp.size]; omega
  | consumeFirstM K l p mk ih =>
    have hl := substExpr_size_le hEnv l
    have hmk := substExpr_size_le (liftEnv1_size_le hEnv) mk
    cases K with
    | zero => simp only [substNoQueryComp, Comp.size, Expr.size]; omega
    | succ K =>
      have hp := ih (liftEnv1_size_le hEnv) (by simp [Comp.queries] at hc; omega)
      simp only [substNoQueryComp, Comp.size]; omega

private theorem substQueryComp_size_le_querySum {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {rStTy : Ty S}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (qW : I₁.Tag → ℕ)
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).size ≤ e.size + 2)
    (hQuery : ∀ g, (qImpl g).size ≤ qW g)
    {Γ Δ : List (Ty S)} {t : Ty S}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2)
    (rExpr : Expr O Δ rStTy) (hR : rExpr.size ≤ 9)
    (c : Comp O I₁ Γ t) :
    (substQueryComp mapSamp qImpl envMap rExpr c).size ≤
      12 * c.size + 45 * compListMNodes c + compQuerySum qW c := by
  induction c generalizing Δ with
  | ret e =>
    have he := substExpr_size_le hEnv e
    have he1 := one_le_exprSize e
    simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
  | bind c k ihc ihk =>
    have hc := ihc hEnv rExpr hR
    have hk := ihk (liftEnvFst_size_le hEnv) (.snd (.var .zero)) (by dsimp only [Expr.size]; omega)
    simp only [substQueryComp, Comp.size, compListMNodes, compQuerySum]; omega
  | ite b c d ihc ihd =>
    have hb := substExpr_size_le hEnv b
    have hc := ihc hEnv rExpr hR
    have hd := ihd hEnv rExpr hR
    simp only [substQueryComp, Comp.size, compListMNodes, compQuerySum]; omega
  | caseOpt e n s ihn ihs =>
    have he := substExpr_size_le hEnv e
    have hn := ihn hEnv rExpr hR
    have hs := ihs (liftEnv1_size_le hEnv) (exprWk1 rExpr) ((exprWk1_size rExpr).trans_le hR)
    simp only [substQueryComp, Comp.size, compListMNodes, compQuerySum]; omega
  | caseSum e l r ihl ihr =>
    have he := substExpr_size_le hEnv e
    have hl := ihl (liftEnv1_size_le hEnv) (exprWk1 rExpr) ((exprWk1_size rExpr).trans_le hR)
    have hr := ihr (liftEnv1_size_le hEnv) (exprWk1 rExpr) ((exprWk1_size rExpr).trans_le hR)
    simp only [substQueryComp, Comp.size, compListMNodes, compQuerySum]; omega
  | sample s e =>
    have he := substExpr_size_le hEnv e
    have he1 := one_le_exprSize e
    have hs := hSamp s (substExpr envMap e)
    simp only [substQueryComp, Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum]
    omega
  | query g e =>
    have he := substExpr_size_le hEnv e
    have he1 := one_le_exprSize e
    have hq := hQuery g
    simp only [substQueryComp, Comp.size, Expr.size, callBinaryComp_size, compListMNodes,
      compQuerySum]
    omega
  | iter n e body ihb =>
    have he := substExpr_size_le hEnv e
    have hb := ihb (liftEnvFst_size_le hEnv) (.snd (.var .zero)) (by dsimp only [Expr.size]; omega)
    simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
  | foldM K l z f ihf =>
    have hl := substExpr_size_le hEnv l
    have hz := substExpr_size_le hEnv z
    have hf := ihf (liftEnvFold_size_le hEnv) (.snd (.var (.succ .zero)))
      (by dsimp only [Expr.size]; omega)
    simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
  | findM K l p ihp =>
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hn := substNoQueryComp_size_le mapSamp hSamp hEnv (.findM (K + 1) l p) hc0
        simp only [Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum] at hn ⊢; omega
      · have hl := substExpr_size_le hEnv l
        have hl1 := one_le_exprSize l
        simp only [Comp.size, Expr.size, compListMNodes, compQuerySum]
        generalize hsq : (substQueryComp mapSamp qImpl _ _ p).size = sq
        have hp : sq ≤ 12 * p.size + 45 * compListMNodes p + compQuerySum qW p := by
          rw [← hsq]; exact ihp (liftEnvPred2_size_le hEnv) _ (by simp only [Expr.size]; omega)
        omega
  | anyM K l p ihp =>
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hn := substNoQueryComp_size_le mapSamp hSamp hEnv (.anyM (K + 1) l p) hc0
        simp only [Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum] at hn ⊢; omega
      · have hl := substExpr_size_le hEnv l
        have hl1 := one_le_exprSize l
        simp only [Comp.size, Expr.size, compListMNodes, compQuerySum]
        generalize hsq : (substQueryComp mapSamp qImpl _ _ p).size = sq
        have hp : sq ≤ 12 * p.size + 45 * compListMNodes p + compQuerySum qW p := by
          rw [← hsq]; exact ihp (liftEnvPred2_size_le hEnv) _ (by simp only [Expr.size]; omega)
        omega
  | mapM K l f ihf =>
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hn := substNoQueryComp_size_le mapSamp hSamp hEnv (.mapM (K + 1) l f) hc0
        simp only [Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum] at hn ⊢; omega
      · have hl := substExpr_size_le hEnv l
        have hl1 := one_le_exprSize l
        simp only [Comp.size, Expr.size, compListMNodes, compQuerySum]
        generalize hsq : (substQueryComp mapSamp qImpl _ _ f).size = sq
        have hf : sq ≤ 12 * f.size + 45 * compListMNodes f + compQuerySum qW f := by
          rw [← hsq]; exact ihf (liftEnvPred2_size_le hEnv) _ (by simp only [Expr.size]; omega)
        omega
  | consumeFirstM K l p mk ihp =>
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hn := substNoQueryComp_size_le mapSamp hSamp hEnv (.consumeFirstM (K + 1) l p mk) hc0
        simp only [Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum] at hn ⊢; omega
      · have hl := substExpr_size_le hEnv l
        have hl1 := one_le_exprSize l
        have hmk1 := one_le_exprSize mk
        simp only [Comp.size, Expr.size, compListMNodes, compQuerySum]
        generalize hsmk : (substExpr _ mk).size = smk
        have hmk : smk ≤ 2 * mk.size := by
          rw [← hsmk]; exact substExpr_size_le (liftEnvMk3_size_le hEnv) mk
        generalize hsq : (substQueryComp mapSamp qImpl _ _ p).size = sq
        have hp : sq ≤ 12 * p.size + 45 * compListMNodes p + compQuerySum qW p := by
          rw [← hsq]; exact ihp (liftEnvPred2_size_le hEnv) _ (by simp only [Expr.size]; omega)
        omega

private theorem compQuerySum_compilePureAuxComp_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (qW₁ : I₁.Tag → ℕ) (qW₂ : I₂.Tag → ℕ)
    (hSamp : ∀ s, compQuerySum qW₂ (M.sampMacro s) = 0)
    (hQuery : ∀ g, compQuerySum qW₂ (M.queryMacro g) ≤ qW₁ g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    compQuerySum qW₂ (compilePureAuxComp M c) ≤ compQuerySum qW₁ c := by
  induction c with
  | sample s e =>
    simp only [compilePureAuxComp, compQuerySum,
      Computational.Proofs.ReductionDsl.MacroLift.callMacroAux, compQuerySum_renameM, hSamp s]
    omega
  | query g e =>
    have hq := hQuery g
    simp only [compilePureAuxComp, compQuerySum,
      Computational.Proofs.ReductionDsl.MacroLift.callMacroAux, compQuerySum_renameM]
    omega
  | _ => simp only [compilePureAuxComp, compQuerySum]; omega

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
      Computational.Proofs.ReductionDsl.MacroLift.callMacroAux, compListMNodes_renameM,
      hSamp s]
    omega
  | query g e =>
    simp only [compilePureAuxComp, compListMNodes,
      Computational.Proofs.ReductionDsl.MacroLift.callMacroAux, compListMNodes_renameM,
      hQuery g]
    omega
  | _ => simp only [compilePureAuxComp, compListMNodes]; omega

private theorem compSizeW_querySum_le_32 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ) (qW : I.Tag → ℕ)
    (hQ : ∀ g, 120 + qW g ≤ 32 * qS g)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    12 * compSizeW opS sS (fun _ => 10) c + 45 * compListMNodes c + compQuerySum qW c ≤
      32 * compSizeW opS sS qS c := by
  induction c with
  | query g e =>
    have hq := hQ g
    simp only [compSizeW, compListMNodes, compQuerySum]; omega
  | findM K l p ih | anyM K l p ih | mapM K l p ih =>
    have hl := one_le_exprSizeW opS l
    have hk := ReductionDsl.one_le_bits K
    simp only [compSizeW, compListMNodes, compQuerySum]; omega
  | consumeFirstM K l p mk ih =>
    have hl := one_le_exprSizeW opS l
    have hmk := one_le_exprSizeW opS mk
    have hk := ReductionDsl.one_le_bits K
    simp only [compSizeW, compListMNodes, compQuerySum]; omega
  | _ => simp only [compSizeW, compListMNodes, compQuerySum]; omega

private theorem substQueryRed_compilePureAuxRed_size_le
    {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι₁ ι₂ κ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {G : OracleSpec κ}
    {I₁ : Iface S₁ T₁} {I₂ : Iface S₂ T₁} {I₃ : Iface S₂ T₂}
    {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G} {auxT rStTy : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : Computational.Proofs.ReductionDsl.PureAuxMacroLift.PureAuxAdapters
      M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (rInit : Expr O₂ [rIn₂] rStTy) (hrInit : rInit.size ≤ 9)
    (mapSamp : ∀ (s : I₂.smp.Samp) {Δ : List (Ty S₂)},
      Expr O₂ Δ (I₂.smp.sDom s) → Comp O₂ I₃ Δ (I₂.smp.sTy s))
    (qImpl : (g : I₂.Tag) → Comp O₂ I₃ [I₂.dom g, rStTy] (.prod (I₂.cod g) rStTy))
    (opS : O₁.Op → ℕ) (sS : I₁.smp.Samp → ℕ) (qS : I₁.Tag → ℕ)
    (qW₁ : I₁.Tag → ℕ) (qW₂ : I₂.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ sS s)
    (hQuery0 : ∀ g, (M.queryMacro g).size + 2 ≤ 10)
    (hMapSamp : ∀ s {Δ} (e : Expr O₂ Δ _), (mapSamp s e).size ≤ e.size + 2)
    (hQImpl : ∀ g, (qImpl g).size ≤ qW₂ g)
    (hSampQ : ∀ s, compQuerySum qW₂ (M.sampMacro s) = 0)
    (hQueryQ : ∀ g, compQuerySum qW₂ (M.queryMacro g) ≤ qW₁ g)
    (hSampL : ∀ s, compListMNodes (M.sampMacro s) = 0)
    (hQueryL : ∀ g, compListMNodes (M.queryMacro g) = 0)
    (hWQ : ∀ g, 120 + qW₁ g ≤ 32 * qS g)
    (hAd : A.splitIn.size + A.adaptAIn.size + A.adaptQ.size + A.adaptR.size +
      A.adaptAOut.size + A.adaptOut.size ≤ 340) :
    (substQueryRed rInit mapSamp qImpl (compilePureAuxRed M A R)).size ≤
      32 * (compSizeW opS sS qS R.init + compSizeW opS sS qS R.handle +
        compSizeW opS sS qS R.finish + 400) := by
  let R' := compilePureAuxRed M A R
  have hEnv1 : ∀ ⦃u⦄ (v : Var [rIn₂] u), (envId1 (O := O₂) v).size ≤ 2
    | _, .zero => by simp only [envId1, Expr.size]; omega
  have hEnv2 : ∀ {a b : Ty S₂} ⦃u⦄ (v : Var [a, b] u),
      (envFst2 (O := O₂) (r := rStTy) v).size ≤ 2
    | _, _, _, .zero => by simp only [envFst2, Expr.size]; omega
    | _, _, _, .succ .zero => by simp only [envFst2, Expr.size]; omega
  have hi := substQueryComp_size_le_querySum mapSamp qImpl qW₂ hMapSamp hQImpl hEnv1 rInit hrInit R'.init
  have hh := substQueryComp_size_le_querySum mapSamp qImpl qW₂ hMapSamp hQImpl hEnv2
    (.snd (.var .zero)) (by dsimp only [Expr.size]; omega) R'.handle
  have hf := substQueryComp_size_le_querySum mapSamp qImpl qW₂ hMapSamp hQImpl hEnv2
    (.snd (.var .zero)) (by dsimp only [Expr.size]; omega) R'.finish
  have hRsize := compilePureAuxRed_size_le M A R opS sS (fun _ => 10) hOp hSamp hQuery0
  have hRsum : R'.init.size + R'.handle.size + R'.finish.size = R'.size := rfl
  have hLi : compListMNodes R'.init ≤ compListMNodes R.init := by
    dsimp [R', compilePureAuxRed, Comp.wkTop2]
    simp only [compListMNodes_renameM, zero_add]
    exact compListMNodes_compilePureAuxComp_le M hSampL hQueryL R.init
  have hLh : compListMNodes R'.handle ≤ compListMNodes R.handle := by
    dsimp [R', compilePureAuxRed, Comp.wkTop3]
    simp only [compListMNodes_renameM, zero_add]
    exact compListMNodes_compilePureAuxComp_le M hSampL hQueryL R.handle
  have hLf : compListMNodes R'.finish ≤ compListMNodes R.finish := by
    dsimp [R', compilePureAuxRed, Comp.wkTop3]
    simp only [compListMNodes_renameM, zero_add]
    exact compListMNodes_compilePureAuxComp_le M hSampL hQueryL R.finish
  have hQi : compQuerySum qW₂ R'.init ≤ compQuerySum qW₁ R.init := by
    dsimp [R', compilePureAuxRed, Comp.wkTop2]
    simp only [compQuerySum, compQuerySum_renameM, zero_add, add_zero]
    exact compQuerySum_compilePureAuxComp_le M qW₁ qW₂ hSampQ hQueryQ R.init
  have hQh : compQuerySum qW₂ R'.handle ≤ compQuerySum qW₁ R.handle := by
    dsimp [R', compilePureAuxRed, Comp.wkTop3]
    simp only [compQuerySum, compQuerySum_renameM, zero_add, add_zero]
    exact compQuerySum_compilePureAuxComp_le M qW₁ qW₂ hSampQ hQueryQ R.handle
  have hQf : compQuerySum qW₂ R'.finish ≤ compQuerySum qW₁ R.finish := by
    dsimp [R', compilePureAuxRed, Comp.wkTop3]
    simp only [compQuerySum, compQuerySum_renameM, zero_add, add_zero]
    exact compQuerySum_compilePureAuxComp_le M qW₁ qW₂ hSampQ hQueryQ R.finish
  have hBi := compSizeW_querySum_le_32 opS sS qS qW₁ hWQ R.init
  have hBh := compSizeW_querySum_le_32 opS sS qS qW₁ hWQ R.handle
  have hBf := compSizeW_querySum_le_32 opS sS qS qW₁ hWQ R.finish
  dsimp only [R'] at hi hh hf hRsum hLi hLh hLf hQi hQh hQf
  dsimp only [CostedReduction.size, substQueryRed]
  simp only [Comp.size, Expr.size]
  omega

private theorem compQuerySum_const {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (w : ℕ) {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compQuerySum (fun _ => w) c = w * compQueryCount c := by
  induction c with
  | query _ _ => simp only [compQuerySum, compQueryCount, Nat.mul_one]
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp only [compQuerySum, compQueryCount, ih1, ih2, Nat.left_distrib]
  | iter _ _ _ ih | foldM _ _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih =>
    simp only [compQuerySum, compQueryCount, ih]
  | ret _ | sample _ _ =>
    simp only [compQuerySum, compQueryCount, Nat.mul_zero]

private theorem compSizeW_ten_add_queryCount {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ) (q₀ : ℕ)
    (hQ : ∀ g, q₀ + 10 ≤ qS g)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compSizeW opS sS (fun _ => 10) c + q₀ * compQueryCount c ≤ compSizeW opS sS qS c := by
  induction c with
  | query g e =>
    have hq := hQ g
    simp only [compSizeW, compQueryCount, Nat.mul_one]; omega
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp only [compSizeW, compQueryCount, Nat.left_distrib]; omega
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih =>
    simp only [compSizeW, compQueryCount]; omega
  | ret _ | sample _ _ =>
    simp only [compSizeW, compQueryCount, Nat.mul_zero]; omega

private theorem substQueryComp_size_le_5 {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {rStTy : Ty S}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (qW : I₁.Tag → ℕ)
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).size ≤ e.size + 1)
    (hQuery : ∀ g, (qImpl g).size + 6 ≤ qW g)
    {Γ Δ : List (Ty S)} {t : Ty S}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).size ≤ 2)
    (rExpr : Expr O Δ rStTy) (hR : rExpr.size ≤ 3)
    (c : Comp O I₁ Γ t) :
    (substQueryComp mapSamp qImpl envMap rExpr c).size ≤
      5 * c.size + 100 * compListMNodes c + compQuerySum qW c := by
  have hSamp2 : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).size ≤ e.size + 2 :=
    fun s {_} e => (hSamp s e).trans (Nat.le_succ _)
  induction c generalizing Δ with
  | ret e =>
    have he := substExpr_size_le hEnv e
    have he1 := one_le_exprSize e
    simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
  | bind c k ihc ihk =>
    have hc := ihc hEnv rExpr hR
    have hk := ihk (liftEnvFst_size_le hEnv) (.snd (.var .zero)) (by dsimp only [Expr.size]; omega)
    simp only [substQueryComp, Comp.size, compListMNodes, compQuerySum]; omega
  | ite b c d ihc ihd =>
    have hb := substExpr_size_le hEnv b
    have hc := ihc hEnv rExpr hR
    have hd := ihd hEnv rExpr hR
    simp only [substQueryComp, Comp.size, compListMNodes, compQuerySum]; omega
  | caseOpt e n s ihn ihs =>
    have he := substExpr_size_le hEnv e
    have hn := ihn hEnv rExpr hR
    have hs := ihs (liftEnv1_size_le hEnv) (exprWk1 rExpr) ((exprWk1_size rExpr).trans_le hR)
    simp only [substQueryComp, Comp.size, compListMNodes, compQuerySum]; omega
  | caseSum e l r ihl ihr =>
    have he := substExpr_size_le hEnv e
    have hl := ihl (liftEnv1_size_le hEnv) (exprWk1 rExpr) ((exprWk1_size rExpr).trans_le hR)
    have hr := ihr (liftEnv1_size_le hEnv) (exprWk1 rExpr) ((exprWk1_size rExpr).trans_le hR)
    simp only [substQueryComp, Comp.size, compListMNodes, compQuerySum]; omega
  | sample s e =>
    have he := substExpr_size_le hEnv e
    have he1 := one_le_exprSize e
    have hs := hSamp s (substExpr envMap e)
    simp only [substQueryComp, Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum]
    omega
  | query g e =>
    have he := substExpr_size_le hEnv e
    have he1 := one_le_exprSize e
    have hq := hQuery g
    simp only [substQueryComp, Comp.size, Expr.size, callBinaryComp_size, compListMNodes,
      compQuerySum]
    omega
  | iter n e body ihb =>
    have he := substExpr_size_le hEnv e
    have hb := ihb (liftEnvFst_size_le hEnv) (.snd (.var .zero)) (by dsimp only [Expr.size]; omega)
    simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
  | foldM K l z f ihf =>
    have hl := substExpr_size_le hEnv l
    have hz := substExpr_size_le hEnv z
    have hf := ihf (liftEnvFold_size_le hEnv) (.snd (.var (.succ .zero)))
      (by dsimp only [Expr.size]; omega)
    simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
  | findM K l p ihp =>
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hn := substNoQueryComp_size_le mapSamp hSamp2 hEnv (.findM (K + 1) l p) hc0
        simp only [Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum] at hn ⊢; omega
      · have hl := substExpr_size_le hEnv l
        simp only [Comp.size, Expr.size, compListMNodes, compQuerySum]
        generalize hsq : (substQueryComp mapSamp qImpl _ _ p).size = sq
        have hp : sq ≤ 5 * p.size + 100 * compListMNodes p + compQuerySum qW p := by
          rw [← hsq]; exact ihp (liftEnvPred2_size_le hEnv) _ (by simp only [Expr.size]; omega)
        omega
  | anyM K l p ihp =>
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hn := substNoQueryComp_size_le mapSamp hSamp2 hEnv (.anyM (K + 1) l p) hc0
        simp only [Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum] at hn ⊢; omega
      · have hl := substExpr_size_le hEnv l
        simp only [Comp.size, Expr.size, compListMNodes, compQuerySum]
        generalize hsq : (substQueryComp mapSamp qImpl _ _ p).size = sq
        have hp : sq ≤ 5 * p.size + 100 * compListMNodes p + compQuerySum qW p := by
          rw [← hsq]; exact ihp (liftEnvPred2_size_le hEnv) _ (by simp only [Expr.size]; omega)
        omega
  | mapM K l f ihf =>
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hn := substNoQueryComp_size_le mapSamp hSamp2 hEnv (.mapM (K + 1) l f) hc0
        simp only [Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum] at hn ⊢; omega
      · have hl := substExpr_size_le hEnv l
        simp only [Comp.size, Expr.size, compListMNodes, compQuerySum]
        generalize hsq : (substQueryComp mapSamp qImpl _ _ f).size = sq
        have hf : sq ≤ 5 * f.size + 100 * compListMNodes f + compQuerySum qW f := by
          rw [← hsq]; exact ihf (liftEnvPred2_size_le hEnv) _ (by simp only [Expr.size]; omega)
        omega
  | consumeFirstM K l p mk ihp =>
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hn := substNoQueryComp_size_le mapSamp hSamp2 hEnv (.consumeFirstM (K + 1) l p mk) hc0
        simp only [Comp.size, Expr.size, exprWk1_size, compListMNodes, compQuerySum] at hn ⊢; omega
      · have hl := substExpr_size_le hEnv l
        simp only [Comp.size, Expr.size, compListMNodes, compQuerySum]
        generalize hsmk : (substExpr _ mk).size = smk
        have hmk : smk ≤ 2 * mk.size := by
          rw [← hsmk]; exact substExpr_size_le (liftEnvMk3_size_le hEnv) mk
        generalize hsq : (substQueryComp mapSamp qImpl _ _ p).size = sq
        have hp : sq ≤ 5 * p.size + 100 * compListMNodes p + compQuerySum qW p := by
          rw [← hsq]; exact ihp (liftEnvPred2_size_le hEnv) _ (by simp only [Expr.size]; omega)
        omega

private theorem substQueryRed_compilePureAuxRed_size_le_6
    {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι₁ ι₂ κ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {G : OracleSpec κ}
    {I₁ : Iface S₁ T₁} {I₂ : Iface S₂ T₁} {I₃ : Iface S₂ T₂}
    {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G} {auxT rStTy : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : Computational.Proofs.ReductionDsl.PureAuxMacroLift.PureAuxAdapters
      M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (rInit : Expr O₂ [rIn₂] rStTy) (hrInit : rInit.size ≤ 9)
    (mapSamp : ∀ (s : I₂.smp.Samp) {Δ : List (Ty S₂)},
      Expr O₂ Δ (I₂.smp.sDom s) → Comp O₂ I₃ Δ (I₂.smp.sTy s))
    (qImpl : (g : I₂.Tag) → Comp O₂ I₃ [I₂.dom g, rStTy] (.prod (I₂.cod g) rStTy))
    (opS : O₁.Op → ℕ) (sS : I₁.smp.Samp → ℕ) (qS : I₁.Tag → ℕ)
    (q₀ Q_max : ℕ)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ sS s)
    (hQuery0 : ∀ g, (M.queryMacro g).size + 2 ≤ 10)
    (hMapSamp : ∀ s {Δ} (e : Expr O₂ Δ _), (mapSamp s e).size ≤ e.size + 1)
    (hQImpl : ∀ g, (qImpl g).size + 6 ≤ Q_max)
    (hSampQ : ∀ s, compQuerySum (fun _ => Q_max) (M.sampMacro s) = 0)
    (hQueryQ : ∀ g, compQuerySum (fun _ => Q_max) (M.queryMacro g) ≤ Q_max)
    (hSampL : ∀ s, compListMNodes (M.sampMacro s) = 0)
    (hQueryL : ∀ g, compListMNodes (M.queryMacro g) = 0)
    (hqS : ∀ g, q₀ + 10 ≤ qS g)
    (hQMax : Q_max ≤ 5 * q₀ + 101000)
    (hAd : A.splitIn.size + A.adaptAIn.size + A.adaptQ.size + A.adaptR.size +
      A.adaptAOut.size + A.adaptOut.size ≤ 340) :
    (substQueryRed rInit mapSamp qImpl (compilePureAuxRed M A R)).size ≤
      5 * (compSizeW opS sS qS R.init + compSizeW opS sS qS R.handle +
        compSizeW opS sS qS R.finish + 400) + 200 +
      100 * (compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish) +
      101000 * (compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish) := by
  let R' := compilePureAuxRed M A R
  have hEnv1 : ∀ ⦃u⦄ (v : Var [rIn₂] u), (envId1 (O := O₂) v).size ≤ 2
    | _, .zero => by simp only [envId1, Expr.size]; omega
  have hEnv2 : ∀ {a b : Ty S₂} ⦃u⦄ (v : Var [a, b] u),
      (envFst2 (O := O₂) (r := rStTy) v).size ≤ 2
    | _, _, _, .zero => by simp only [envFst2, Expr.size]; omega
    | _, _, _, .succ .zero => by simp only [envFst2, Expr.size]; omega
  have hi : (substQueryComp mapSamp qImpl envId1 rInit R'.init).size ≤
      5 * R'.init.size + 100 * compListMNodes R'.init + compQuerySum (fun _ => Q_max) R'.init := by
    dsimp only [R', compilePureAuxRed]
    generalize Comp.bind (.ret (.snd (.var .zero))) _ = k_init
    have hSplit1 := one_le_exprSize A.splitIn
    have hSplitSub := substExpr_size_le hEnv1 A.splitIn
    have hk_init := substQueryComp_size_le_5 mapSamp qImpl (fun _ => Q_max) hMapSamp hQImpl
      (liftEnvFst_size_le hEnv1) (.snd (.var .zero)) (by dsimp only [Expr.size]; omega) k_init
    simp only [substQueryComp, Comp.size, Expr.size, compListMNodes, compQuerySum]
    omega
  have hh := substQueryComp_size_le_5 mapSamp qImpl (fun _ => Q_max) hMapSamp hQImpl hEnv2
    (.snd (.var .zero)) (by dsimp only [Expr.size]; omega) R'.handle
  have hf := substQueryComp_size_le_5 mapSamp qImpl (fun _ => Q_max) hMapSamp hQImpl hEnv2
    (.snd (.var .zero)) (by dsimp only [Expr.size]; omega) R'.finish
  have hRsize := compilePureAuxRed_size_le M A R opS sS (fun _ => 10) hOp hSamp hQuery0
  have hRsum : R'.init.size + R'.handle.size + R'.finish.size = R'.size := rfl
  have hLi : compListMNodes R'.init ≤ compListMNodes R.init := by
    dsimp [R', compilePureAuxRed, Comp.wkTop2]
    simp only [compListMNodes_renameM, zero_add]
    exact compListMNodes_compilePureAuxComp_le M hSampL hQueryL R.init
  have hLh : compListMNodes R'.handle ≤ compListMNodes R.handle := by
    dsimp [R', compilePureAuxRed, Comp.wkTop3]
    simp only [compListMNodes_renameM, zero_add]
    exact compListMNodes_compilePureAuxComp_le M hSampL hQueryL R.handle
  have hLf : compListMNodes R'.finish ≤ compListMNodes R.finish := by
    dsimp [R', compilePureAuxRed, Comp.wkTop3]
    simp only [compListMNodes_renameM, zero_add]
    exact compListMNodes_compilePureAuxComp_le M hSampL hQueryL R.finish
  have hQi : compQuerySum (fun _ => Q_max) R'.init ≤ Q_max * compQueryCount R.init := by
    dsimp [R', compilePureAuxRed, Comp.wkTop2]
    simp only [compQuerySum, compQuerySum_renameM, zero_add, add_zero]
    exact (compQuerySum_compilePureAuxComp_le M (fun _ => Q_max) (fun _ => Q_max)
      hSampQ hQueryQ R.init).trans_eq (compQuerySum_const Q_max R.init)
  have hQh : compQuerySum (fun _ => Q_max) R'.handle ≤ Q_max * compQueryCount R.handle := by
    dsimp [R', compilePureAuxRed, Comp.wkTop3]
    simp only [compQuerySum, compQuerySum_renameM, zero_add, add_zero]
    exact (compQuerySum_compilePureAuxComp_le M (fun _ => Q_max) (fun _ => Q_max)
      hSampQ hQueryQ R.handle).trans_eq (compQuerySum_const Q_max R.handle)
  have hQf : compQuerySum (fun _ => Q_max) R'.finish ≤ Q_max * compQueryCount R.finish := by
    dsimp [R', compilePureAuxRed, Comp.wkTop3]
    simp only [compQuerySum, compQuerySum_renameM, zero_add, add_zero]
    exact (compQuerySum_compilePureAuxComp_le M (fun _ => Q_max) (fun _ => Q_max)
      hSampQ hQueryQ R.finish).trans_eq (compQuerySum_const Q_max R.finish)
  have hBi := compSizeW_ten_add_queryCount opS sS qS q₀ hqS R.init
  have hBh := compSizeW_ten_add_queryCount opS sS qS q₀ hqS R.handle
  have hBf := compSizeW_ten_add_queryCount opS sS qS q₀ hqS R.finish
  have hQsum : Q_max * compQueryCount R.init + Q_max * compQueryCount R.handle +
      Q_max * compQueryCount R.finish ≤
      5 * (q₀ * compQueryCount R.init + q₀ * compQueryCount R.handle +
        q₀ * compQueryCount R.finish) +
      101000 * (compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish) := by
    calc Q_max * compQueryCount R.init + Q_max * compQueryCount R.handle +
          Q_max * compQueryCount R.finish
      _ = Q_max * (compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish) := by
          ring
      _ ≤ (5 * q₀ + 101000) *
            (compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish) :=
          Nat.mul_le_mul_right _ hQMax
      _ = 5 * (q₀ * compQueryCount R.init + q₀ * compQueryCount R.handle +
            q₀ * compQueryCount R.finish) +
          101000 * (compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish) := by
          ring
  generalize q₀ * compQueryCount R.init = qci at hBi hQsum
  generalize q₀ * compQueryCount R.handle = qch at hBh hQsum
  generalize q₀ * compQueryCount R.finish = qcf at hBf hQsum
  generalize Q_max * compQueryCount R.init = qmi at hQi hQsum
  generalize Q_max * compQueryCount R.handle = qmh at hQh hQsum
  generalize Q_max * compQueryCount R.finish = qmf at hQf hQsum
  dsimp only [R'] at hi hh hf hRsum hLi hLh hLf hQi hQh hQf
  dsimp only [CostedReduction.size, substQueryRed]
  simp only [Comp.size, Expr.size]
  omega

/-! ### Concrete Router Handler `.size` Bounds -/

section ConcreteRouterSize

open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_mul_le size_le_budget_of_log_cost)
open Computational.Proofs.ReductionDsl.FsAtomicBounds (hybOpMacro_size_le swOpMacro_size_le
  prgSampMacro_size_le multiSampMacro_size_le multiQueryMacro_size_le
  slotSwSampMacro_size_le slotSwQueryMacro_size_le lPubOfExpr_size)

local macro "unfold_dsl_vars" : tactic =>
  `(tactic| try dsimp only [Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, Expr.v7])

private theorem bits_le_of_le_add_const {x P c : ℕ} (hP : 1 ≤ P) (hx : x ≤ P + c) :
    bits x ≤ bits P + bits (c + 1) := by
  have hmul : x ≤ P * (c + 1) := by nlinarith
  exact (bits_mono hmul).trans (bits_mul_le P (c + 1))

private theorem bits_router_params {j qep qR B0 : ℕ} (la stage : Bool)
    (hj : j ≤ (qep + 2) * B0 + B0 * B0) (hqR : qR ≤ B0) :
    let P := qep + qR + B0 + 1
    let N := authHopCutoff maxForwardJumps qR la
    let qSim := 2 * qR + 4
    let jPosR := if stage then N else 0
    let mSlotR := if stage then N else 0
    bits N ≤ bits P + 16 ∧ bits qSim ≤ bits P + 3 ∧
      bits jPosR ≤ bits P + 16 ∧ bits mSlotR ≤ bits P + 16 ∧
      bits j ≤ 2 * bits P + 2 := by
  intro P N qSim jPosR mSlotR
  have hP1 : 1 ≤ P := by dsimp [P]; omega
  have hmfj : maxForwardJumps = 25000 := rfl
  have hN_le : N ≤ P + 25002 := by
    dsimp [N, authHopCutoff, P]; rw [hmfj]; split_ifs <;> omega
  have hbN : bits N ≤ bits P + 16 := by
    have h15 : bits (25002 + 1) = 15 := by decide
    have := bits_le_of_le_add_const hP1 hN_le
    omega
  have hqSim_le : qSim ≤ P * 6 := by dsimp [qSim, P]; omega
  have hbqSim : bits qSim ≤ bits P + 3 := by
    have h6 : bits 6 = 3 := by decide
    have := (bits_mono hqSim_le).trans (bits_mul_le P 6)
    omega
  have hbjPos : bits jPosR ≤ bits P + 16 := by
    dsimp [jPosR]; split_ifs
    · exact hbN
    · have : bits 0 = 1 := rfl; omega
  have hbmSlot : bits mSlotR ≤ bits P + 16 := by
    dsimp [mSlotR]; split_ifs
    · exact hbN
    · have : bits 0 = 1 := rfl; omega
  have hj_le : j ≤ 2 * (P * P) := by dsimp [P]; nlinarith
  have hbj : bits j ≤ 2 * bits P + 2 := by
    have h2 : bits 2 = 2 := by decide
    have hmul1 := (bits_mono hj_le).trans (bits_mul_le 2 (P * P))
    have hmul2 := bits_mul_le P P
    omega
  exact ⟨hbN, hbqSim, hbjPos, hbmSlot, hbj⟩

private theorem slotOtccaImpl_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (nf : Bool) {qSim P : ℕ} (hqS : bits qSim ≤ bits P + 3) (g : OTCCATag) :
    (slotOtccaImpl ℓ Pt C Dh encPt encT idOf lam nf qSim g).size ≤ 9500 + 2 * bits P := by
  have hOp : ∀ o, ((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).opMacro o).size + 1 ≤ 650 :=
    swOpMacro_size_le C ℓ encT idOf
  have hSamp : ∀ s, ((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).size + 2 ≤ 650 :=
    slotSwSampMacro_size_le C ℓ encT idOf hℓ
  have hQuery : ∀ g', ((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g').size + 2 ≤ 650 :=
    slotSwQueryMacro_size_le C ℓ encT idOf
  cases g with
  | enc =>
    dsimp only [slotOtccaImpl]
    simp only [Comp.size, Expr.size]
    erw [Comp.renameM_size]
    have h1 := liftNoQuerySlotComp_none_size_le (Dh := Dh) (encPt := encPt) (lam := lam)
      (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC
          C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim (Γ := [])))
    have h2 := compilePureComp_sizeW_le (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
      (fun _ => 650) (fun _ => 650) (fun _ => 650) hOp hSamp hQuery
      (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC
        C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim (Γ := []))
    have h3 : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC
          C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim (Γ := [])) ≤ 9450 + 2 * bits P := by
      dsimp only [CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC,
        CryptoGames.Ratchet.LibsignalInst.Costed.slotKeyOfC,
        CryptoGames.Ratchet.LibsignalInst.Costed.sampleSlotMsgKeyC,
        CryptoGames.Ratchet.LibsignalInst.Costed.sampleSlotIdealC,
        CryptoGames.Ratchet.LibsignalInst.Costed.isSomeE,
        CryptoGames.Ratchet.LibsignalInst.Costed.saltOfE,
        CryptoGames.Ratchet.LibsignalInst.Costed.encKE,
        CryptoGames.Ratchet.LibsignalInst.Costed.eqSaltE]
      unfold_dsl_vars
      dsimp only [compSizeW, exprSizeW]; omega
    omega
  | dec =>
    dsimp only [slotOtccaImpl]
    simp only [Comp.size, Expr.size]
    erw [Comp.renameM_size]
    have h1 := liftNoQuerySlotComp_none_size_le (Dh := Dh) (encPt := encPt) (lam := lam)
      (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC
          C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim (Γ := [])))
    have h2 := compilePureComp_sizeW_le (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
      (fun _ => 650) (fun _ => 650) (fun _ => 650) hOp hSamp hQuery
      (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC
        C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim (Γ := []))
    have h3 : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC
          C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim (Γ := [])) ≤ 9450 + 2 * bits P := by
      dsimp only [CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC,
        CryptoGames.Ratchet.LibsignalInst.Costed.isSlotChalSaltE,
        CryptoGames.Ratchet.LibsignalInst.Costed.slotKeyOfC,
        CryptoGames.Ratchet.LibsignalInst.Costed.sampleSlotMsgKeyC,
        CryptoGames.Ratchet.LibsignalInst.Costed.orE,
        CryptoGames.Ratchet.LibsignalInst.Costed.eqSaltE,
        CryptoGames.Ratchet.LibsignalInst.Costed.saltOfE,
        CryptoGames.Ratchet.LibsignalInst.Costed.eqChalSomeE,
        CryptoGames.Ratchet.LibsignalInst.Costed.eqADE,
        CryptoGames.Ratchet.LibsignalInst.Costed.eqCE,
        CryptoGames.Ratchet.LibsignalInst.Costed.decKE]
      unfold_dsl_vars
      cases nf
      · have hite : ∀ {α : Type} (x y : α), (if false = true then x else y) = y := fun _ _ => rfl
        rw [hite]; dsimp only [compSizeW, exprSizeW]; omega
      · have hite : ∀ {α : Type} (x y : α), (if true = true then x else y) = x := fun _ _ => rfl
        rw [hite]; dsimp only [compSizeW, exprSizeW]; omega
    omega

section HybStepBounds

open _root_.CryptoGames.FSAEAD.Thm5.Costed (aeadDecE aeadEncE anyInTransitBody anyInTransitE appendKcE
  callC callE chainFromBody chainFromC challengeBody challsContainsBody challsContainsE
  corruptSenderBody decIdxBody deliverBody encIdxBody eqAdE eqCE eqME findInTransitBody
  findInTransitE genStepKcBody genUpToBody genUpToC hsB hsChalls hsCorrAt hsCorrKey hsEnded
  hsInTransit hsKeysT hsLastSent hsLf hsNKeys hsRecvIdx hsSkipped hsTy hsWin initHSE injectBody
  isCompromisedBody isCompromisedE isSomeE maxNatE mkHS orE prependNewSkippedBody prgGenE recAd
  recCt recIdx recMatchesE recMsg receiveBody removeFromTransitBody removeFromTransitE revealBody
  senderKeyBody skippedContainsE skippedRemoveBody skippedRemoveE stTy transmitBody withKcE
  withSkippedE)

local macro "HSigM" "(" Pt:term "," ℓ:term ")" : term =>
  `(CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header $Pt × LibsignalMsgPublicPart) Unit (Plain $ℓ) LCt)

local macro "HSampM" "(" Pt:term "," ℓ:term ")" : term =>
  `(ReductionDsl.unifSamplers (S := HSigM($Pt, $ℓ))
      CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))

private theorem genUpToC_sizeW_q_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface HSigM(Pt, ℓ) T} {Γ}
    {jPos P : ℕ} (hj : bits jPos ≤ bits P + 16)
    (qW : (I₀.withSamp HSampM(Pt, ℓ)).Tag → ℕ)
    (i : Expr _ Γ .nat) (s : Expr _ Γ stTy) :
    compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
      (genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos i s) ≤
      exprSizeW (fun _ => 650) i + exprSizeW (fun _ => 650) s + 8500 + 2 * bits P ∧
    compListMNodes
      (genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos i s) = 0 ∧
    compQuerySum qW
      (genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos i s) = 0 := by
  have _ := hj
  have hb1 : bits 1 = 1 := rfl
  have hb25001 : bits 25001 = 15 := by decide
  have hmfj : maxForwardJumps = 25000 := rfl
  have hstep : ∀ {Δ},
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
        (genStepKcBody (I₀ := I₀) (Γ := Δ)
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1) ≤ 6000 ∧
      compListMNodes
        (genStepKcBody (I₀ := I₀) (Γ := Δ)
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1) = 0 ∧
      compQuerySum qW
        (genStepKcBody (I₀ := I₀) (Γ := Δ)
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1) = 0 := by
    intro Δ
    dsimp only [genStepKcBody, appendKcE, prgGenE]
    unfold_dsl_vars
    dsimp only [compSizeW, exprSizeW, compListMNodes, compQuerySum]
    try simp only [Nat.reduceAdd]
    try simp only [hb1]
    refine ⟨by omega, trivial, trivial⟩
  dsimp only [genUpToC, genUpToBody, withKcE, hsNKeys, hsKeysT, callC]
  generalize hbs : genStepKcBody (I₀ := I₀)
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 (Γ := _) = bs
  have ⟨hs1, hs2, hs3⟩ : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) bs ≤ 6000 ∧
      compListMNodes bs = 0 ∧ compQuerySum qW bs = 0 := by rw [← hbs]; exact hstep
  unfold_dsl_vars
  dsimp only [compSizeW, exprSizeW, compListMNodes, compQuerySum]
  try simp only [hmfj]
  try simp only [Nat.reduceAdd]
  try simp only [hb25001]
  simp only [hs2, hs3]
  generalize hsb : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) bs = sbs at hs1 ⊢
  refine ⟨by omega, trivial, trivial⟩

private theorem senderKeyBody_sizeW_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface HSigM(Pt, ℓ) T} {Γ}
    {qSim P : ℕ} (hqS : bits qSim ≤ bits P + 3) :
    compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
      (senderKeyBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 qSim (Γ := Γ)) ≤ 4000 + 2 * bits P := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  dsimp only [senderKeyBody, revealBody, chainFromC, chainFromBody, hsCorrAt, hsCorrKey,
    hsLastSent, prgGenE, callC]
  unfold_dsl_vars
  dsimp only [compSizeW, exprSizeW]
  simp only [hb0, hb1, Nat.reduceAdd]; omega

private theorem receiveBody_sizeW_q_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface HSigM(Pt, ℓ) T} {Γ}
    {jPos mSlot P Q₀ : ℕ} (hj : bits jPos ≤ bits P + 16) (hm : bits mSlot ≤ bits P + 16)
    (la : Bool) (qW : (I₀.withSamp HSampM(Pt, ℓ)).Tag → ℕ)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp HSampM(Pt, ℓ)) Δ _))
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _),
          compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (f x) ≤
            exprSizeW (fun _ => 650) x + 700 ∧
          compListMNodes (f x) = 0 ∧ compQuerySum qW (f x) ≤ Q₀) :
    compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
      (receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos mSlot la specialDec (Γ := Γ)) ≤ 16500 + 6 * bits P ∧
    compListMNodes
      (receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos mSlot la specialDec (Γ := Γ)) = 0 ∧
    compQuerySum qW
      (receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos mSlot la specialDec (Γ := Γ)) ≤ 2 * Q₀ := by
  have _ := hm
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb25000 : bits 25000 = 15 := by decide
  have hdecB : ∀ {Δ},
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
        (decIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
          1 1 mSlot specialDec (Γ := Δ)) ≤ 2000 + 2 * bits P ∧
      compListMNodes
        (decIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
          1 1 mSlot specialDec (Γ := Δ)) = 0 ∧
      compQuerySum qW
        (decIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
          1 1 mSlot specialDec (Γ := Δ)) ≤ Q₀ := by
    intro Δ
    dsimp only [decIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt, aeadDecE, callE]
    cases specialDec with
    | none =>
      unfold_dsl_vars
      dsimp only [compSizeW, exprSizeW, compListMNodes, compQuerySum]
      simp only [hb0, hb1]; refine ⟨by omega, by simp, by omega⟩
    | some sD =>
      have ⟨hs1, hs2, hs3⟩ := hDec (Δ := .prod (.prod (.opt (CryptoGames.FSAEAD.Costed.bt .msg))
        (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
          (CryptoGames.FSAEAD.Costed.bt .ct)))) hsTy :: Δ)
        (.pair (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))
          (.snd (.snd (.snd (.fst .v0)))))
      dsimp only [Expr.v0, exprSizeW] at hs1 hs2 hs3
      unfold_dsl_vars
      dsimp only [compSizeW, exprSizeW, compListMNodes, compQuerySum]
      simp only [hb0, hb1, hs2]
      generalize hsdx : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (sD _) = sdx at hs1 ⊢
      generalize hsdq : compQuerySum qW (sD _) = sdq at hs3 ⊢
      refine ⟨by omega, by simp, by omega⟩
  dsimp only [receiveBody, skippedContainsE, skippedRemoveE, skippedRemoveBody, withSkippedE,
    isCompromisedE, isCompromisedBody, prependNewSkippedBody,
    orE, hsLastSent, hsCorrAt, hsRecvIdx, hsSkipped, callE, callC]
  generalize hgc :
    genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
      1 1 maxForwardJumps jPos _ _ = gc
  have ⟨hg1, hg2, hg3⟩ :
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) gc ≤ 8520 + 2 * bits P ∧
      compListMNodes gc = 0 ∧ compQuerySum qW gc = 0 := by
    rw [← hgc]
    refine And.imp_left (fun u1 => ?_) (genUpToC_sizeW_q_le (I₀ := I₀) C ℓ encT idOf hj qW _ _)
    unfold_dsl_vars; dsimp only [Expr.v0, exprSizeW] at u1; omega
  unfold_dsl_vars; dsimp only [Expr.v0, compSizeW, exprSizeW, compListMNodes, compQuerySum]
  generalize hd1 : decIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
    (Γ := stTy :: _) = d1
  have ⟨hd1s, hd1l, hd1q⟩ :
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) d1 ≤ 2000 + 2 * bits P ∧
      compListMNodes d1 = 0 ∧ compQuerySum qW d1 ≤ Q₀ := by rw [← hd1]; exact hdecB
  generalize hd2 : decIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot specialDec
    (Γ := _) = d2
  have ⟨hd2s, hd2l, hd2q⟩ :
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) d2 ≤ 2000 + 2 * bits P ∧
      compListMNodes d2 = 0 ∧ compQuerySum qW d2 ≤ Q₀ := by rw [← hd2]; exact hdecB
  try simp only [hmfj]
  try simp only [hb1]
  try simp only [hb25000]
  try simp only [Nat.reduceAdd]
  simp only [hg2, hg3, hd1l, hd2l]
  generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) gc = sgc at hg1 ⊢
  generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) d1 = sd1 at hd1s ⊢
  generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) d2 = sd2 at hd2s ⊢
  generalize compQuerySum qW d1 = qd1 at hd1q ⊢
  generalize compQuerySum qW d2 = qd2 at hd2q ⊢
  refine ⟨by omega, by simp, by omega⟩

private theorem encIdxBody_sizeW_q_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface HSigM(Pt, ℓ) T} {Δ}
    {mSlot P Q₀ : ℕ} (hm : bits mSlot ≤ bits P + 16)
    (qW : (I₀.withSamp HSampM(Pt, ℓ)).Tag → ℕ)
    (sampleIdeal : ∀ {Δ'}, Expr _ Δ' _ → Comp _ (I₀.withSamp HSampM(Pt, ℓ)) Δ' _)
    (specialEnc : Option (∀ {Δ'}, Expr _ Δ' _ → Comp _ (I₀.withSamp HSampM(Pt, ℓ)) Δ' _))
    (hId : ∀ {Δ'} (ia : Expr _ Δ' _),
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (sampleIdeal ia) ≤
        exprSizeW (fun _ => 650) ia + 700 ∧
      compListMNodes (sampleIdeal ia) = 0 ∧ compQuerySum qW (sampleIdeal ia) = 0)
    (hEnc : match specialEnc with
      | none => True
      | some f => ∀ {Δ'} (x : Expr _ Δ' _),
          compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (f x) ≤
            2 * exprSizeW (fun _ => 650) x + 1400 ∧
          compListMNodes (f x) = 0 ∧ compQuerySum qW (f x) ≤ Q₀) :
    compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
      (encIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 mSlot sampleIdeal specialEnc (Γ := Δ)) ≤ 3700 + 2 * bits P ∧
    compListMNodes
      (encIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 mSlot sampleIdeal specialEnc (Γ := Δ)) = 0 ∧
    compQuerySum qW
      (encIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 mSlot sampleIdeal specialEnc (Γ := Δ)) ≤ Q₀ := by
  have _ := hm
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  let Δ0 : List (Ty HSigM(Pt, ℓ)) :=
    .prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
      (CryptoGames.FSAEAD.Costed.bt .msg))) hsTy :: Δ
  have ⟨hi1, hi2, hi3⟩ := hId (Δ' := Δ0) (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
  dsimp only [Δ0, encIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt,
    aeadEncE, callE, Expr.v0, exprSizeW] at hi1 hi2 hi3 ⊢
  cases specialEnc with
  | none =>
    unfold_dsl_vars
    dsimp only [compSizeW, exprSizeW, compListMNodes, compQuerySum]
    simp only [hb0, hb1, hi2, hi3]
    generalize hidx : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (sampleIdeal _) = idx
      at hi1 ⊢
    refine ⟨by omega, trivial, by omega⟩
  | some sE =>
    have ⟨hs1, hs2, hs3⟩ := hEnc (Δ' := Δ0)
      (.pair (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0)))) (.snd (.snd (.fst .v0))))
    dsimp only [Δ0, Expr.v0, exprSizeW] at hs1 hs2 hs3
    unfold_dsl_vars
    dsimp only [compSizeW, exprSizeW, compListMNodes, compQuerySum]
    simp only [hb0, hb1, hi2, hi3, hs2]
    generalize hidx : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (sampleIdeal _) = idx
      at hi1 ⊢
    generalize hsex : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (sE _) = sex at hs1 ⊢
    generalize hseq : compQuerySum qW (sE _) = seq at hs3 ⊢
    refine ⟨by omega, trivial, by omega⟩

private theorem transmitBody_sizeW_q_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface HSigM(Pt, ℓ) T} {Γ}
    {jPos mSlot P Q₀ : ℕ} (hj : bits jPos ≤ bits P + 16) (hm : bits mSlot ≤ bits P + 16)
    (qW : (I₀.withSamp HSampM(Pt, ℓ)).Tag → ℕ)
    (sampleIdeal : ∀ {Δ'}, Expr _ Δ' _ → Comp _ (I₀.withSamp HSampM(Pt, ℓ)) Δ' _)
    (specialEnc : Option (∀ {Δ'}, Expr _ Δ' _ → Comp _ (I₀.withSamp HSampM(Pt, ℓ)) Δ' _))
    (hId : ∀ {Δ'} (ia : Expr _ Δ' _),
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (sampleIdeal ia) ≤
        exprSizeW (fun _ => 650) ia + 700 ∧
      compListMNodes (sampleIdeal ia) = 0 ∧ compQuerySum qW (sampleIdeal ia) = 0)
    (hEnc : match specialEnc with
      | none => True
      | some f => ∀ {Δ'} (x : Expr _ Δ' _),
          compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (f x) ≤
            2 * exprSizeW (fun _ => 650) x + 1400 ∧
          compListMNodes (f x) = 0 ∧ compQuerySum qW (f x) ≤ Q₀) :
    compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
      (transmitBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) ≤ 15000 + 5 * bits P ∧
    compListMNodes
      (transmitBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) = 0 ∧
    compQuerySum qW
      (transmitBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) ≤ Q₀ := by
  have _ := hm
  have hb1 : bits 1 = 1 := rfl
  dsimp only [transmitBody, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin,
    hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
  generalize hgc : genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) 1 1 maxForwardJumps jPos _ _ = gc
  have ⟨hg1, hg2, hg3⟩ :
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) gc ≤ 8520 + 2 * bits P ∧
      compListMNodes gc = 0 ∧ compQuerySum qW gc = 0 := by
    rw [← hgc]
    refine And.imp_left (fun u1 => ?_) (genUpToC_sizeW_q_le (I₀ := I₀) C ℓ encT idOf hj qW _ _)
    unfold_dsl_vars; dsimp only [Expr.v0, hsLastSent, exprSizeW] at u1
    simp only [hb1] at u1; omega
  generalize hex : encIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot sampleIdeal
    specialEnc (Γ := _) = ex
  have ⟨he1, he2, he3⟩ :
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) ex ≤ 3700 + 2 * bits P ∧
      compListMNodes ex = 0 ∧ compQuerySum qW ex ≤ Q₀ := by
    rw [← hex]; exact encIdxBody_sizeW_q_le C ℓ encT idOf hm qW sampleIdeal specialEnc hId hEnc
  unfold_dsl_vars
  dsimp only [Expr.v0, hsLastSent, compSizeW, exprSizeW, compListMNodes, compQuerySum]
  simp only [hb1, hg2, hg3, he2]
  generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) gc = sgc at hg1 ⊢
  generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) ex = sex at he1 ⊢
  generalize compQuerySum qW ex = qex at he3 ⊢
  refine ⟨by omega, trivial, by omega⟩

private theorem challengeBody_sizeW_q_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface HSigM(Pt, ℓ) T} {Γ}
    {jPos mSlot P Q₀ : ℕ} (hj : bits jPos ≤ bits P + 16) (hm : bits mSlot ≤ bits P + 16)
    (qW : (I₀.withSamp HSampM(Pt, ℓ)).Tag → ℕ)
    (sampleIdeal : ∀ {Δ'}, Expr _ Δ' _ → Comp _ (I₀.withSamp HSampM(Pt, ℓ)) Δ' _)
    (specialEnc : Option (∀ {Δ'}, Expr _ Δ' _ → Comp _ (I₀.withSamp HSampM(Pt, ℓ)) Δ' _))
    (hId : ∀ {Δ'} (ia : Expr _ Δ' _),
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (sampleIdeal ia) ≤
        exprSizeW (fun _ => 650) ia + 700 ∧
      compListMNodes (sampleIdeal ia) = 0 ∧ compQuerySum qW (sampleIdeal ia) = 0)
    (hEnc : match specialEnc with
      | none => True
      | some f => ∀ {Δ'} (x : Expr _ Δ' _),
          compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (f x) ≤
            2 * exprSizeW (fun _ => 650) x + 1400 ∧
          compListMNodes (f x) = 0 ∧ compQuerySum qW (f x) ≤ Q₀) :
    compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
      (challengeBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) ≤ 15000 + 5 * bits P ∧
    compListMNodes
      (challengeBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) = 0 ∧
    compQuerySum qW
      (challengeBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps jPos mSlot sampleIdeal specialEnc (Γ := Γ)) ≤ Q₀ := by
  have _ := hm
  have hb1 : bits 1 = 1 := rfl
  dsimp only [challengeBody, isSomeE, orE, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx,
    hsEnded, hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
  generalize hgc : genUpToC (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) 1 1 maxForwardJumps jPos _ _ = gc
  have ⟨hg1, hg2, hg3⟩ :
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) gc ≤ 8520 + 2 * bits P ∧
      compListMNodes gc = 0 ∧ compQuerySum qW gc = 0 := by
    rw [← hgc]
    refine And.imp_left (fun u1 => ?_) (genUpToC_sizeW_q_le (I₀ := I₀) C ℓ encT idOf hj qW _ _)
    unfold_dsl_vars; dsimp only [Expr.v0, hsLastSent, exprSizeW] at u1
    simp only [hb1] at u1; omega
  generalize hex : encIdxBody (I := I₀.withSamp HSampM(Pt, ℓ))
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot sampleIdeal
    specialEnc (Γ := _) = ex
  have ⟨he1, he2, he3⟩ :
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) ex ≤ 3700 + 2 * bits P ∧
      compListMNodes ex = 0 ∧ compQuerySum qW ex ≤ Q₀ := by
    rw [← hex]; exact encIdxBody_sizeW_q_le C ℓ encT idOf hm qW sampleIdeal specialEnc hId hEnc
  unfold_dsl_vars
  dsimp only [Expr.v0, hsLastSent, compSizeW, exprSizeW, compListMNodes, compQuerySum]
  simp only [hb1, hg2, hg3, he2]
  generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) gc = sgc at hg1 ⊢
  generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) ex = sex at he1 ⊢
  generalize compQuerySum qW ex = qex at he3 ⊢
  refine ⟨by omega, trivial, by omega⟩

private theorem deliverBody_sizeW_q_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface HSigM(Pt, ℓ) T} {Γ}
    {qSim jPos mSlot P Q₀ : ℕ} (hqS : bits qSim ≤ bits P + 3)
    (hj : bits jPos ≤ bits P + 16) (hm : bits mSlot ≤ bits P + 16)
    (la : Bool) (qW : (I₀.withSamp HSampM(Pt, ℓ)).Tag → ℕ)
    (specialDec : Option (∀ {Δ'}, Expr _ Δ' _ → Comp _ (I₀.withSamp HSampM(Pt, ℓ)) Δ' _))
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ'} (x : Expr _ Δ' _),
          compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (f x) ≤
            exprSizeW (fun _ => 650) x + 700 ∧
          compListMNodes (f x) = 0 ∧ compQuerySum qW (f x) ≤ Q₀) :
    compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
      (deliverBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) ≤ 23000 + 10 * bits P ∧
    compListMNodes
      (deliverBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) = 0 ∧
    compQuerySum qW
      (deliverBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) ≤ 2 * Q₀ := by
  have _ := hqS
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb25000 : bits 25000 = 15 := by decide
  dsimp only [deliverBody, findInTransitE, findInTransitBody, recMatchesE, challsContainsE,
    challsContainsBody, removeFromTransitE, removeFromTransitBody, isCompromisedE,
    isCompromisedBody, eqAdE, eqME, eqCE, orE, maxNatE, mkHS, hsB, hsLastSent, hsCorrAt,
    hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey,
    hsSkipped, recIdx, recAd, recMsg, recCt, callE, callC]
  generalize hrx : receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) 1 1 maxForwardJumps jPos mSlot la specialDec (Γ := _) = rx
  have ⟨hr1, hr2, hr3⟩ :
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) rx ≤ 16500 + 6 * bits P ∧
      compListMNodes rx = 0 ∧ compQuerySum qW rx ≤ 2 * Q₀ := by
    rw [← hrx]; exact receiveBody_sizeW_q_le C ℓ encT idOf hj hm la qW specialDec hDec
  unfold_dsl_vars
  dsimp only [compSizeW, exprSizeW, compListMNodes, compQuerySum]
  try simp only [hmfj]
  try simp only [hb1]
  try simp only [hb2]
  try simp only [hb25000]
  try simp only [Nat.reduceAdd]
  simp only [hr2]
  generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) rx = srx at hr1 ⊢
  generalize compQuerySum qW rx = qrx at hr3 ⊢
  refine ⟨by omega, trivial, by omega⟩

private theorem injectBody_sizeW_q_le {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface HSigM(Pt, ℓ) T} {Γ}
    {qSim jPos mSlot P Q₀ : ℕ} (hqS : bits qSim ≤ bits P + 3)
    (hj : bits jPos ≤ bits P + 16) (hm : bits mSlot ≤ bits P + 16)
    (la : Bool) (qW : (I₀.withSamp HSampM(Pt, ℓ)).Tag → ℕ)
    (specialDec : Option (∀ {Δ'}, Expr _ Δ' _ → Comp _ (I₀.withSamp HSampM(Pt, ℓ)) Δ' _))
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ'} (x : Expr _ Δ' _),
          compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) (f x) ≤
            exprSizeW (fun _ => 650) x + 700 ∧
          compListMNodes (f x) = 0 ∧ compQuerySum qW (f x) ≤ Q₀) :
    compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
      (injectBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) ≤ 23000 + 10 * bits P ∧
    compListMNodes
      (injectBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) = 0 ∧
    compQuerySum qW
      (injectBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        1 1 maxForwardJumps qSim jPos mSlot la specialDec (Γ := Γ)) ≤ 2 * Q₀ := by
  have _ := hqS
  have hb1 : bits 1 = 1 := rfl
  dsimp only [injectBody, anyInTransitE, anyInTransitBody, recMatchesE, removeFromTransitE,
    removeFromTransitBody, isCompromisedE, isCompromisedBody, eqAdE, eqCE, orE, maxNatE,
    mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls,
    hsNKeys, hsKeysT, hsCorrKey, hsSkipped, recIdx, recAd, recCt, callE, callC]
  generalize hrx : receiveBody (I₀ := I₀) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) 1 1 maxForwardJumps jPos mSlot la specialDec (Γ := _) = rx
  have ⟨hr1, hr2, hr3⟩ :
      compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) rx ≤ 16500 + 6 * bits P ∧
      compListMNodes rx = 0 ∧ compQuerySum qW rx ≤ 2 * Q₀ := by
    rw [← hrx]; exact receiveBody_sizeW_q_le C ℓ encT idOf hj hm la qW specialDec hDec
  unfold_dsl_vars
  dsimp only [compSizeW, exprSizeW, compListMNodes, compQuerySum]
  try simp only [hb1]
  try simp only [Nat.reduceAdd]
  simp only [hr2]
  generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) rx = srx at hr1 ⊢
  generalize compQuerySum qW rx = qrx at hr3 ⊢
  refine ⟨by omega, trivial, by omega⟩

end HybStepBounds

private theorem initHybSessStExpr_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) :
    (initHybSessStExpr ℓ Pt C Dh encPt encT idOf lam).size ≤ 250 := by
  have hb0 : bits 0 = 1 := rfl
  dsimp only [initHybSessStExpr]
  refine (liftFsExpr_size (Dh := Dh) (encPt := encPt) (lam := lam) _).trans_le ?_
  refine (compilePureExpr_sizeW_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
    (fun _ => 650) (hybOpMacro_size_le C ℓ encT idOf) _).trans ?_
  dsimp only [CryptoGames.FSAEAD.Thm5.Costed.initHSE, CryptoGames.FSAEAD.Thm5.Costed.mkHS]
  dsimp only [exprSizeW]; simp only [hb0]; omega

private theorem liftSlotHybStep_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (nf : Bool) {qSim P : ℕ} (hqS : bits qSim ≤ bits P + 3)
    {qTy rTy : Ty (atomicSig ℓ Pt)}
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt)
      [qTy, hybSessStTy ℓ Pt] (.prod rTy (hybSessStTy ℓ Pt))) :
    (liftSlotHybStep ℓ Pt C Dh encPt encT idOf lam nf qSim c).size ≤
      5 * c.size + 100 * compListMNodes c +
        compQuerySum (fun _ => 9506 + 2 * bits P) c + 15 := by
  have hEnv : ∀ ⦃u⦄ (v : Var [qTy, hybSessStTy ℓ Pt] u),
      (envSwapFst2 v :
        Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [qTy, slotSessStTy ℓ Pt] u).size ≤ 2 := by
    intro u v
    cases v with
    | zero => simp only [envSwapFst2, Expr.size]; omega
    | succ v =>
      cases v with
      | zero => simp only [envSwapFst2, Expr.size]; omega
      | succ v => nomatch v
  have hSub := substQueryComp_size_le_5
    (I₁ := slotOtccaTargetIface ℓ Pt) (I₂ := fsaeadHeaderIface ℓ Pt)
    (fun s {_} e => liftBaseSamp s e)
    (slotOtccaImpl ℓ Pt C Dh encPt encT idOf lam nf qSim)
    (fun _ => 9506 + 2 * bits P)
    (fun s {_} e => by rw [liftBaseSamp_size])
    (fun g => by have := slotOtccaImpl_size_le ℓ Pt C Dh encPt encT idOf lam hℓ nf hqS g; omega)
    hEnv (.snd (.var (.succ .zero))) (by simp only [Expr.size]; omega)
    (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c)
  simp only [liftFsSlotComp_size, compListMNodes_liftFsSlotComp,
    compQuerySum_liftFsSlotComp] at hSub
  dsimp only [liftSlotHybStep]
  simp only [Comp.size, Expr.size]
  omega

private theorem runLazyPubSess_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (lam : Pt) {sTy : Ty (atomicSig ℓ Pt)}
    (mkInit : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt) [] sTy)
    (trS chS csS crS dlS ijS)
    {B_init B_step : ℕ}
    (hInit : mkInit.size ≤ B_init)
    (htr : trS.size ≤ B_step) (hch : chS.size ≤ B_step)
    (hcs : csS.size ≤ B_step) (hcr : crS.size ≤ B_step)
    (hdl : dlS.size ≤ B_step) (hij : ijS.size ≤ B_step)
    (g : FSAEADTag) :
    (runLazyPubSess ℓ Pt C Dh encPt encT lam mkInit trS chS csS crS dlS ijS g).size ≤
      B_init + B_step + 150 := by
  have hpubDl : (lPubOfExpr ℓ Pt C encT
      (Γ := [(fsaeadHeaderIface ℓ Pt).dom .dl, .prod .bool (.opt sTy)])
      (.snd (.snd (.var .zero)))).size ≤ 43 := by
    have := lPubOfExpr_size C ℓ encT
      (Γ := [(fsaeadHeaderIface ℓ Pt).dom .dl, .prod .bool (.opt sTy)])
      (.snd (.snd (.var .zero)))
    dsimp only [Expr.size] at this; omega
  have hpubIj : (lPubOfExpr ℓ Pt C encT
      (Γ := [(fsaeadHeaderIface ℓ Pt).dom .ij, .prod .bool (.opt sTy)])
      (.snd (.snd (.var .zero)))).size ≤ 43 := by
    have := lPubOfExpr_size C ℓ encT
      (Γ := [(fsaeadHeaderIface ℓ Pt).dom .ij, .prod .bool (.opt sTy)])
      (.snd (.snd (.var .zero)))
    dsimp only [Expr.size] at this; omega
  cases g <;>
    (dsimp only [runLazyPubSess, ensureSessInit, mapRrWithPubExpr]
     simp only [Comp.size, Comp.renameM_size, liftFsExpr_size, exprWk1_size, Expr.size]
     omega)

private theorem realTrStep_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) {jPos mSlot P : ℕ}
    (hbjPos : bits jPos ≤ bits P + 16) (hbmSlot : bits mSlot ≤ bits P + 16) :
    (realTrStep ℓ Pt C Dh encPt encT idOf lam jPos mSlot).size ≤ 24000 + 10 * bits P := by
  dsimp only [realTrStep]
  refine (liftFsCoinComp_size (Dh := Dh) (encPt := encPt) (lam := lam) _).trans_le ?_
  refine (compilePureComp_sizeW_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
    (fun _ => 650) (fun _ => 650) (fun _ => 650)
    (hybOpMacro_size_le (Pt := Pt) C ℓ encT idOf)
    (prgSampMacro_size_le (Pt := Pt) C ℓ encT idOf hℓ)
    (fun e => nomatch e) _).trans ?_
  let HSig := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt
  let I₀ := Iface.withSamp (CryptoGames.PRG.Costed.prgIface HSig)
    (CryptoGames.OTCCA.Costed.idealSamplers
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ct) (lIdeal C clampedProtoSignalCodec ℓ encT) 1)
  let HSamp := ReductionDsl.unifSamplers (S := HSig)
    CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)
  have ht1 := And.left (transmitBody_sizeW_q_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀) (Q₀ := 0)
    (Γ := [.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg),
      CryptoGames.FSAEAD.Thm5.Costed.stTy])
    hbjPos hbmSlot (fun _ => 0)
    (fun a => Comp.sample (I := I₀.withSamp HSamp) (Sum.inl (Sum.inr ())) a)
    (some fun x => Comp.sample (I := I₀.withSamp HSamp) (Sum.inl (Sum.inr ())) (.fst x))
    (fun ia => ⟨(show compSizeW _ _ _ _ = exprSizeW (fun _ => 650) ia + 650 from rfl).trans_le
      (Nat.add_le_add_left (by decide) _), rfl, rfl⟩)
    (fun x => ⟨(show compSizeW _ _ _ _ = (exprSizeW (fun _ => 650) x + 1) + 650 from rfl).trans_le
      (by omega), rfl, le_rfl⟩))
  exact (Nat.add_le_add_right (Nat.add_le_add (le_refl 4) ht1) 1).trans (by omega)

private theorem realChStep_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) {jPos mSlot P : ℕ}
    (hbjPos : bits jPos ≤ bits P + 16) (hbmSlot : bits mSlot ≤ bits P + 16) :
    (realChStep ℓ Pt C Dh encPt encT idOf lam jPos mSlot).size ≤ 24000 + 10 * bits P := by
  dsimp only [realChStep]
  refine (liftFsCoinComp_size (Dh := Dh) (encPt := encPt) (lam := lam) _).trans_le ?_
  refine (compilePureComp_sizeW_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
    (fun _ => 650) (fun _ => 650) (fun _ => 650)
    (hybOpMacro_size_le (Pt := Pt) C ℓ encT idOf)
    (prgSampMacro_size_le (Pt := Pt) C ℓ encT idOf hℓ)
    (fun e => nomatch e) _).trans ?_
  let HSig := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt
  let I₀ := Iface.withSamp (CryptoGames.PRG.Costed.prgIface HSig)
    (CryptoGames.OTCCA.Costed.idealSamplers
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ct) (lIdeal C clampedProtoSignalCodec ℓ encT) 1)
  let HSamp := ReductionDsl.unifSamplers (S := HSig)
    CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)
  have ht1 := And.left (challengeBody_sizeW_q_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀) (Q₀ := 0)
    (Γ := [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
      (.prod (CryptoGames.FSAEAD.Costed.bt .msg) (CryptoGames.FSAEAD.Costed.bt .msg)),
      CryptoGames.FSAEAD.Thm5.Costed.stTy])
    hbjPos hbmSlot (fun _ => 0)
    (fun a => Comp.sample (I := I₀.withSamp HSamp) (Sum.inl (Sum.inr ())) a)
    (some fun x => Comp.sample (I := I₀.withSamp HSamp) (Sum.inl (Sum.inr ())) (.fst x))
    (fun ia => ⟨(show compSizeW _ _ _ _ = exprSizeW (fun _ => 650) ia + 650 from rfl).trans_le
      (Nat.add_le_add_left (by decide) _), rfl, rfl⟩)
    (fun x => ⟨(show compSizeW _ _ _ _ = (exprSizeW (fun _ => 650) x + 1) + 650 from rfl).trans_le
      (by omega), rfl, le_rfl⟩))
  exact (Nat.add_le_add_right (Nat.add_le_add (le_refl 4) ht1) 1).trans (by omega)

private theorem routerQueryMacro_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (stage la : Bool) {j qep qR B0 : ℕ}
    (hj : j ≤ (qep + 2) * B0 + B0 * B0) (hqR : qR ≤ B0) (g : FSHdrTag) :
    (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR g).size ≤
      160500 + 68 * bits (qep + qR + B0 + 1) := by
  let P := qep + qR + B0 + 1
  have ⟨hbN, hbqSim, hbjPos, hbmSlot, hbj⟩ := bits_router_params (la := la) (stage := stage) hj hqR
  change bits (authHopCutoff maxForwardJumps qR la) ≤ bits P + 16 at hbN
  change bits (2 * qR + 4) ≤ bits P + 3 at hbqSim
  change bits (if stage then authHopCutoff maxForwardJumps qR la else 0) ≤ bits P + 16 at hbjPos hbmSlot
  change bits j ≤ 2 * bits P + 2 at hbj
  let N := authHopCutoff maxForwardJumps qR la
  let qSim := 2 * qR + 4
  let jPosR := if stage then N else 0
  let mSlotR := if stage then N else 0
  have _ := initHybSessStExpr_size_le ℓ Pt C Dh encPt encT idOf lam
  have hInitR : (initRealSessComp ℓ Pt C Dh encPt encT idOf lam).size ≤ 260 := by
    dsimp only [initRealSessComp]; simp only [Comp.size, Expr.size]; omega
  have hInitS : (initSlotSessComp ℓ Pt C Dh encPt encT idOf lam).size ≤ 270 := by
    dsimp only [initSlotSessComp, emptySaltSlotAtomExpr]; simp only [Comp.size, Expr.size]; omega
  have hOp0 := hybOpMacro_size_le (Pt := Pt) C ℓ encT idOf
  have hSamp0 := prgSampMacro_size_le (Pt := Pt) C ℓ encT idOf hℓ
  have hSampM := multiSampMacro_size_le (Pt := Pt) C ℓ encT idOf hℓ
  have hQueryM := multiQueryMacro_size_le (Pt := Pt) C ℓ encT idOf
  have hSampML : ∀ s, compListMNodes ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s) = 0 := by
    intro s; cases s with
    | inl u =>
      cases u
      dsimp [multiMacroBundle, Iface.withSamp, ReductionDsl.Samplers.sum, Sum.elim,
        CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleU64Comp, compListMNodes]
    | inr t =>
      rcases t with _ | _ | (_ | _) <;>
        dsimp [multiMacroBundle, slotOtccaTargetIface, ReductionDsl.atomicBaseSamplers,
          ReductionDsl.unifSamplers, compListMNodes]
  have hQueryML : ∀ g', compListMNodes ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g') = 0 := by
    intro g'; cases g' <;>
      dsimp [multiMacroBundle, Iface.withSamp, CryptoGames.OTCCA.Costed.otccaIface, compListMNodes]
  have hSampMQ : ∀ s, compQuerySum (fun _ => 9506 + 2 * bits P)
      ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s) = 0 := by
    intro s; cases s with
    | inl u =>
      cases u
      dsimp [multiMacroBundle, Iface.withSamp, ReductionDsl.Samplers.sum, Sum.elim,
        CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp,
        Computational.Proofs.ReductionDsl.FsAtomicOps.sampleU64Comp, compQuerySum]
    | inr t =>
      rcases t with _ | _ | (_ | _) <;>
        dsimp [multiMacroBundle, slotOtccaTargetIface, ReductionDsl.atomicBaseSamplers,
          ReductionDsl.unifSamplers, compQuerySum]
  have hQueryMQ : ∀ g', compQuerySum (fun _ => 9506 + 2 * bits P)
      ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g') ≤ 9506 + 2 * bits P := by
    intro g'; cases g' <;>
      (dsimp [multiMacroBundle, Iface.withSamp, CryptoGames.OTCCA.Costed.otccaIface, compQuerySum]
       omega)
  let I₀R := Iface.withSamp
    (CryptoGames.PRG.Costed.prgIface
      (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
    (CryptoGames.OTCCA.Costed.idealSamplers
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ct) (lIdeal C clampedProtoSignalCodec ℓ encT) 1)
  let HSigR := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt
  let _HSampR := ReductionDsl.unifSamplers (S := HSigR)
    CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)
  have hRealTr : (realTrStep ℓ Pt C Dh encPt encT idOf lam jPosR mSlotR).size ≤ 24000 + 10 * bits P :=
    realTrStep_size_le ℓ Pt C Dh encPt encT idOf lam hℓ hbjPos hbmSlot
  have hRealCh : (realChStep ℓ Pt C Dh encPt encT idOf lam jPosR mSlotR).size ≤ 24000 + 10 * bits P :=
    realChStep_size_le ℓ Pt C Dh encPt encT idOf lam hℓ hbjPos hbmSlot
  have hRealCs : (realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la).size ≤ 5000 + 2 * bits P := by
    dsimp only [realCsStep]
    refine (liftFsCoinComp_size (Dh := Dh) (encPt := encPt) (lam := lam) _).trans_le ?_
    refine (compilePureComp_sizeW_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      (fun _ => 650) (fun _ => 650) (fun _ => 650) hOp0 hSamp0 (fun e => nomatch e) _).trans ?_
    dsimp only [CryptoGames.FSAEAD.Thm5.Costed.corruptSenderBody,
      CryptoGames.FSAEAD.Thm5.Costed.mkHS, CryptoGames.FSAEAD.Thm5.Costed.hsB,
      CryptoGames.FSAEAD.Thm5.Costed.hsLastSent, CryptoGames.FSAEAD.Thm5.Costed.hsCorrAt,
      CryptoGames.FSAEAD.Thm5.Costed.hsRecvIdx, CryptoGames.FSAEAD.Thm5.Costed.hsEnded,
      CryptoGames.FSAEAD.Thm5.Costed.hsWin, CryptoGames.FSAEAD.Thm5.Costed.hsLf,
      CryptoGames.FSAEAD.Thm5.Costed.hsInTransit, CryptoGames.FSAEAD.Thm5.Costed.hsChalls,
      CryptoGames.FSAEAD.Thm5.Costed.hsNKeys, CryptoGames.FSAEAD.Thm5.Costed.hsKeysT,
      CryptoGames.FSAEAD.Thm5.Costed.hsCorrKey, CryptoGames.FSAEAD.Thm5.Costed.hsSkipped,
      CryptoGames.FSAEAD.Thm5.Costed.callC]
    unfold_dsl_vars
    dsimp only [compSizeW, exprSizeW]
    generalize hsx : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650)
      (CryptoGames.FSAEAD.Thm5.Costed.senderKeyBody (I₀ := I₀R) _ _ 1 1 qSim (Γ := _)) = sx
    have : sx ≤ 4000 + 2 * bits P := by
      rw [← hsx]; exact senderKeyBody_sizeW_le (Pt := Pt) C ℓ encT idOf hbqSim
    omega
  have hRealCr : (realCrStep ℓ Pt C Dh encPt encT lam).size ≤ 24000 + 10 * bits P := by
    dsimp only [realCrStep, Comp.size, Expr.size]; omega
  have hRealDl : (realDlStep ℓ Pt C Dh encPt encT idOf lam qSim jPosR mSlotR la).size ≤
      24000 + 10 * bits P := by
    dsimp only [realDlStep]
    refine (liftFsCoinComp_size (Dh := Dh) (encPt := encPt) (lam := lam) _).trans_le ?_
    generalize hbody : CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀R)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps qSim jPosR mSlotR la _ = body
    have ht1 : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) body ≤ 23000 + 10 * bits P := by
      rw [← hbody]
      exact And.left (deliverBody_sizeW_q_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀R) (Q₀ := 0)
        hbqSim hbjPos hbmSlot la (fun _ => 0) _
        (fun x => ⟨by dsimp [compSizeW, exprSizeW]; omega, rfl, by dsimp [compQuerySum]; omega⟩))
    refine (compilePureComp_sizeW_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      (fun _ => 650) (fun _ => 650) (fun _ => 650) hOp0 hSamp0 (fun e => nomatch e) _).trans ?_
    dsimp only [compSizeW, exprSizeW]
    generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) body = tx at ht1 ⊢
    omega
  have hRealIj : (realIjStep ℓ Pt C Dh encPt encT idOf lam qSim jPosR mSlotR la).size ≤
      24000 + 10 * bits P := by
    dsimp only [realIjStep]
    refine (liftFsCoinComp_size (Dh := Dh) (encPt := encPt) (lam := lam) _).trans_le ?_
    generalize hbody : CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀R)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      maxForwardJumps qSim jPosR mSlotR la _ = body
    have ht1 : compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) body ≤ 23000 + 10 * bits P := by
      rw [← hbody]
      exact And.left (injectBody_sizeW_q_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀R) (Q₀ := 0)
        hbqSim hbjPos hbmSlot la (fun _ => 0) _
        (fun x => ⟨by dsimp [compSizeW, exprSizeW]; omega, rfl, by dsimp [compQuerySum]; omega⟩))
    refine (compilePureComp_sizeW_le (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      (fun _ => 650) (fun _ => 650) (fun _ => 650) hOp0 hSamp0 (fun e => nomatch e) _).trans ?_
    dsimp only [compSizeW, exprSizeW]
    generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) body = tx at ht1 ⊢
    omega
  let I₀S := CryptoGames.OTCCA.Costed.otccaIface
    (S := HSigR)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) (lIdeal C clampedProtoSignalCodec ℓ encT) 1
  have hSlotBind : ∀ {τ₁ τ₂ : Ty HSigR} {S_b Q_b : ℕ}
      (body : Comp _ (I₀S.withSamp _)
        [.prod τ₁ CryptoGames.FSAEAD.Thm5.Costed.stTy, τ₁, CryptoGames.FSAEAD.Thm5.Costed.stTy]
        (.prod (.opt τ₂) CryptoGames.FSAEAD.Thm5.Costed.stTy)),
      (compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) body ≤ S_b ∧
        compListMNodes body = 0 ∧
        compQuerySum (fun _ => 9506 + 2 * bits P) body ≤ Q_b) →
      (liftSlotHybStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim
        (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
          (.bind (.ret (.pair (.var .zero) (.var (.succ .zero)))) body))).size ≤
        5 * (5 + S_b) + Q_b + 15 := by
    intro τ₁ τ₂ S_b Q_b body ⟨ht1, ht2, ht3⟩
    refine (liftSlotHybStep_size_le ℓ Pt C Dh encPt encT idOf lam hℓ stage hbqSim _).trans ?_
    generalize hret : Comp.ret (Expr.pair (Expr.var Var.zero) (Expr.var (Var.succ Var.zero))) = r0
    have ⟨hr1, hr2, hr3⟩ :
        compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) r0 = 4 ∧
        compListMNodes r0 = 0 ∧
        compQuerySum (fun _ => 9506 + 2 * bits P) r0 = 0 := by
      rw [← hret]; exact ⟨rfl, rfl, rfl⟩
    have hcs := compilePureComp_sizeW_le (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
      (fun _ => 650) (fun _ => 650) (fun _ => 650) hOp0 hSampM hQueryM (.bind r0 body)
    have hcl := compListMNodes_compilePureComp_le (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
      hSampML hQueryML (.bind r0 body)
    have hcq := compQuerySum_compilePureComp_le (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
      (fun _ => 9506 + 2 * bits P) (fun _ => 9506 + 2 * bits P) hSampMQ hQueryMQ (.bind r0 body)
    dsimp only [compSizeW, compListMNodes, compQuerySum] at hcs hcl hcq
    simp only [hr1, hr2, hr3, ht2, zero_add] at hcs hcl hcq
    generalize compSizeW (fun _ => 650) (fun _ => 650) (fun _ => 650) body = sb at ht1 hcs
    generalize compQuerySum (fun _ => 9506 + 2 * bits P) body = qb at ht3 hcq
    refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left 5 hcs) (Nat.mul_le_mul_left 100 hcl)) hcq) (Nat.le_refl 15)).trans ?_
    omega
  have hSlotTr : (slotTrStep ℓ Pt C Dh encPt encT idOf lam stage qSim N).size ≤
      135000 + 54 * bits P := by
    dsimp only [slotTrStep]
    exact (hSlotBind _ (transmitBody_sizeW_q_le (Pt := Pt) C ℓ encT idOf
      (Q₀ := 9506 + 2 * bits P) hbN hbN (fun _ => 9506 + 2 * bits P) _ _
      (fun {Δ'} ia => ⟨by
        change exprSizeW (fun _ => 650) ia + 650 ≤ exprSizeW (fun _ => 650) ia + 700
        omega, rfl, rfl⟩)
      (fun {Δ'} x => ⟨by
        change (exprSizeW (fun _ => 650) x + 650) +
          (1 + ((exprSizeW (fun _ => 650) (exprWk1 x) + 1) + 650) + (1 + 1) + 1) + 1 ≤
          2 * exprSizeW (fun _ => 650) x + 1400
        dsimp only [exprWk1]
        rw [Computational.Proofs.SessionCostedFig8.BundlesAuxSize.exprSizeW_renameM]
        omega,
        rfl, (Nat.add_zero _).le⟩))).trans (by omega)
  have hSlotCh : (slotChStep ℓ Pt C Dh encPt encT idOf lam stage qSim N).size ≤
      135000 + 54 * bits P := by
    dsimp only [slotChStep]
    exact (hSlotBind _ (challengeBody_sizeW_q_le (Pt := Pt) C ℓ encT idOf
      (Q₀ := 9506 + 2 * bits P) hbN hbN (fun _ => 9506 + 2 * bits P) _ _
      (fun {Δ'} ia => ⟨by
        change exprSizeW (fun _ => 650) ia + 650 ≤ exprSizeW (fun _ => 650) ia + 700
        omega, rfl, rfl⟩)
      (fun {Δ'} x => ⟨by
        change (exprSizeW (fun _ => 650) x + 650) +
          (1 + ((exprSizeW (fun _ => 650) (exprWk1 x) + 1) + 650) + (1 + 1) + 1) + 1 ≤
          2 * exprSizeW (fun _ => 650) x + 1400
        dsimp only [exprWk1]
        rw [Computational.Proofs.SessionCostedFig8.BundlesAuxSize.exprSizeW_renameM]
        omega,
        rfl, (Nat.add_zero _).le⟩))).trans (by omega)
  have hSlotCs : (slotCsStep ℓ Pt C Dh encPt encT idOf lam qSim la).size ≤
      135000 + 54 * bits P := by
    dsimp only [slotCsStep]; simp only [Comp.size, Expr.size]
    generalize hren : (Comp.renameM renSwap2 _).size = sr
    have : sr = (realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la).size := by
      rw [← hren]; exact Comp.renameM_size _ _
    omega
  have hSlotCr : (slotCrStep ℓ Pt C Dh encPt encT lam).size ≤ 135000 + 54 * bits P := by
    dsimp only [slotCrStep, Comp.size, Expr.size]; omega
  have hSlotDl : (slotDlStep ℓ Pt C Dh encPt encT idOf lam stage qSim N la).size ≤
      135000 + 54 * bits P := by
    dsimp only [slotDlStep]
    exact (hSlotBind _ (deliverBody_sizeW_q_le (Pt := Pt) C ℓ encT idOf
      (Q₀ := 9506 + 2 * bits P) hbqSim hbN hbN la (fun _ => 9506 + 2 * bits P) _
      (fun {Δ'} x => ⟨(show compSizeW _ _ _ _ = exprSizeW (fun _ => 650) x + 650 from rfl).trans_le
        (Nat.add_le_add_left (by decide) _), rfl, le_rfl⟩))).trans (by omega)
  have hSlotIj : (slotIjStep ℓ Pt C Dh encPt encT idOf lam stage qSim N la).size ≤
      135000 + 54 * bits P := by
    dsimp only [slotIjStep]
    exact (hSlotBind _ (injectBody_sizeW_q_le (Pt := Pt) C ℓ encT idOf
      (Q₀ := 9506 + 2 * bits P) hbqSim hbN hbN la (fun _ => 9506 + 2 * bits P) _
      (fun {Δ'} x => ⟨(show compSizeW _ _ _ _ = exprSizeW (fun _ => 650) x + 650 from rfl).trans_le
        (Nat.add_le_add_left (by decide) _), rfl, le_rfl⟩))).trans (by omega)
  have hRealLazy := runLazyPubSess_size_le ℓ Pt C Dh encPt encT lam
    (initRealSessComp ℓ Pt C Dh encPt encT idOf lam) _ _ _ _ _ _
    hInitR hRealTr hRealCh (hRealCs.trans (by omega)) hRealCr hRealDl hRealIj (toFsTag g)
  have hSlotLazy := runLazyPubSess_size_le ℓ Pt C Dh encPt encT lam
    (initSlotSessComp ℓ Pt C Dh encPt encT idOf lam) _ _ _ _ _ _
    hInitS hSlotTr hSlotCh hSlotCs hSlotCr hSlotDl hSlotIj (toFsTag g)
  cases stage <;>
    (dsimp only [routerQueryMacro, P, N, qSim, jPosR, mSlotR] at *
     simp only [Bool.false_eq_true, eq_self, ite_true, ite_false, Comp.size, Expr.size] at *
     repeat erw [Comp.renameM_size]
     omega)

private theorem routerQueryMacro_size_le_200k (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (stage la : Bool) {j qep qR B0 : ℕ}
    (hj : j ≤ (qep + 2) * B0 + B0 * B0) (hqR : qR ≤ B0) (g : FSHdrTag) :
    120 + (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR g).size ≤
      32 * fsMultiQueryS qep qR B0 g := by
  have h := routerQueryMacro_size_le ℓ Pt C Dh encPt encT idOf lam hℓ stage la hj hqR g
  simp only [fsMultiQueryS_apply]; omega

/-- Positive-branch AST `.size` bound for `compileFsMultiAtomic` (discharging `hSizePos` of
`guardRed_gRedBounded`). Note: `hSize` uses `reductionSizeBudget / 32 + 2 ^ 7 * bits (...)`
(`= 524,288 + 128 * bits (...)`) because `substQueryRed` multiplies `.var` leaves by up to `2`
and list-monadic combinators by up to `32`. -/
theorem compileFsMultiAtomic_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j qep qR B0 q : ℕ)
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
    (hSize : compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.finish + 400 ≤
        1400000 + 585 * bits (ratchetCostBudget q qep))
    (hP : ℓ < 10 ^ 6 ∧ j ≤ (qep + 2) * B0 + B0 * B0 ∧ qR ≤ B0)
    (hListM : compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish ≤ 50 :=
      by simp [compListMNodes])
    (hqCount : compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish ≤ 60 :=
      by simp [compQueryCount]) :
    (substQueryRed
      (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (I₂ := fsaeadHeaderIface ℓ Pt)
      (initRouterStExpr ℓ Pt C Dh encPt encT lam)
      (fun s {_} e => Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam)
        (I := fsaeadHeaderIface ℓ Pt) s e)
      (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR)
      (compilePureAuxRed
        (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
        (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  rcases hP with ⟨hℓ, hj, hqR⟩
  let bP := bits (qep + qR + B0 + 1)
  let q₀ := 11990 + 16 * bP
  let Q_max := 160506 + 68 * bP
  have hAd : (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).splitIn.size +
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptAIn.size +
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptQ.size +
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptR.size +
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptAOut.size +
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptOut.size ≤ 340 := by
    have h1 := fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
    have h2 := fig8AdaptQ_size ℓ Pt C Dh encPt encT lam
    have h3 := fig8AdaptR_size ℓ Pt C Dh encPt encT lam
    dsimp only [ckaToFig8Adapters, Expr.size]; omega
  have hMain := substQueryRed_compilePureAuxRed_size_le_6
    (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
    (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R
    (initRouterStExpr ℓ Pt C Dh encPt encT lam)
    (by dsimp [initRouterStExpr]; simp only [Expr.size]; omega)
    (fun s {_} e => Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (I := fsaeadHeaderIface ℓ Pt) s e)
    (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR)
    (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) q₀ Q_max
    (ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0)
    (fun s => by cases s <;> (dsimp [fsMultiPureAuxBundle, fsMultiSampMacro, ckaSampS, Comp.size, Expr.size]; omega))
    (fun g => by cases g <;> (dsimp [fsMultiPureAuxBundle, Comp.size, Expr.size]; omega))
    (fun s {_} e => le_rfl)
    (fun g => (Nat.add_le_add_right
      (routerQueryMacro_size_le ℓ Pt C Dh encPt encT idOf lam hℓ stage la hj hqR g) 6).trans
      (by dsimp [Q_max, bP]; omega))
    (fun s => by cases s <;> rfl)
    (fun g => by cases g <;> (dsimp [fsMultiPureAuxBundle, compQuerySum]; omega))
    (fun s => by cases s <;> rfl)
    (fun g => by cases g <;> rfl)
    (fun g => by simp only [fsMultiQueryS_apply]; dsimp [q₀, bP]; omega)
    (by dsimp [Q_max, q₀, bP]; omega)
    hAd
  have hBud : reductionSizeBudget = 16777216 := rfl
  omega

/-- Positive-branch AST `.size` bound for `compileFsMultiDFAtomic` (discharging `hSizePos` of
`guardRed_gRedBounded`). -/
theorem compileFsMultiDFAtomic_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j qep qR B0 q : ℕ)
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
    (hSize : compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.finish + 400 ≤
        1400000 + 810 * bits (ratchetCostBudget q qep))
    (hP : ℓ < 10 ^ 6 ∧ j ≤ (qep + 2) * B0 + B0 * B0 ∧ qR ≤ B0)
    (hListM : compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish ≤ 50 :=
      by simp [compListMNodes])
    (hqCount : compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish ≤ 60 :=
      by simp [compQueryCount]) :
    (substQueryRed
      (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (I₂ := fsaeadHeaderIface ℓ Pt)
      (initRouterStExpr ℓ Pt C Dh encPt encT lam)
      (fun s {_} e => Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam)
        (I := fsaeadHeaderIface ℓ Pt) s e)
      (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR)
      (compilePureAuxRed
        (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
        (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  rcases hP with ⟨hℓ, hj, hqR⟩
  let bP := bits (qep + qR + B0 + 1)
  let q₀ := 11990 + 16 * bP
  let Q_max := 160506 + 68 * bP
  have hAd : (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).splitIn.size +
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptAIn.size +
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptQ.size +
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptR.size +
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptAOut.size +
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam).adaptOut.size ≤ 340 := by
    have h1 := fig8SplitIn_size ℓ Pt C Dh encPt encT idOf lam
    have h2 := fig8AdaptQDF_size ℓ Pt C Dh encPt encT lam
    have h3 := fig8AdaptRDF_size ℓ Pt C Dh encPt encT lam
    dsimp only [ckaDFToFig8Adapters, Expr.size]; omega
  have hMain := substQueryRed_compilePureAuxRed_size_le_6
    (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
    (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R
    (initRouterStExpr ℓ Pt C Dh encPt encT lam)
    (by dsimp [initRouterStExpr]; simp only [Expr.size]; omega)
    (fun s {_} e => Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (I := fsaeadHeaderIface ℓ Pt) s e)
    (routerQueryMacro ℓ Pt C Dh encPt encT idOf lam stage la j qR)
    (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) q₀ Q_max
    (ckaOpMacro_size_le ℓ Pt C Dh encPt encT idOf lam B0)
    (fun s => by cases s <;> (dsimp [fsMultiPureAuxBundle, fsMultiSampMacro, ckaSampS, Comp.size, Expr.size]; omega))
    (fun g => by cases g <;> (dsimp [fsMultiPureAuxBundle, Comp.size, Expr.size]; omega))
    (fun s {_} e => le_rfl)
    (fun g => (Nat.add_le_add_right
      (routerQueryMacro_size_le ℓ Pt C Dh encPt encT idOf lam hℓ stage la hj hqR g) 6).trans
      (by dsimp [Q_max, bP]; omega))
    (fun s => by cases s <;> rfl)
    (fun g => by cases g <;> (dsimp [fsMultiPureAuxBundle, compQuerySum]; omega))
    (fun s => by cases s <;> rfl)
    (fun g => by cases g <;> rfl)
    (fun g => by simp only [fsMultiQueryS_apply]; dsimp [q₀, bP]; omega)
    (by dsimp [Q_max, q₀, bP]; omega)
    hAd
  have hBud : reductionSizeBudget = 16777216 := rfl
  omega

/-- Negative-branch fallback AST `.size` bound for `compileFsMultiAtomic` and
`compileFsMultiDFAtomic` (discharging `hSizeNeg` of `guardRed_gRedBounded`). -/
theorem compileFsMulti_dflt_size_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {rTy uTy : Ty (atomicSig ℓ Pt)} {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {lam : Pt} :
    ((Expr.unit (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (Γ := [])).size + 3) +
      ((@Expr.inl _ (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [] (.opt uTy) rTy .none).size + 3) +
      ((Expr.bool (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (Γ := []) false).size + 1) ≤
      reductionSizeBudget := by
  have hBud : reductionSizeBudget = 16777216 := rfl
  dsimp [Expr.size]; omega

end ConcreteRouterSize

end SizeBounds
end Computational.Proofs.SessionCostedFig8.BundlesMultiFsRouterCostA

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
import Computational.Specifications.Session.StatementComposed
import Computational.Proofs.HeadlineV1.Stage2RouterHelpers
import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.ReductionDsl.MacroLift
import Computational.Proofs.ReductionDsl.PureAuxMacroLift
import Computational.Proofs.ReductionDsl.Fig8Atomic
import Computational.Proofs.ReductionDsl.FsAtomicOps
import Computational.Proofs.ReductionDsl.FsAtomicMacros
import Computational.Proofs.ReductionDsl.FsAtomicBundles
import Computational.Proofs.ReductionDsl.FSAEAD.HybridCosted
import Computational.Proofs.ReductionDsl.FSAEAD.HybridInv
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRed
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWireCosted
import Computational.Proofs.ReductionDsl.SM.Engine
import Computational.Proofs.E2E.SessionAuthQueries
import VCVio.OracleComp.EvalDist.Measure
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
import Computational.Specifications.Reductions.ReductionDsl.Core
import Computational.Specifications.Reductions.ReductionDsl.Samplers
import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Disjoint
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PolyFun.Control.Monad.Support
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import ToMathlib.Control.StateT
import VCVio.CryptoFoundations.SecExp
import VCVio.EvalDist.Defs.Measure.Core
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.OracleSpec
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.Prelude.Core
import VCVio.ProgramLogic.Unary.HoareTriple

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Expr Comp Ops Iface GameCodec CostedReduction
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

namespace Computational.Proofs.SessionCostedFig8.BundlesMultiFsSlot

section RouterDSL

set_option linter.unusedSectionVars false

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

local notation "SigA" => (atomicSig ℓ Pt)
local notation "OpsF" => (atomicFig8Ops ℓ Pt C Dh encPt encT lam)
local notation "IfaceF" => (fsaeadHeaderIface ℓ Pt)

/-! ### Query-Subsumption and Router-Subsumption Helpers -/

private inductive CoinOnly {κ : Type} {G : OracleSpec.{0, 0} κ} :
    {α : Type} → OracleComp (unifSpec + G) α → Prop where
  | ret {α : Type} (a : α) : CoinOnly (pure a)
  | coin {α : Type} (n : ℕ) (k : Fin (n + 1) → OracleComp (unifSpec + G) α) :
      (∀ u, CoinOnly (k u)) →
      CoinOnly (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= k)

private theorem CoinOnly.bind {κ : Type} {G : OracleSpec.{0, 0} κ} {α β : Type}
    {oa : OracleComp (unifSpec + G) α} {k : α → OracleComp (unifSpec + G) β}
    (hoa : CoinOnly oa) (hk : ∀ a, CoinOnly (k a)) :
    CoinOnly (oa >>= k) := by
  induction hoa with
  | ret a => rw [pure_bind]; exact hk a
  | coin n c _ ih => rw [bind_assoc]; exact .coin n _ ih

private theorem CoinOnly.map {κ : Type} {G : OracleSpec.{0, 0} κ} {α β : Type}
    (f : α → β) {oa : OracleComp (unifSpec + G) α} (hoa : CoinOnly oa) :
    CoinOnly (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact hoa.bind fun a => .ret (f a)

private theorem CoinOnly.liftP {S : Sig} {κ : Type} {G : OracleSpec.{0, 0} κ}
    (I : Iface S (unifSpec + G))
    (hFwd : ∀ n, I.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    {α : Type} (p : ProbComp α) :
    CoinOnly (I.liftP p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [Iface.liftP, simulateQ_pure]; exact .ret a
  | query_bind n mx ih =>
    rw [Iface.liftP, simulateQ_bind, simulateQ_query, hFwd]
    exact .coin n _ ih

private theorem CoinOnly.iterM {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    (f : α → OracleComp (unifSpec + G) α) (hf : ∀ a, CoinOnly (f a)) :
    ∀ (n : ℕ) (a : α), CoinOnly (ReductionDsl.iterM f n a)
  | 0, a => .ret a
  | n + 1, a => (hf a).bind (CoinOnly.iterM f hf n)

private theorem CoinOnly.findML {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    (p : α → OracleComp (unifSpec + G) Bool) (hp : ∀ a, CoinOnly (p a)) :
    ∀ xs : List α, CoinOnly (ReductionDsl.findML p xs)
  | [] => .ret none
  | x :: xs => (hp x).bind fun b => by cases b <;> [exact CoinOnly.findML p hp xs; exact .ret (some x)]

private theorem CoinOnly.anyML {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    (p : α → OracleComp (unifSpec + G) Bool) (hp : ∀ a, CoinOnly (p a)) :
    ∀ xs : List α, CoinOnly (ReductionDsl.anyML p xs)
  | [] => .ret false
  | x :: xs => (hp x).bind fun b => by cases b <;> [exact CoinOnly.anyML p hp xs; exact .ret true]

private theorem CoinOnly.mapML {κ : Type} {G : OracleSpec.{0, 0} κ} {α β : Type}
    (f : α → OracleComp (unifSpec + G) β) (hf : ∀ a, CoinOnly (f a)) :
    ∀ xs : List α, CoinOnly (ReductionDsl.mapML f xs)
  | [] => .ret []
  | x :: xs => (hf x).bind fun y => (CoinOnly.mapML f hf xs).bind fun ys => .ret (y :: ys)

private theorem CoinOnly.consumeFirstML {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    (p : α → OracleComp (unifSpec + G) Bool) (mark : α → α) (hp : ∀ a, CoinOnly (p a)) :
    ∀ xs : List α, CoinOnly (ReductionDsl.consumeFirstML p mark xs)
  | [] => .ret (false, [])
  | x :: xs => (hp x).bind fun b => by
    cases b
    · exact (CoinOnly.consumeFirstML p mark hp xs).bind fun r => .ret (r.1, x :: r.2)
    · exact .ret (true, mark x :: xs)

private theorem CoinOnly.foldML {κ : Type} {G : OracleSpec.{0, 0} κ} {α β : Type}
    (f : α → β → OracleComp (unifSpec + G) β) (hf : ∀ a b, CoinOnly (f a b)) :
    ∀ (b : β) (xs : List α), CoinOnly (ReductionDsl.foldML f b xs)
  | b, [] => .ret b
  | b, x :: xs => (hf x b).bind fun b' => CoinOnly.foldML f hf b' xs

private theorem CoinOnly.isQueryBoundP {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    {oa : OracleComp (unifSpec + G) α} (hoa : CoinOnly oa)
    {p : (unifSpec + G).Domain → Prop} [DecidablePred p]
    (hp : ∀ n, ¬ p (.inl n)) (k : ℕ) :
    oa.IsQueryBoundP p k := by
  induction hoa with
  | ret _ => trivial
  | coin n _ _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (hp n), fun u => ?_⟩
    simp only [hp n, ↓reduceIte]
    exact ih u

private theorem CoinOnly.guardedSafePost {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    {RespOk : (t : (unifSpec + G).Domain) → (unifSpec + G).Range t → Prop}
    {Q : (unifSpec + G).Domain → Prop}
    (hQu : ∀ n, ¬ Q (.inl n))
    {oa : OracleComp (unifSpec + G) α} (hoa : CoinOnly oa) :
    CryptoGames.GuardedSafe.GuardedSafePost RespOk Q (fun _ => True) oa := by
  induction hoa with
  | ret _ => exact .pure trivial
  | coin n _ _ ih => exact .query_bind (hQu n) fun u _ => ih u

private theorem dummyRed_eval_coinOnly {S : Sig} {O : Ops S} {κ₁ κ₂ : Type}
    {G₁ : OracleSpec.{0, 0} κ₁} {I : Iface S (unifSpec + G₁)}
    {G₂ : OracleSpec.{0, 0} κ₂} {Cg : GameCodec S G₂} {rIn aIn aOut out : Ty S}
    (hFwd : ∀ n, I.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G₁) (.inl n)))
    (dfltAIn : Expr O [rIn] aIn) (dfltR : Expr O [.unit, Cg.Q] Cg.R)
    (dfltOut : Expr O [.unit, aOut] out)
    (adv : aIn.denote → OracleComp (unifSpec + G₂) aOut.denote) (x : rIn.denote) :
    CoinOnly (({ σ := .unit
                 init := .ret (.pair dfltAIn .unit)
                 handle := .ret (.pair dfltR .unit)
                 finish := .ret dfltOut } :
               CostedReduction O I G₂ Cg rIn aIn aOut out).eval adv x) := by
  let R₀ : CostedReduction O I G₂ Cg rIn aIn aOut out :=
    { σ := .unit
      init := .ret (.pair dfltAIn .unit)
      handle := .ret (.pair dfltR .unit)
      finish := .ret dfltOut }
  have hSim : ∀ {α : Type} (oa : OracleComp (unifSpec + G₂) α) (st : Ty.unit.denote),
      CoinOnly ((simulateQ R₀.impl oa).run st) := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure b =>
      intro st
      simp only [simulateQ_pure, StateT.run_pure]
      exact .ret (b, st)
    | query_bind q k ih =>
      intro st
      cases q with
      | inl n =>
        simp only [R₀, simulateQ_bind, simulateQ_query, CostedReduction.impl,
          ReductionDsl.handlerImpl, StateT.run_bind, hFwd]
        exact .coin n _ fun u => ih u st
      | inr t =>
        simp only [R₀, simulateQ_bind, simulateQ_query, CostedReduction.impl,
          ReductionDsl.handlerImpl, Comp.eval, Expr.eval, StateT.run_bind, pure_bind]
        exact ih _ ()
  simp only [CostedReduction.eval, Comp.eval, pure_bind]
  exact (hSim _ ()).bind fun _ => .ret _

private def Comp.NoQuery {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .bind c k => Comp.NoQuery c ∧ Comp.NoQuery k
  | _, _, .ite _ c d => Comp.NoQuery c ∧ Comp.NoQuery d
  | _, _, .caseOpt _ n s => Comp.NoQuery n ∧ Comp.NoQuery s
  | _, _, .caseSum _ l r => Comp.NoQuery l ∧ Comp.NoQuery r
  | _, _, .sample _ _ => True
  | _, _, .query _ _ => False
  | _, _, .iter _ _ body => Comp.NoQuery body
  | _, _, .findM _ _ p => Comp.NoQuery p
  | _, _, .anyM _ _ p => Comp.NoQuery p
  | _, _, .mapM _ _ f => Comp.NoQuery f
  | _, _, .consumeFirstM _ _ p _ => Comp.NoQuery p
  | _, _, .foldM _ _ _ f => Comp.NoQuery f

private theorem Comp.NoQuery.renameM {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (ren : ∀ ⦃u⦄, Var Γ u → Var Δ u) {c : Comp O I Γ t} (hc : Comp.NoQuery c) :
    Comp.NoQuery (c.renameM ren) := by
  induction c generalizing Δ with
  | ret _ | sample _ _ => trivial
  | query _ _ => exact hc
  | bind _ _ ihc ihk | ite _ _ _ ihc ihk | caseOpt _ _ _ ihc ihk | caseSum _ _ _ ihc ihk =>
    exact ⟨ihc _ hc.1, ihk _ hc.2⟩
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih =>
    exact ih _ hc

private theorem Comp.NoQuery.eval_coinOnly {S : Sig} {O : Ops S} {κ : Type}
    {G : OracleSpec.{0, 0} κ} {I : Iface S (unifSpec + G)}
    (hFwd : ∀ n, I.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    {Γ : List (Ty S)} {t : Ty S} {c : Comp O I Γ t} (hc : Comp.NoQuery c) (ρ : Env Γ) :
    CoinOnly (c.eval ρ) := by
  induction c with
  | ret _ => exact .ret _
  | bind _ _ ihc ihk => exact (ihc hc.1 ρ).bind fun x => ihk hc.2 (.cons x ρ)
  | ite b _ _ ihc ihd =>
    dsimp only [Comp.eval]; split_ifs <;> [exact ihc hc.1 ρ; exact ihd hc.2 ρ]
  | caseOpt e _ _ ihn ihs =>
    dsimp only [Comp.eval]; cases e.eval ρ <;> [exact ihn hc.1 ρ; exact ihs hc.2 (.cons _ ρ)]
  | caseSum e _ _ ihl ihr =>
    dsimp only [Comp.eval]; cases e.eval ρ <;> [exact ihl hc.1 (.cons _ ρ); exact ihr hc.2 (.cons _ ρ)]
  | sample s e => exact CoinOnly.liftP I hFwd _
  | query _ _ => exact False.elim hc
  | iter n e _ ih => exact CoinOnly.iterM _ (fun a => ih hc (.cons a ρ)) n (e.eval ρ)
  | findM K l _ ih => exact CoinOnly.findML _ (fun a => ih hc (.cons a ρ)) ((l.eval ρ).take K)
  | anyM K l _ ih => exact CoinOnly.anyML _ (fun a => ih hc (.cons a ρ)) ((l.eval ρ).take K)
  | mapM K l _ ih => exact CoinOnly.mapML _ (fun a => ih hc (.cons a ρ)) ((l.eval ρ).take K)
  | consumeFirstM K l _ _ ih =>
    exact CoinOnly.consumeFirstML _ _ (fun a => ih hc (.cons a ρ)) ((l.eval ρ).take K)
  | foldM K l z _ ih =>
    exact CoinOnly.foldML _ (fun a b => ih hc (.cons a (.cons b ρ))) (z.eval ρ) ((l.eval ρ).take K)

private theorem liftBaseSamp_noQuery {Γ : List (Ty SigA)}
    (s : UniformSamplerTag ReductionDsl.AtomicBaseUnif)
    (e : Expr OpsF Γ ((ReductionDsl.atomicBaseSamplers ℓ Pt).sDom s)) :
    Comp.NoQuery (liftBaseSamp s e) := by
  cases s with
  | bool | index _ => trivial
  | base b => cases b <;> trivial

private theorem liftFsCoinComp_noQuery {Γ : List (Ty SigA)} {t : Ty SigA}
    (c : Comp (atomicFsOps ℓ Pt C encT) (coinOnlyBaseIface ℓ Pt) Γ t) :
    Comp.NoQuery (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) c) := by
  induction c with
  | ret _ => trivial
  | sample s _ => exact liftBaseSamp_noQuery ℓ Pt C Dh encPt encT lam s _
  | query g _ => nomatch g
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    exact ⟨ih1, ih2⟩
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih => exact ih

private theorem liftNoQuerySlotComp_noQuery {Γ : List (Ty SigA)} {t : Ty SigA}
    (dflt : Expr OpsF [] (.opt wireSaltCtT)) (dfltM : Expr OpsF [] (.opt PlainT))
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    Comp.NoQuery (liftNoQuerySlotComp dflt dfltM c) := by
  induction c with
  | ret _ => trivial
  | sample s _ => exact liftBaseSamp_noQuery ℓ Pt C Dh encPt encT lam s _
  | query g _ => cases g <;> trivial
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    exact ⟨ih1, ih2⟩
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih => exact ih

private theorem substNoQueryComp_noQuery {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (hSamp : ∀ s {Δ} (e : Expr O Δ (I₁.smp.sDom s)), Comp.NoQuery (mapSamp s e))
    {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
    (c : Comp O I₁ Γ t) (hc : c.queries (fun _ => 1) (fun _ => 0) = 0) :
    Comp.NoQuery (substNoQueryComp mapSamp envMap c hc) := by
  induction c generalizing Δ with
  | ret _ => trivial
  | bind _ _ ihc ihk =>
    exact ⟨ihc _ (by simp [Comp.queries] at hc; omega), ihk _ (by simp [Comp.queries] at hc; omega)⟩
  | ite _ _ _ ihc ihd | caseOpt _ _ _ ihc ihd | caseSum _ _ _ ihc ihd =>
    exact ⟨ihc _ (by simp [Comp.queries] at hc; omega), ihd _ (by simp [Comp.queries] at hc; omega)⟩
  | sample s _ => exact hSamp s _
  | query _ _ => exfalso; simp [Comp.queries] at hc
  | iter n _ _ ih =>
    cases n with
    | zero => trivial
    | succ n => exact ih _ (by simp [Comp.queries] at hc; omega)
  | foldM K _ _ _ ih | findM K _ _ ih | anyM K _ _ ih | mapM K _ _ ih | consumeFirstM K _ _ _ ih =>
    cases K with
    | zero => trivial
    | succ K => exact ih _ (by simp [Comp.queries] at hc; omega)

private theorem substQueryComp_noQuery {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {rStTy : Ty S}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (hSamp : ∀ s {Δ} (e : Expr O Δ (I₁.smp.sDom s)), Comp.NoQuery (mapSamp s e))
    (hQ : ∀ g, Comp.NoQuery (qImpl g))
    {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (rExpr : Expr O Δ rStTy)
    (c : Comp O I₁ Γ t) :
    Comp.NoQuery (substQueryComp mapSamp qImpl envMap rExpr c) := by
  induction c generalizing Δ with
  | ret _ => trivial
  | bind _ _ ihc ihk => exact ⟨ihc _ _, ihk _ _⟩
  | ite _ _ _ ihc ihd | caseOpt _ _ _ ihc ihd | caseSum _ _ _ ihc ihd =>
    exact ⟨ihc _ _, ihd _ _⟩
  | sample s _ => exact ⟨hSamp s _, trivial⟩
  | query g _ => exact ⟨trivial, trivial, trivial, (hQ g).renameM _⟩
  | iter _ _ _ ih | foldM _ _ _ _ ih => exact ih _ _
  | findM K l p ih =>
    cases K with
    | zero => trivial
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · exact ⟨substNoQueryComp_noQuery mapSamp hSamp envMap _ hc0, trivial⟩
      · exact ⟨⟨ih _ _, trivial⟩, trivial⟩
  | anyM K l p ih =>
    cases K with
    | zero => trivial
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · exact ⟨substNoQueryComp_noQuery mapSamp hSamp envMap _ hc0, trivial⟩
      · exact ⟨trivial, ih _ _⟩
  | mapM K l f ih =>
    cases K with
    | zero => trivial
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · exact ⟨substNoQueryComp_noQuery mapSamp hSamp envMap _ hc0, trivial⟩
      · exact ⟨⟨ih _ _, trivial⟩, trivial, trivial⟩
  | consumeFirstM K l p mk ih =>
    cases K with
    | zero => trivial
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · exact ⟨substNoQueryComp_noQuery mapSamp hSamp envMap _ hc0, trivial⟩
      · exact ⟨⟨trivial, ih _ _, trivial, trivial⟩, trivial, trivial⟩

private theorem slotOtccaImpl_noQuery (nf : Bool) (qSim : ℕ) (g : OTCCATag) :
    Comp.NoQuery (slotOtccaImpl ℓ Pt C Dh encPt encT idOf lam nf qSim g) := by
  cases g <;>
    exact ⟨trivial, (liftNoQuerySlotComp_noQuery ℓ Pt C Dh encPt encT lam _ _ _).renameM _, trivial⟩

private theorem liftSlotHybStep_noQuery {qTy rTy : Ty SigA} (nf : Bool) (qSim : ℕ)
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt)
      [qTy, hybSessStTy ℓ Pt] (.prod rTy (hybSessStTy ℓ Pt))) :
    Comp.NoQuery (liftSlotHybStep ℓ Pt C Dh encPt encT idOf lam nf qSim c) :=
  ⟨substQueryComp_noQuery _ _
    (fun s {_} e => liftBaseSamp_noQuery ℓ Pt C Dh encPt encT lam s e)
    (slotOtccaImpl_noQuery ℓ Pt C Dh encPt encT idOf lam nf qSim) _ _ _, trivial⟩

private theorem runLazyPubSess_noQuery {sTy : Ty SigA}
    {mkInit : Comp OpsF IfaceF [] sTy}
    {trS : Comp OpsF IfaceF [.prod fig8PubAdT PlainT, sTy] (.prod (.opt lctT) sTy)}
    {chS : Comp OpsF IfaceF [.prod fig8PubAdT (.prod PlainT PlainT), sTy] (.prod (.opt lctT) sTy)}
    {csS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt fsSendStT) sTy)}
    {crS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt (.prod fsSendStT fsRecvStT)) sTy)}
    {dlS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy)}
    {ijS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy)}
    (hInit : Comp.NoQuery mkInit) (hTr : Comp.NoQuery trS) (hCh : Comp.NoQuery chS)
    (hCs : Comp.NoQuery csS) (hCr : Comp.NoQuery crS)
    (hDl : Comp.NoQuery dlS) (hIj : Comp.NoQuery ijS)
    (g : FSAEADTag) :
    Comp.NoQuery (runLazyPubSess ℓ Pt C Dh encPt encT lam mkInit trS chS csS crS dlS ijS g) := by
  have hEns : Comp.NoQuery (ensureSessInit ℓ Pt C Dh encPt encT lam mkInit) :=
    ⟨hInit.renameM _, trivial⟩
  cases g with
  | tr => exact ⟨trivial, hEns.renameM _, trivial, hTr.renameM _, trivial⟩
  | ch => exact ⟨trivial, hEns.renameM _, trivial, hCh.renameM _, trivial⟩
  | cs => exact ⟨trivial, hEns.renameM _, hCs.renameM _, trivial⟩
  | cr => exact ⟨trivial, hEns.renameM _, hCr.renameM _, trivial⟩
  | dl => exact ⟨trivial, trivial, hEns.renameM _, trivial, hDl.renameM _, trivial, trivial⟩
  | ij => exact ⟨trivial, trivial, hEns.renameM _, trivial, hIj.renameM _, trivial, trivial⟩

private theorem exprRenameM_eval {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (ren : ∀ ⦃u⦄, Var Γ u → Var Δ u) (e : Expr O Γ t) (ρ₁ : Env Γ) (ρ₂ : Env Δ)
    (hρ : ∀ {u} (v : Var Γ u), ρ₂.get (ren v) = ρ₁.get v) :
    (e.renameM ren).eval ρ₂ = e.eval ρ₁ := by
  induction e generalizing Δ with
  | var v => exact hρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb
  | and _ _ iha ihb | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb
  | appendL _ _ _ iha ihb | tget _ _ iha ihb =>
    simp [Expr.renameM, Expr.eval, iha _ ρ₁ ρ₂ hρ, ihb _ ρ₁ ρ₂ hρ]
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | op _ _ iha | len _ iha | tconst _ iha =>
    simp [Expr.renameM, Expr.eval, iha _ ρ₁ ρ₂ hρ]
  | tset _ _ _ ihm ihi iha =>
    dsimp only [Expr.renameM, Expr.eval]
    rw [ihm _ ρ₁ ρ₂ hρ, ihi _ ρ₁ ρ₂ hρ, iha _ ρ₁ ρ₂ hρ]
  | ite _ _ _ ihc iha ihb =>
    dsimp only [Expr.renameM, Expr.eval]
    rw [ihc _ ρ₁ ρ₂ hρ, iha _ ρ₁ ρ₂ hρ, ihb _ ρ₁ ρ₂ hρ]
  | caseOpt e _ _ ihe ihn ihs =>
    dsimp only [Expr.renameM, Expr.eval]; rw [ihe _ ρ₁ ρ₂ hρ]
    cases e.eval ρ₁ with
    | none => exact ihn _ ρ₁ ρ₂ hρ
    | some x =>
      exact ihs _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
  | caseSum e _ _ ihe ihl ihr =>
    dsimp only [Expr.renameM, Expr.eval]; rw [ihe _ ρ₁ ρ₂ hρ]
    cases e.eval ρ₁ with
    | inl x =>
      exact ihl _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
    | inr y =>
      exact ihr _ (.cons y ρ₁) (.cons y ρ₂) fun | .zero => rfl | .succ w => hρ w
  | letE e _ ihe ihb =>
    dsimp only [Expr.renameM, Expr.eval]; rw [ihe _ ρ₁ ρ₂ hρ]
    exact ihb _ (.cons (e.eval ρ₁) ρ₁) (.cons (e.eval ρ₁) ρ₂) fun
      | .zero => rfl | .succ w => hρ w
  | findB K l _ ihl ihp =>
    dsimp only [Expr.renameM, Expr.eval]; rw [ihl _ ρ₁ ρ₂ hρ]
    congr 1; funext x
    exact ihp _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
  | anyB K l _ ihl ihp =>
    dsimp only [Expr.renameM, Expr.eval]; rw [ihl _ ρ₁ ρ₂ hρ]
    congr 1; funext x
    exact ihp _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
  | mapB K l _ ihl ihf =>
    dsimp only [Expr.renameM, Expr.eval]; rw [ihl _ ρ₁ ρ₂ hρ]
    congr 1; funext x
    exact ihf _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
  | foldrB K l z _ ihl ihz ihf =>
    dsimp only [Expr.renameM, Expr.eval]; rw [ihl _ ρ₁ ρ₂ hρ, ihz _ ρ₁ ρ₂ hρ]
    congr 1; funext x; funext acc
    exact ihf _ (.cons x (.cons acc ρ₁)) (.cons x (.cons acc ρ₂)) fun
      | .zero => rfl | .succ .zero => rfl | .succ (.succ w) => hρ w

private theorem compRenameM_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (ren : ∀ ⦃u⦄, Var Γ u → Var Δ u) (c : Comp O I Γ t) (ρ₁ : Env Γ) (ρ₂ : Env Δ)
    (hρ : ∀ {u} (v : Var Γ u), ρ₂.get (ren v) = ρ₁.get v) :
    (c.renameM ren).eval ρ₂ = c.eval ρ₁ := by
  induction c generalizing Δ with
  | ret e => simp [Comp.renameM, Comp.eval, exprRenameM_eval ren e ρ₁ ρ₂ hρ]
  | bind _ _ ihc ihk =>
    dsimp only [Comp.renameM, Comp.eval]; rw [ihc _ ρ₁ ρ₂ hρ]
    exact bind_congr fun x => ihk _ (.cons x ρ₁) (.cons x ρ₂) fun
      | .zero => rfl | .succ w => hρ w
  | ite b _ _ ihc ihd =>
    dsimp only [Comp.renameM, Comp.eval]
    rw [exprRenameM_eval ren b ρ₁ ρ₂ hρ, ihc _ ρ₁ ρ₂ hρ, ihd _ ρ₁ ρ₂ hρ]
  | caseOpt e _ _ ihn ihs =>
    dsimp only [Comp.renameM, Comp.eval]; rw [exprRenameM_eval ren e ρ₁ ρ₂ hρ]
    cases e.eval ρ₁ with
    | none => exact ihn _ ρ₁ ρ₂ hρ
    | some x =>
      exact ihs _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
  | caseSum e _ _ ihl ihr =>
    dsimp only [Comp.renameM, Comp.eval]; rw [exprRenameM_eval ren e ρ₁ ρ₂ hρ]
    cases e.eval ρ₁ with
    | inl x =>
      exact ihl _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
    | inr y =>
      exact ihr _ (.cons y ρ₁) (.cons y ρ₂) fun | .zero => rfl | .succ w => hρ w
  | sample s e =>
    dsimp only [Comp.renameM, Comp.eval]; rw [exprRenameM_eval ren e ρ₁ ρ₂ hρ]
  | query g e =>
    dsimp only [Comp.renameM, Comp.eval]; rw [exprRenameM_eval ren e ρ₁ ρ₂ hρ]
  | iter n e _ ih =>
    dsimp only [Comp.renameM, Comp.eval]; rw [exprRenameM_eval ren e ρ₁ ρ₂ hρ]
    congr 1; funext a
    exact ih _ (.cons a ρ₁) (.cons a ρ₂) fun | .zero => rfl | .succ w => hρ w
  | findM K l _ ih =>
    dsimp only [Comp.renameM, Comp.eval]; rw [exprRenameM_eval ren l ρ₁ ρ₂ hρ]
    congr 1; funext x
    exact ih _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
  | anyM K l _ ih =>
    dsimp only [Comp.renameM, Comp.eval]; rw [exprRenameM_eval ren l ρ₁ ρ₂ hρ]
    congr 1; funext x
    exact ih _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
  | mapM K l _ ih =>
    dsimp only [Comp.renameM, Comp.eval]; rw [exprRenameM_eval ren l ρ₁ ρ₂ hρ]
    congr 1; funext x
    exact ih _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
  | consumeFirstM K l _ mk ih =>
    dsimp only [Comp.renameM, Comp.eval]; rw [exprRenameM_eval ren l ρ₁ ρ₂ hρ]
    congr 1
    · funext x; exact ih _ (.cons x ρ₁) (.cons x ρ₂) fun | .zero => rfl | .succ w => hρ w
    · funext x
      exact exprRenameM_eval _ mk (.cons x ρ₁) (.cons x ρ₂) fun
        | .zero => rfl | .succ w => hρ w
  | foldM K l z _ ih =>
    dsimp only [Comp.renameM, Comp.eval]
    rw [exprRenameM_eval ren l ρ₁ ρ₂ hρ, exprRenameM_eval ren z ρ₁ ρ₂ hρ]
    congr 1; funext x; funext acc
    exact ih _ (.cons x (.cons acc ρ₁)) (.cons x (.cons acc ρ₂)) fun
      | .zero => rfl | .succ .zero => rfl | .succ (.succ w) => hρ w

private theorem exprWk1_eval_qsub {S : Sig} {O : Ops S} {a t : Ty S} {Γ : List (Ty S)}
    (e : Expr O Γ t) (x : a.denote) (ρ : Env Γ) :
    (exprWk1 e).eval (.cons x ρ) = e.eval ρ :=
  exprRenameM_eval (fun _ v => .succ v) e ρ (.cons x ρ) fun _ => rfl

private theorem substExpr_eval_qsub {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (e : Expr O Γ t)
    (ρ₁ : Env Γ) (ρ₂ : Env Δ)
    (hEnv : ∀ {u} (v : Var Γ u), (envMap v).eval ρ₂ = ρ₁.get v) :
    (substExpr envMap e).eval ρ₂ = e.eval ρ₁ := by
  induction e generalizing Δ with
  | var v => exact hEnv v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb
  | and _ _ iha ihb | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb
  | appendL _ _ _ iha ihb | tget _ _ iha ihb =>
    simp [substExpr, Expr.eval, iha envMap ρ₁ ρ₂ hEnv, ihb envMap ρ₁ ρ₂ hEnv]
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | op _ _ iha | len _ iha | tconst _ iha =>
    simp [substExpr, Expr.eval, iha envMap ρ₁ ρ₂ hEnv]
  | tset _ _ _ ihm ihi iha =>
    dsimp only [substExpr, Expr.eval]
    rw [ihm envMap ρ₁ ρ₂ hEnv, ihi envMap ρ₁ ρ₂ hEnv, iha envMap ρ₁ ρ₂ hEnv]
  | ite _ _ _ ihc iha ihb =>
    dsimp only [substExpr, Expr.eval]
    rw [ihc envMap ρ₁ ρ₂ hEnv, iha envMap ρ₁ ρ₂ hEnv, ihb envMap ρ₁ ρ₂ hEnv]
  | caseOpt e _ _ ihe ihn ihs =>
    dsimp only [substExpr, Expr.eval]; rw [ihe envMap ρ₁ ρ₂ hEnv]
    cases e.eval ρ₁ with
    | none => exact ihn envMap ρ₁ ρ₂ hEnv
    | some x =>
      exact ihs (liftEnv1 envMap) (.cons x ρ₁) (.cons x ρ₂) fun
        | .zero => rfl
        | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)
  | caseSum e _ _ ihe ihl ihr =>
    dsimp only [substExpr, Expr.eval]; rw [ihe envMap ρ₁ ρ₂ hEnv]
    cases e.eval ρ₁ with
    | inl x =>
      exact ihl (liftEnv1 envMap) (.cons x ρ₁) (.cons x ρ₂) fun
        | .zero => rfl
        | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)
    | inr y =>
      exact ihr (liftEnv1 envMap) (.cons y ρ₁) (.cons y ρ₂) fun
        | .zero => rfl
        | .succ w => (exprWk1_eval_qsub (envMap w) y ρ₂).trans (hEnv w)
  | letE e _ ihe ihb =>
    dsimp only [substExpr, Expr.eval]; rw [ihe envMap ρ₁ ρ₂ hEnv]
    exact ihb (liftEnv1 envMap) (.cons (e.eval ρ₁) ρ₁) (.cons (e.eval ρ₁) ρ₂) fun
      | .zero => rfl
      | .succ w => (exprWk1_eval_qsub (envMap w) (e.eval ρ₁) ρ₂).trans (hEnv w)
  | findB K l _ ihl ihp =>
    dsimp only [substExpr, Expr.eval]; rw [ihl envMap ρ₁ ρ₂ hEnv]
    congr 1; funext x
    exact ihp (liftEnv1 envMap) (.cons x ρ₁) (.cons x ρ₂) fun
      | .zero => rfl
      | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)
  | anyB K l _ ihl ihp =>
    dsimp only [substExpr, Expr.eval]; rw [ihl envMap ρ₁ ρ₂ hEnv]
    congr 1; funext x
    exact ihp (liftEnv1 envMap) (.cons x ρ₁) (.cons x ρ₂) fun
      | .zero => rfl
      | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)
  | mapB K l _ ihl ihf =>
    dsimp only [substExpr, Expr.eval]; rw [ihl envMap ρ₁ ρ₂ hEnv]
    congr 1; funext x
    exact ihf (liftEnv1 envMap) (.cons x ρ₁) (.cons x ρ₂) fun
      | .zero => rfl
      | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)
  | foldrB K l z _ ihl ihz ihf =>
    dsimp only [substExpr, Expr.eval]; rw [ihl envMap ρ₁ ρ₂ hEnv, ihz envMap ρ₁ ρ₂ hEnv]
    congr 1; funext x; funext acc
    exact ihf (liftEnv2 envMap) (.cons x (.cons acc ρ₁)) (.cons x (.cons acc ρ₂)) fun
      | .zero => rfl
      | .succ .zero => rfl
      | .succ (.succ w) =>
        (exprWk1_eval_qsub _ x _).trans ((exprWk1_eval_qsub (envMap w) acc ρ₂).trans (hEnv w))

private theorem callBinaryComp_eval_qsub {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {a b c : Ty S} {Δ : List (Ty S)}
    (m : Comp O I [a, b] c) (va : a.denote) (vb : b.denote) (ρ : Env Δ) :
    (callBinaryComp m).eval (.cons (va, vb) ρ) = m.eval (.cons va (.cons vb .nil)) := by
  exact callBinaryComp_eval m (va, vb) ρ

private def fsEncQuery_qsub :
    (g : FSAEADTag) → ((IfaceF).dom g).denote →
      (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Domain
  | .tr, (h, (pv, m)) =>
    .inl (.inl (.inl (.inl (.inl (h, (ReductionDsl.lpubOfV pv, m))))))
  | .ch, (h, ((pv0, m0), (pv1, m1))) =>
    .inl (.inl (.inl (.inl (.inr (h, ((ReductionDsl.lpubOfV pv0, m0), (ReductionDsl.lpubOfV pv1, m1)))))))
  | .cs, () => .inl (.inl (.inl (.inr ())))
  | .cr, () => .inl (.inl (.inr ()))
  | .dl, (h, cv) => .inl (.inr (h, ReductionDsl.lctOfV cv))
  | .ij, (h, cv) => .inr (h, ReductionDsl.lctOfV cv)

private theorem fsaeadHeaderIface_enc_eq_qsub (g : FSAEADTag) (x : ((IfaceF).dom g).denote) :
    (IfaceF).enc g x = .inr (fsEncQuery_qsub ℓ Pt g x) := by
  cases g <;> rfl

private theorem fsaeadMultiAtomicIface_enc_eq_qsub (qep qR B0 : ℕ) (g : FSHdrTag)
    (sx : ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).dom g).denote) :
    (fsaeadMultiAtomicIface ℓ Pt qep qR B0).enc g sx =
      .inr ⟨sx.1, fsEncQuery_qsub ℓ Pt (toFsTag g) sx.2⟩ := by
  cases g <;> rfl

private def fsInvDec :
    (g : FSAEADTag) → {x : ((IfaceF).dom g).denote} →
      ((IfaceF).cod g).denote →
      (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Range
        (fsEncQuery_qsub ℓ Pt g x)
  | .tr, _, r => r.map ReductionDsl.lctOfV
  | .ch, _, r => r.map ReductionDsl.lctOfV
  | .cs, _, r => r.map ReductionDsl.fsSendStOfV
  | .cr, _, r => r.map fun (ss, rs) => (ReductionDsl.fsSendStOfV ss, ReductionDsl.fsRecvStOfV rs)
  | .dl, _, r =>
    r.map (ReductionDsl.fsRrDec (msgT := .prod lpubT PlainT) fun (pv, m) => (ReductionDsl.lpubOfV pv, m))
  | .ij, _, r =>
    r.map (ReductionDsl.fsRrDec (msgT := .prod lpubT PlainT) fun (pv, m) => (ReductionDsl.lpubOfV pv, m))

private theorem fsaeadHeaderIface_dec_fsInvDec (g : FSAEADTag) (x : ((IfaceF).dom g).denote)
    (v : ((IfaceF).cod g).denote) :
    (IfaceF).dec g x
      (show (unifSpec + CryptoGames.FSAEAD.spec
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Range ((IfaceF).enc g x) from
        (fsaeadHeaderIface_enc_eq_qsub ℓ Pt g x).symm ▸ fsInvDec ℓ Pt g (x := x) v) = v := by
  cases g with
  | tr | ch =>
    cases v with
    | none => rfl
    | some cv =>
      exact congrArg some (Computational.Proofs.ReductionDsl.FsAtomicMacros.lctV_lctOfV cv)
  | cs =>
    cases v with
    | none => rfl
    | some sv =>
      exact congrArg some (Computational.Proofs.ReductionDsl.FsAtomicMacros.fsSendStV_fsSendStOfV sv)
  | cr =>
    cases v with
    | none => rfl
    | some p =>
      exact congrArg some (Prod.ext
        (Computational.Proofs.ReductionDsl.FsAtomicMacros.fsSendStV_fsSendStOfV p.1)
        (Computational.Proofs.ReductionDsl.FsAtomicMacros.fsRecvStV_fsRecvStOfV p.2))
  | dl | ij =>
    rcases v with _ | (_ | ⟨idx, _ | ⟨pv, m⟩⟩)
    · rfl
    · rfl
    · rfl
    · dsimp only [fsaeadHeaderIface, fsInvDec, Option.map, ReductionDsl.fsRrDec, ReductionDsl.fsRrEnc]
      rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubV_lpubOfV]

private theorem fsMultiPureAuxBundle_query_eval_qsub (qep qR B0 : ℕ) (sampBV : ProbComp (BitVec 256))
    (g : (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).Tag)
    (z : ((fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).dom g).denote) :
    ((fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 sampBV).queryMacro g).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ <$>
        ((fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV sampBV sampBV ($ᵗ Pt) sampBV).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + multiSessSpec (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256))
              (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)))
            ((fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
              (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              sampBV sampBV sampBV ($ᵗ Pt) sampBV).enc g z)) :
            OracleComp (unifSpec + multiSessSpec (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256))
              (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt))) _)) := by
  rw [Functor.map_map]
  cases g with
  | tr =>
    rcases z with ⟨sIdx, ⟨ep, _ | T⟩, pub, m⟩ <;>
      (dsimp only [fsMultiPureAuxBundle, Comp.eval, Expr.eval, env_get_zero, Option.map,
        fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, fsaeadMultiHeaderAdIface,
        fsaeadHeaderAdIface, toVal, toDenCKA, Function.comp_def]
       rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubOfV_lpubV])
  | ch =>
    rcases z with ⟨sIdx, ⟨ep, _ | T⟩, ⟨pub0, m0⟩, ⟨pub1, m1⟩⟩ <;>
      (dsimp only [fsMultiPureAuxBundle, Comp.eval, Expr.eval, env_get_zero, Option.map,
        fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, fsaeadMultiHeaderAdIface,
        fsaeadHeaderAdIface, toVal, toDenCKA, Function.comp_def]
       rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubOfV_lpubV pub0,
           Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubOfV_lpubV pub1])
  | cs | cr =>
    rcases z with ⟨sIdx, ⟨⟩⟩
    rfl
  | dl | ij =>
    rcases z with ⟨sIdx, ⟨ep, _ | T⟩, c⟩ <;>
      (dsimp only [fsMultiPureAuxBundle, Comp.eval, Expr.eval, env_get_zero, Option.map,
        fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, fsaeadMultiHeaderAdIface,
        fsaeadHeaderAdIface, toVal, toDenCKA, Function.comp_def]
       rw [lctOfV_lctV]
       congr 1; funext r; rcases r with _ | (_ | ⟨idx, _ | ⟨pub, m⟩⟩) <;> rfl)

private theorem fsMultiPureAuxBundle_samp_querySubsumes (qep qR B0 : ℕ) (s : CKASamp)
    (z : ((fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    QuerySubsumes
      (((fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)))
      (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s <;>
    exact Computational.Proofs.SessionCostedFig8.BundlesAuxSize.querySubsumes_liftP_of_support_subset
      (fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (fun _ => rfl) (fun _ => rfl) (fun _ hx => hx)

private theorem compilePureAuxRed_fsMulti_querySubsumes (qep qR B0 : ℕ)
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
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    QuerySubsumes
      ((compilePureAuxRed
        (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
        (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  have h := QuerySubsumes.compilePureAuxRed_querySubsumes
    (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
    (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (Computational.Proofs.SessionCostedFig8.BundlesCompilers.ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (fsMultiPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam qep qR B0)
    (fun g z => .of_eq (fsMultiPureAuxBundle_query_eval_qsub ℓ Pt C Dh encPt encT idOf lam qep qR B0 _ g z))
    (fun _ => rfl) (fun _ => rfl)
    (Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
    (Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

private theorem compilePureAuxRed_fsMultiDF_querySubsumes (qep qR B0 : ℕ)
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
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    QuerySubsumes
      ((compilePureAuxRed
        (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
        (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  have h := QuerySubsumes.compilePureAuxRed_querySubsumes
    (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
    (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (Computational.Proofs.SessionCostedFig8.BundlesCompilers.ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (fsMultiPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam qep qR B0)
    (fun g z => .of_eq (fsMultiPureAuxBundle_query_eval_qsub ℓ Pt C Dh encPt encT idOf lam qep qR B0 _ g z))
    (fun _ => rfl) (fun _ => rfl)
    (Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8AdaptQDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (Computational.Proofs.SessionCostedFig8.BundlesAdapters.fig8AdaptRDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

private inductive RouterSubsumesR {κ : Type} {G : OracleSpec.{0, 0} κ}
    (j : ℕ) (RespSimOk : (q : κ) → G.Range q → Prop) {α β : Type} (Rel : α → β → Prop) :
    OracleComp (unifSpec + G) α → OracleComp (unifSpec + multiSessSpec G) β → Prop where
  | ret {a : α} {b : β} : Rel a b → RouterSubsumesR j RespSimOk Rel (pure a) (pure b)
  | coin_l (n : ℕ) (k : Fin (n + 1) → OracleComp (unifSpec + G) α)
      (oa₂ : OracleComp (unifSpec + multiSessSpec G) β) :
      (∀ u, RouterSubsumesR j RespSimOk Rel (k u) oa₂) →
      RouterSubsumesR j RespSimOk Rel
        (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= k) oa₂
  | coin_r (oa₁ : OracleComp (unifSpec + G) α) (n : ℕ)
      (k : Fin (n + 1) → OracleComp (unifSpec + multiSessSpec G) β) (u : Fin (n + 1)) :
      RouterSubsumesR j RespSimOk Rel oa₁ (k u) →
      RouterSubsumesR j RespSimOk Rel oa₁
        (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec G) (.inl n)) >>= k)
  | sess_eq (q : κ) (k₁ : (unifSpec + G).Range (.inr q) → OracleComp (unifSpec + G) α)
      (k₂ : (unifSpec + multiSessSpec G).Range (.inr ⟨j, q⟩) → OracleComp (unifSpec + multiSessSpec G) β) :
      (∀ r, RouterSubsumesR j RespSimOk Rel (k₁ r) (k₂ r)) →
      RouterSubsumesR j RespSimOk Rel
        (liftM (OracleSpec.query (spec := unifSpec + G) (.inr q)) >>= k₁)
        (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec G) (.inr ⟨j, q⟩)) >>= k₂)
  | sess_ne (s : ℕ) (hs : s ≠ j) (q : κ)
      (r : (unifSpec + multiSessSpec G).Range (.inr ⟨s, q⟩)) (hr : RespSimOk q r)
      (oa₁ : OracleComp (unifSpec + G) α)
      (k₂ : (unifSpec + multiSessSpec G).Range (.inr ⟨s, q⟩) → OracleComp (unifSpec + multiSessSpec G) β) :
      RouterSubsumesR j RespSimOk Rel oa₁ (k₂ r) →
      RouterSubsumesR j RespSimOk Rel oa₁
        (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec G) (.inr ⟨s, q⟩)) >>= k₂)

private theorem RouterSubsumesR.bind {κ : Type} {G : OracleSpec.{0, 0} κ}
    {j : ℕ} {RespSimOk : (q : κ) → G.Range q → Prop}
    {α₁ β₁ α₂ β₂ : Type} {Rel₁ : α₁ → β₁ → Prop} {Rel₂ : α₂ → β₂ → Prop}
    {oa₁ : OracleComp (unifSpec + G) α₁}
    {oa₂ : OracleComp (unifSpec + multiSessSpec G) β₁}
    {k₁ : α₁ → OracleComp (unifSpec + G) α₂}
    {k₂ : β₁ → OracleComp (unifSpec + multiSessSpec G) β₂}
    (h : RouterSubsumesR j RespSimOk Rel₁ oa₁ oa₂)
    (hk : ∀ a b, Rel₁ a b → RouterSubsumesR j RespSimOk Rel₂ (k₁ a) (k₂ b)) :
    RouterSubsumesR j RespSimOk Rel₂ (oa₁ >>= k₁) (oa₂ >>= k₂) := by
  induction h with
  | ret hab => simp only [pure_bind]; exact hk _ _ hab
  | coin_l n _ _ _ ih => rw [bind_assoc]; exact .coin_l n _ _ ih
  | coin_r _ n _ u _ ih => rw [bind_assoc]; exact .coin_r _ n _ u ih
  | sess_eq q _ _ _ ih => rw [bind_assoc, bind_assoc]; exact .sess_eq q _ _ ih
  | sess_ne s hs q r hr _ _ _ ih => rw [bind_assoc]; exact .sess_ne s hs q r hr _ _ ih

private theorem RouterSubsumesR.of_coinOnly_l {κ : Type} {G : OracleSpec.{0, 0} κ}
    {j : ℕ} {RespSimOk : (q : κ) → G.Range q → Prop}
    {α β : Type} {Rel : α → β → Prop}
    {oa₁ : OracleComp (unifSpec + G) α} (hc : CoinOnly oa₁)
    {oa₂ : OracleComp (unifSpec + multiSessSpec G) β}
    (h : ∀ a ∈ support oa₁, RouterSubsumesR j RespSimOk Rel (pure a) oa₂) :
    RouterSubsumesR j RespSimOk Rel oa₁ oa₂ := by
  induction hc with
  | ret a => exact h a (by simp)
  | coin n k _ ih =>
    exact .coin_l n k oa₂ fun u => ih u fun a ha =>
      h a (by rw [mem_support_bind_iff]; exact ⟨u, by simp, ha⟩)

private theorem RouterSubsumesR.liftP_align {S₁ S₂ : Sig} {κ : Type} {G : OracleSpec.{0, 0} κ}
    {j : ℕ} {RespSimOk : (q : κ) → G.Range q → Prop}
    (I₂ : Iface S₂ (unifSpec + G)) (I₁ : Iface S₁ (unifSpec + multiSessSpec G))
    (hFwd₂ : ∀ n, I₂.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    (hFwd₁ : ∀ n, I₁.fwdU n = liftM (OracleSpec.query (spec := unifSpec + multiSessSpec G) (.inl n)))
    {α γ : Type} (p : ProbComp α) (rVal : γ) :
    RouterSubsumesR j RespSimOk (fun (vr : α × γ) v => vr.1 = v)
      (I₂.liftP p >>= fun v => pure (v, rVal)) (I₁.liftP p) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp only [Iface.liftP, simulateQ_pure, pure_bind]
    exact .ret rfl
  | query_bind n mx ih =>
    rw [Iface.liftP, simulateQ_bind, simulateQ_query, hFwd₂, bind_assoc]
    conv_rhs => rw [Iface.liftP, simulateQ_bind, simulateQ_query, hFwd₁]
    exact .coin_l n _ _ fun u => .coin_r _ n _ u (ih u)

private theorem RouterSubsumesR.isQueryBoundP {κ : Type} {G : OracleSpec.{0, 0} κ}
    {j : ℕ} {RespSimOk : (q : κ) → G.Range q → Prop}
    {α β : Type} {Rel : α → β → Prop}
    {oa₁ : OracleComp (unifSpec + G) α}
    {oa₂ : OracleComp (unifSpec + multiSessSpec G) β}
    (hsub : RouterSubsumesR j RespSimOk Rel oa₁ oa₂)
    (P : G.Domain → Bool) {k : ℕ}
    (hb : oa₂.IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, q⟩ => decide (s = j) && P q) = true) k) :
    oa₁.IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr q => P q) = true) k := by
  induction hsub generalizing k with
  | ret _ => trivial
  | coin_l n _ _ _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp), fun u => ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ih u hb
  | coin_r _ n _ u _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    have hbu := hb.2 u
    simp only [Bool.false_eq_true, ↓reduceIte] at hbu
    exact ih hbu
  | sess_eq q _ _ _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    rw [isQueryBoundP_query_bind_iff]
    simp only [decide_true, Bool.true_and] at hb
    exact ⟨hb.1, fun r => ih r (hb.2 r)⟩
  | sess_ne s hs q r _ _ _ _ ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    have hbr := hb.2 r
    simp only [decide_eq_false hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hbr
    exact ih hbr

private theorem guardedSafePost_inv_query_bind_local {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    {RespOk : (t : (unifSpec + G).Domain) → (unifSpec + G).Range t → Prop}
    {Q : (unifSpec + G).Domain → Prop} {P : α → Prop}
    {t : (unifSpec + G).Domain} {k : (unifSpec + G).Range t → OracleComp (unifSpec + G) α}
    (h : CryptoGames.GuardedSafe.GuardedSafePost RespOk Q P
      (liftM (OracleSpec.query (spec := unifSpec + G) t) >>= k)) :
    ¬ Q t ∧ ∀ u, RespOk t u → CryptoGames.GuardedSafe.GuardedSafePost RespOk Q P (k u) := by
  generalize heq : (liftM (OracleSpec.query (spec := unifSpec + G) t) >>= k) = oa at h
  cases h with
  | pure _ =>
    have hd := congrArg (OracleComp.isPure (spec := unifSpec + G)) heq
    simp at hd
  | query_bind hQt hcont =>
    let headQ : OracleComp (unifSpec + G) α →
        Option (Sigma fun t : (unifSpec + G).Domain =>
          (unifSpec + G).Range t → OracleComp (unifSpec + G) α) :=
      OracleComp.construct (fun _ => none) (fun t mx _ => some ⟨t, mx⟩)
    have hd := congrArg headQ heq
    simp only [headQ, OracleComp.construct_query_bind, Option.some.injEq] at hd
    rcases hd with ⟨rfl, rfl⟩
    exact ⟨hQt, hcont⟩

private theorem RouterSubsumesR.guardedFSInjectShort {CK MK AD Msg α β : Type}
    {j : ℕ} {Rel : α → β → Prop}
    {oa₁ : OracleComp (unifSpec + CryptoGames.FSAEAD.spec
      (RatchetSenderState CK) (RatchetReceiverState CK MK) AD Msg (ℕ × LCt)) α}
    {oa₂ : OracleComp (unifSpec + multiSessSpec (CryptoGames.FSAEAD.spec
      (RatchetSenderState CK) (RatchetReceiverState CK MK) AD Msg (ℕ × LCt))) β}
    (hsub : RouterSubsumesR j
      (fun q r => CryptoGames.Ratchet.LibsignalInst.fsRespShort
        (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK) (.inr q) r)
      Rel oa₁ oa₂)
    (h₂ : CryptoVerification.E2E.Signed.SessionWireQueries.GuardedMultiInjectShort oa₂) :
    CryptoGames.GuardedSafe.GuardedSafePost
      (CryptoGames.Ratchet.LibsignalInst.fsRespShort
        (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK))
      (CryptoGames.Ratchet.LibsignalInst.fsInjectLong
        (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK))
      (fun _ => True) oa₁ := by
  induction hsub with
  | ret _ => exact .pure trivial
  | coin_l _ _ _ _ ih => exact .query_bind not_false fun u _ => ih u h₂
  | coin_r _ _ _ u _ ih =>
    exact ih ((guardedSafePost_inv_query_bind_local h₂).2 u trivial)
  | sess_eq q _ _ _ ih =>
    obtain ⟨hQt, hcont⟩ := guardedSafePost_inv_query_bind_local h₂
    exact .query_bind hQt fun r hr => ih r (hcont r hr)
  | sess_ne s _ q r hr _ _ _ ih =>
    exact ih ((guardedSafePost_inv_query_bind_local h₂).2 r hr)

private theorem foldML_pure_cons_qsub {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} :
    ∀ (xs acc : List α),
      ReductionDsl.foldML (m := m) (fun x ys => pure (x :: ys)) acc xs = pure (xs.reverseAux acc)
  | [], acc => rfl
  | x :: xs, acc => by
    dsimp only [ReductionDsl.foldML, List.reverseAux]
    rw [pure_bind, foldML_pure_cons_qsub xs (x :: acc)]

private theorem reverse_reverseAux_qsub {α : Type} :
    ∀ (xs acc : List α), (xs.reverseAux acc).reverse = acc.reverse ++ xs
  | [], acc => by simp [List.reverseAux]
  | x :: xs, acc => by
    simp only [List.reverseAux, reverse_reverseAux_qsub xs (x :: acc), List.reverse_cons, List.append_assoc,
      List.singleton_append]

private theorem foldML_find_some_qsub {m : Type → Type} [Monad m] [LawfulMonad m] {α ρ : Type}
    (stepNone : α → ρ → m (Option α × ρ)) (v : α) :
    ∀ (xs : List α) (r : ρ),
      ReductionDsl.foldML (m := m)
        (fun x (acc : Option α × ρ) => match acc.1 with
          | none => stepNone x acc.2
          | some _ => pure acc)
        (some v, r) xs = pure (some v, r)
  | [], r => rfl
  | _ :: xs, r => by dsimp only [ReductionDsl.foldML]; rw [pure_bind]; exact foldML_find_some_qsub stepNone v xs r

private theorem foldML_any_true_qsub {m : Type → Type} [Monad m] [LawfulMonad m] {α ρ : Type}
    (stepFalse : α → ρ → m (Bool × ρ)) :
    ∀ (xs : List α) (r : ρ),
      ReductionDsl.foldML (m := m)
        (fun x (acc : Bool × ρ) => if acc.1 then pure acc else stepFalse x acc.2)
        (true, r) xs = pure (true, r)
  | [], r => rfl
  | _ :: xs, r => by
    dsimp only [ReductionDsl.foldML]; simp only [↓reduceIte, pure_bind]
    exact foldML_any_true_qsub stepFalse xs r

private theorem foldML_consume_true_qsub {m : Type → Type} [Monad m] [LawfulMonad m] {α ρ : Type}
    (stepFalse : α → List α → ρ → m ((Bool × List α) × ρ)) :
    ∀ (xs accRev : List α) (r : ρ),
      ReductionDsl.foldML (m := m)
        (fun x (acc : (Bool × List α) × ρ) =>
          if acc.1.1 then pure ((true, x :: acc.1.2), acc.2)
          else stepFalse x acc.1.2 acc.2)
        ((true, accRev), r) xs = pure ((true, xs.reverseAux accRev), r)
  | [], accRev, r => rfl
  | x :: xs, accRev, r => by
    dsimp only [ReductionDsl.foldML, List.reverseAux]
    simp only [↓reduceIte, pure_bind]
    exact foldML_consume_true_qsub stepFalse xs (x :: accRev) r

private theorem RouterSubsumesR.liftP_eq {S₁ S₂ : Sig} {κ : Type} {G : OracleSpec.{0, 0} κ}
    {j : ℕ} {RespSimOk : (q : κ) → G.Range q → Prop}
    (I₂ : Iface S₂ (unifSpec + G)) (I₁ : Iface S₁ (unifSpec + multiSessSpec G))
    (hFwd₂ : ∀ n, I₂.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    (hFwd₁ : ∀ n, I₁.fwdU n = liftM (OracleSpec.query (spec := unifSpec + multiSessSpec G) (.inl n)))
    {α : Type} (p : ProbComp α) :
    RouterSubsumesR j RespSimOk (· = ·) (I₂.liftP p) (I₁.liftP p) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp only [Iface.liftP, simulateQ_pure]
    exact .ret rfl
  | query_bind n mx ih =>
    rw [Iface.liftP, simulateQ_bind, simulateQ_query, hFwd₂]
    conv_rhs => rw [Iface.liftP, simulateQ_bind, simulateQ_query, hFwd₁]
    exact .coin_l n _ _ fun u => .coin_r _ n _ u (ih u)

private theorem substNoQueryComp_routerSubsumes (qep qR B0 j : ℕ)
    (RespSimOk :
      (q : (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Domain) →
      (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Range q → Prop)
    {Γ Δ : List (Ty SigA)} {t : Ty SigA}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr OpsF Δ u)
    (c : Comp OpsF (fsaeadMultiAtomicIface ℓ Pt qep qR B0) Γ t)
    (hc : c.queries (fun _ => 1) (fun _ => 0) = 0)
    (ρ₁ : Env Γ) (ρ₂ : Env Δ)
    (hEnv : ∀ {u} (v : Var Γ u), (envMap v).eval ρ₂ = ρ₁.get v) :
    RouterSubsumesR j RespSimOk (· = ·)
      ((substNoQueryComp
        (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
        (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
        envMap c hc).eval ρ₂)
      (c.eval ρ₁) := by
  induction c generalizing Δ with
  | ret e =>
    dsimp only [substNoQueryComp, Comp.eval]
    exact .ret (substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv)
  | bind c k ihc ihk =>
    dsimp only [substNoQueryComp, Comp.eval]
    refine (ihc envMap (by simp [Comp.queries] at hc; omega) ρ₁ ρ₂ hEnv).bind fun a b hEq => ?_
    subst hEq
    exact ihk (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons a ρ₁) (.cons a ρ₂) fun
      | .zero => rfl
      | .succ w => (exprWk1_eval_qsub (envMap w) a ρ₂).trans (hEnv w)
  | ite b c d ihc ihd =>
    dsimp only [substNoQueryComp, Comp.eval]
    rw [substExpr_eval_qsub envMap b ρ₁ ρ₂ hEnv]
    split_ifs <;>
      [exact ihc envMap (by simp [Comp.queries] at hc; omega) ρ₁ ρ₂ hEnv;
       exact ihd envMap (by simp [Comp.queries] at hc; omega) ρ₁ ρ₂ hEnv]
  | caseOpt e n s ihn ihs =>
    dsimp only [substNoQueryComp, Comp.eval]
    rw [substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv]
    cases e.eval ρ₁ with
    | none => exact ihn envMap (by simp [Comp.queries] at hc; omega) ρ₁ ρ₂ hEnv
    | some x =>
      exact ihs (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons x ρ₁) (.cons x ρ₂) fun
        | .zero => rfl
        | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)
  | caseSum e l r ihl ihr =>
    dsimp only [substNoQueryComp, Comp.eval]
    rw [substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv]
    cases e.eval ρ₁ with
    | inl x =>
      exact ihl (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons x ρ₁) (.cons x ρ₂) fun
        | .zero => rfl
        | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)
    | inr y =>
      exact ihr (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons y ρ₁) (.cons y ρ₂) fun
        | .zero => rfl
        | .succ w => (exprWk1_eval_qsub (envMap w) y ρ₂).trans (hEnv w)
  | sample s e =>
    dsimp only [substNoQueryComp, Comp.eval, fsaeadMultiAtomicIface]
    exact RouterSubsumesR.liftP_eq IfaceF (fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (fun _ => rfl) (fun _ => rfl) _
  | query _ _ => exfalso; simp [Comp.queries] at hc
  | iter n e body ih =>
    cases n with
    | zero =>
      dsimp only [substNoQueryComp, Comp.eval, ReductionDsl.iterM]
      exact .ret (substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv)
    | succ n =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv]
      have hLoop : ∀ (m : ℕ) (a : _),
          RouterSubsumesR j RespSimOk (· = ·)
            (ReductionDsl.iterM (fun a' =>
              (substNoQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF) (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                (liftEnv1 envMap) body (by simp [Comp.queries] at hc; omega)).eval (.cons a' ρ₂)) m a)
            (ReductionDsl.iterM (fun a' => body.eval (.cons a' ρ₁)) m a) := by
        intro m; induction m with
        | zero => intro a; exact .ret rfl
        | succ m ihm =>
          intro a; dsimp only [ReductionDsl.iterM]
          exact (ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)
            (.cons a ρ₁) (.cons a ρ₂) fun
              | .zero => rfl
              | .succ w => (exprWk1_eval_qsub (envMap w) a ρ₂).trans (hEnv w)).bind
            fun a' b' hEq => by subst hEq; exact ihm a'
      exact hLoop (n + 1) (e.eval ρ₁)
  | foldM K l z f ih =>
    cases K with
    | zero =>
      dsimp only [substNoQueryComp, Comp.eval, List.take, ReductionDsl.foldML]
      exact .ret (substExpr_eval_qsub envMap z ρ₁ ρ₂ hEnv)
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv, substExpr_eval_qsub envMap z ρ₁ ρ₂ hEnv]
      have hLoop : ∀ (xs : List _) (acc : _),
          RouterSubsumesR j RespSimOk (· = ·)
            (ReductionDsl.foldML (fun x a' =>
              (substNoQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF) (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                (liftEnv2 envMap) f (by simp [Comp.queries] at hc; omega)).eval (.cons x (.cons a' ρ₂))) acc xs)
            (ReductionDsl.foldML (fun x a' => f.eval (.cons x (.cons a' ρ₁))) acc xs) := by
        intro xs; induction xs with
        | nil => intro acc; exact .ret rfl
        | cons x xs ihxs =>
          intro acc; dsimp only [ReductionDsl.foldML]
          exact (ih (liftEnv2 envMap) (by simp [Comp.queries] at hc; omega)
            (.cons x (.cons acc ρ₁)) (.cons x (.cons acc ρ₂)) fun
              | .zero => rfl
              | .succ .zero => rfl
              | .succ (.succ w) =>
                (exprWk1_eval_qsub _ x _).trans
                  ((exprWk1_eval_qsub (envMap w) acc ρ₂).trans (hEnv w))).bind
            fun a₁ a₂ hEq => by subst hEq; exact ihxs a₁
      exact hLoop ((l.eval ρ₁).take (K + 1)) (z.eval ρ₁)
  | findM K l p ih =>
    cases K with
    | zero =>
      dsimp only [substNoQueryComp, Comp.eval, List.take, ReductionDsl.findML]
      exact .ret rfl
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv]
      have hLoop : ∀ (xs : List _),
          RouterSubsumesR j RespSimOk (· = ·)
            (ReductionDsl.findML (fun x =>
              (substNoQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF) (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                (liftEnv1 envMap) p (by simp [Comp.queries] at hc; omega)).eval (.cons x ρ₂)) xs)
            (ReductionDsl.findML (fun x => p.eval (.cons x ρ₁)) xs) := by
        intro xs; induction xs with
        | nil => exact .ret rfl
        | cons x xs ihxs =>
          dsimp only [ReductionDsl.findML]
          refine (ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)
            (.cons x ρ₁) (.cons x ρ₂) fun
              | .zero => rfl
              | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)).bind fun b₁ b₂ hEq => ?_
          subst hEq
          cases b₁ with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ihxs
          | true => simp only [↓reduceIte]; exact .ret rfl
      exact hLoop ((l.eval ρ₁).take (K + 1))
  | anyM K l p ih =>
    cases K with
    | zero =>
      dsimp only [substNoQueryComp, Comp.eval, List.take, ReductionDsl.anyML]
      exact .ret rfl
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv]
      have hLoop : ∀ (xs : List _),
          RouterSubsumesR j RespSimOk (· = ·)
            (ReductionDsl.anyML (fun x =>
              (substNoQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF) (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                (liftEnv1 envMap) p (by simp [Comp.queries] at hc; omega)).eval (.cons x ρ₂)) xs)
            (ReductionDsl.anyML (fun x => p.eval (.cons x ρ₁)) xs) := by
        intro xs; induction xs with
        | nil => exact .ret rfl
        | cons x xs ihxs =>
          dsimp only [ReductionDsl.anyML]
          refine (ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)
            (.cons x ρ₁) (.cons x ρ₂) fun
              | .zero => rfl
              | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)).bind fun b₁ b₂ hEq => ?_
          subst hEq
          cases b₁ with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ihxs
          | true => simp only [↓reduceIte]; exact .ret rfl
      exact hLoop ((l.eval ρ₁).take (K + 1))
  | mapM K l f ih =>
    cases K with
    | zero =>
      dsimp only [substNoQueryComp, Comp.eval, List.take, ReductionDsl.mapML, Expr.eval]
      exact .ret rfl
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv]
      have hLoop : ∀ (xs : List _),
          RouterSubsumesR j RespSimOk (· = ·)
            (ReductionDsl.mapML (fun x =>
              (substNoQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF) (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                (liftEnv1 envMap) f (by simp [Comp.queries] at hc; omega)).eval (.cons x ρ₂)) xs)
            (ReductionDsl.mapML (fun x => f.eval (.cons x ρ₁)) xs) := by
        intro xs; induction xs with
        | nil => exact .ret rfl
        | cons x xs ihxs =>
          dsimp only [ReductionDsl.mapML]
          refine (ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)
            (.cons x ρ₁) (.cons x ρ₂) fun
              | .zero => rfl
              | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)).bind fun y₁ y₂ hEq => ?_
          subst hEq
          exact ihxs.bind fun ys₁ ys₂ hYs => by subst hYs; exact .ret rfl
      exact hLoop ((l.eval ρ₁).take (K + 1))
  | consumeFirstM K l p mk ih =>
    cases K with
    | zero =>
      dsimp only [substNoQueryComp, Comp.eval, List.take, ReductionDsl.consumeFirstML, Expr.eval]
      exact .ret rfl
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv]
      have hLoop : ∀ (xs : List _),
          RouterSubsumesR j RespSimOk (· = ·)
            (ReductionDsl.consumeFirstML
              (fun x =>
                (substNoQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF) (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                  (liftEnv1 envMap) p (by simp [Comp.queries] at hc; omega)).eval (.cons x ρ₂))
              (fun x => (substExpr (liftEnv1 envMap) mk).eval (.cons x ρ₂)) xs)
            (ReductionDsl.consumeFirstML (fun x => p.eval (.cons x ρ₁))
              (fun x => mk.eval (.cons x ρ₁)) xs) := by
        intro xs; induction xs with
        | nil => exact .ret rfl
        | cons x xs ihxs =>
          dsimp only [ReductionDsl.consumeFirstML]
          refine (ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)
            (.cons x ρ₁) (.cons x ρ₂) fun
              | .zero => rfl
              | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)).bind fun b₁ b₂ hEq => ?_
          subst hEq
          cases b₁ with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ihxs.bind fun r₁ r₂ hR => by subst hR; exact .ret rfl
          | true =>
            simp only [↓reduceIte]
            rw [substExpr_eval_qsub (liftEnv1 envMap) mk (.cons x ρ₁) (.cons x ρ₂) fun
              | .zero => rfl
              | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)]
            exact .ret rfl
      exact hLoop ((l.eval ρ₁).take (K + 1))

private theorem RouterSubsumesR.bind_pure_l {κ : Type} {G : OracleSpec.{0, 0} κ}
    {j : ℕ} {RespSimOk : (q : κ) → G.Range q → Prop}
    {α₁ β α₂ : Type} {Rel₁ : α₁ → β → Prop} {Rel₂ : α₂ → β → Prop}
    {oa₁ : OracleComp (unifSpec + G) α₁}
    {oa₂ : OracleComp (unifSpec + multiSessSpec G) β}
    {f : α₁ → α₂}
    (h : RouterSubsumesR j RespSimOk Rel₁ oa₁ oa₂)
    (hf : ∀ a b, Rel₁ a b → Rel₂ (f a) b) :
    RouterSubsumesR j RespSimOk Rel₂ (oa₁ >>= fun a => pure (f a)) oa₂ := by
  simpa only [bind_pure] using h.bind fun a b hab => .ret (hf a b hab)

private theorem RouterSubsumesR.mono_rel {κ : Type} {G : OracleSpec.{0, 0} κ}
    {j : ℕ} {RespSimOk : (q : κ) → G.Range q → Prop}
    {α β : Type} {Rel₁ Rel₂ : α → β → Prop}
    {oa₁ : OracleComp (unifSpec + G) α}
    {oa₂ : OracleComp (unifSpec + multiSessSpec G) β}
    (h : RouterSubsumesR j RespSimOk Rel₁ oa₁ oa₂)
    (himp : ∀ a b, Rel₁ a b → Rel₂ a b) :
    RouterSubsumesR j RespSimOk Rel₂ oa₁ oa₂ := by
  induction h with
  | ret hab => exact .ret (himp _ _ hab)
  | coin_l n _ _ _ ih => exact .coin_l n _ _ ih
  | coin_r _ n _ u _ ih => exact .coin_r _ n _ u ih
  | sess_eq q _ _ _ ih => exact .sess_eq q _ _ ih
  | sess_ne s hs q r hr _ _ _ ih => exact .sess_ne s hs q r hr _ _ ih

private theorem substQueryComp_routerSubsumes (qep qR B0 : ℕ)
    (j : ℕ)
    (RespSimOk :
      (q : (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Domain) →
      (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Range q → Prop)
    {rStTy : Ty SigA}
    (qImpl : (g : FSHdrTag) →
      Comp OpsF IfaceF
        [(fsaeadMultiAtomicIface ℓ Pt qep qR B0).dom g, rStTy]
        (.prod ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).cod g) rStTy))
    (hQuery : ∀ (g : FSHdrTag) (s : ℕ) (payload : ((IfaceF).dom (toFsTag g)).denote)
        (rSt : rStTy.denote),
      (s = j →
        (qImpl g).eval (.cons (s, payload) (.cons rSt .nil)) =
          ((IfaceF).dec (toFsTag g) payload <$>
            (liftM (OracleSpec.query (spec := unifSpec + _)
              ((IfaceF).enc (toFsTag g) payload)) : OracleComp _ _)) >>=
            fun v => pure (v, rSt)) ∧
      (s ≠ j →
        CoinOnly ((qImpl g).eval (.cons (s, payload) (.cons rSt .nil))) ∧
        ∀ p ∈ support ((qImpl g).eval (.cons (s, payload) (.cons rSt .nil))),
          RespSimOk (fsEncQuery_qsub ℓ Pt (toFsTag g) payload)
            (fsInvDec ℓ Pt (toFsTag g) (x := payload) p.1)))
    {Γ Δ : List (Ty SigA)} {t : Ty SigA}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr OpsF Δ u) (rExpr : Expr OpsF Δ rStTy)
    (c : Comp OpsF (fsaeadMultiAtomicIface ℓ Pt qep qR B0) Γ t)
    (ρ₁ : Env Γ) (ρ₂ : Env Δ)
    (hEnv : ∀ {u} (v : Var Γ u), (envMap v).eval ρ₂ = ρ₁.get v) :
    RouterSubsumesR j RespSimOk (fun vr v => vr.1 = v)
      ((substQueryComp
        (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
        (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
        qImpl envMap rExpr c).eval ρ₂)
      (c.eval ρ₁) := by
  induction c generalizing Δ with
  | ret e =>
    dsimp only [substQueryComp, Comp.eval, Expr.eval]
    exact .ret (substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv)
  | bind c k ihc ihk =>
    dsimp only [substQueryComp, Comp.eval]
    refine (ihc envMap rExpr ρ₁ ρ₂ hEnv).bind fun vr v hEq => ?_
    subst hEq
    exact ihk (liftEnvFst envMap) (.snd (.var .zero)) (.cons vr.1 ρ₁) (.cons vr ρ₂) fun
      | .zero => rfl
      | .succ w => (exprWk1_eval_qsub (envMap w) vr ρ₂).trans (hEnv w)
  | ite b c d ihc ihd =>
    dsimp only [substQueryComp, Comp.eval]
    rw [substExpr_eval_qsub envMap b ρ₁ ρ₂ hEnv]
    split_ifs <;> [exact ihc envMap rExpr ρ₁ ρ₂ hEnv; exact ihd envMap rExpr ρ₁ ρ₂ hEnv]
  | caseOpt e n s ihn ihs =>
    dsimp only [substQueryComp, Comp.eval]
    rw [substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv]
    cases e.eval ρ₁ with
    | none => exact ihn envMap rExpr ρ₁ ρ₂ hEnv
    | some x =>
      exact ihs (liftEnv1 envMap) (exprWk1 rExpr) (.cons x ρ₁) (.cons x ρ₂) fun
        | .zero => rfl
        | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)
  | caseSum e l r ihl ihr =>
    dsimp only [substQueryComp, Comp.eval]
    rw [substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv]
    cases e.eval ρ₁ with
    | inl x =>
      exact ihl (liftEnv1 envMap) (exprWk1 rExpr) (.cons x ρ₁) (.cons x ρ₂) fun
        | .zero => rfl
        | .succ w => (exprWk1_eval_qsub (envMap w) x ρ₂).trans (hEnv w)
    | inr y =>
      exact ihr (liftEnv1 envMap) (exprWk1 rExpr) (.cons y ρ₁) (.cons y ρ₂) fun
        | .zero => rfl
        | .succ w => (exprWk1_eval_qsub (envMap w) y ρ₂).trans (hEnv w)
  | sample s e =>
    dsimp only [substQueryComp, Comp.eval, Expr.eval, fsaeadMultiAtomicIface]
    simp only [exprWk1_eval_qsub rExpr _ ρ₂]
    exact RouterSubsumesR.liftP_align (IfaceF) (fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (fun _ => rfl) (fun _ => rfl) _ (rExpr.eval ρ₂)
  | query g e =>
    dsimp only [substQueryComp, Comp.eval, Expr.eval]
    rw [pure_bind, substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv, callBinaryComp_eval_qsub]
    rcases hev : e.eval ρ₁ with ⟨s, payload⟩
    let G_fs := CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)
    have hRHS :
        (fsaeadMultiAtomicIface ℓ Pt qep qR B0).dec g (s, payload) <$>
          (liftM (OracleSpec.query
            ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).enc g (s, payload))) :
            OracleComp (unifSpec + multiSessSpec G_fs) _) =
        (liftM (OracleSpec.query (spec := unifSpec + multiSessSpec G_fs)
          (.inr ⟨s, fsEncQuery_qsub ℓ Pt (toFsTag g) payload⟩)) >>=
          fun r => pure ((IfaceF).dec (toFsTag g) payload
            (show OracleSpec.Range (unifSpec + G_fs) ((IfaceF).enc (toFsTag g) payload) from
              (fsaeadHeaderIface_enc_eq_qsub ℓ Pt (toFsTag g) payload).symm ▸ r))) := by
      cases g <;> (
        dsimp only [fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, fsEncQuery_qsub,
          multiSessSpec, G_fs, LCt]
        simp only [map_eq_bind_pure_comp, Function.comp_def]
        rfl)
    rw [hRHS]
    by_cases hs : s = j
    · subst hs
      rw [(hQuery g s payload (rExpr.eval ρ₂)).1 rfl]
      cases g <;> (
        dsimp only [fsaeadHeaderIface, toFsTag, fsEncQuery_qsub, G_fs, LCt]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        exact .sess_eq _ _ _ fun r => .ret rfl)
    · obtain ⟨hc, hok⟩ := (hQuery g s payload (rExpr.eval ρ₂)).2 hs
      refine RouterSubsumesR.of_coinOnly_l hc fun p hp => ?_
      exact .sess_ne s hs (fsEncQuery_qsub ℓ Pt (toFsTag g) payload)
        (fsInvDec ℓ Pt (toFsTag g) (x := payload) p.1) (hok p hp) _ _
        (.ret (fsaeadHeaderIface_dec_fsInvDec ℓ Pt (toFsTag g) payload p.1).symm)
  | iter n e body ih =>
    dsimp only [substQueryComp, Comp.eval, Expr.eval]
    rw [substExpr_eval_qsub envMap e ρ₁ ρ₂ hEnv]
    let tB := compRetTy body
    have hLoop : ∀ (m : ℕ) (a : tB.denote) (rVal : rStTy.denote),
        RouterSubsumesR j RespSimOk (fun vr v => vr.1 = v)
          (ReductionDsl.iterM
            (fun pr => (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
              (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
              qImpl (liftEnvFst envMap) (.snd (.var .zero)) body).eval (.cons pr ρ₂))
            m (a, rVal))
          (ReductionDsl.iterM (fun a' => body.eval (.cons a' ρ₁)) m a) := by
      intro m
      induction m with
      | zero => intro a rVal; exact .ret rfl
      | succ m ihm =>
        intro a rVal
        dsimp only [ReductionDsl.iterM]
        have hStep := ih (liftEnvFst envMap) (.snd (.var .zero))
          (.cons a ρ₁) (.cons (t := .prod tB rStTy) (a, rVal) ρ₂) fun
          | .zero => rfl
          | .succ w => (exprWk1_eval_qsub (a := .prod tB rStTy) (envMap w) (a, rVal) ρ₂).trans (hEnv w)
        exact hStep.bind fun vr v hEq => by subst hEq; exact ihm vr.1 vr.2
    exact hLoop n (e.eval ρ₁) (rExpr.eval ρ₂)
  | foldM K l z f ih =>
    dsimp only [substQueryComp, Comp.eval, Expr.eval]
    rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv, substExpr_eval_qsub envMap z ρ₁ ρ₂ hEnv]
    let tZ := compRetTy f
    let tX := listElemTy l
    have hLoop : ∀ (xs : List tX.denote) (acc : tZ.denote) (rVal : rStTy.denote),
        RouterSubsumesR j RespSimOk (fun vr v => vr.1 = v)
          (ReductionDsl.foldML
            (fun x pr => (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
              (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
              qImpl (liftEnvFold envMap) (.snd (.var (.succ .zero))) f).eval
              (.cons x (.cons pr ρ₂)))
            (acc, rVal) xs)
            (ReductionDsl.foldML (fun x a' => f.eval (.cons x (.cons a' ρ₁))) acc xs) := by
      intro xs
      induction xs with
      | nil => intro acc rVal; exact .ret rfl
      | cons x xs ihxs =>
        intro acc rVal
        dsimp only [ReductionDsl.foldML]
        have hStep := ih (liftEnvFold envMap) (.snd (.var (.succ .zero)))
          (.cons x (.cons acc ρ₁)) (.cons x (.cons (t := .prod tZ rStTy) (acc, rVal) ρ₂)) fun
          | .zero => rfl
          | .succ .zero => rfl
          | .succ (.succ w) =>
            (exprWk1_eval_qsub (a := tX) _ x _).trans
              ((exprWk1_eval_qsub (a := .prod tZ rStTy) (envMap w) (acc, rVal) ρ₂).trans (hEnv w))
        exact hStep.bind fun vr v hEq => by subst hEq; exact ihxs vr.1 vr.2
    exact hLoop ((l.eval ρ₁).take K) (z.eval ρ₁) (rExpr.eval ρ₂)
  | findM K l p ih =>
    cases K with
    | zero =>
      dsimp only [substQueryComp, Comp.eval, List.take, ReductionDsl.findML, Expr.eval]
      exact .ret rfl
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · dsimp only [Comp.eval, Expr.eval]
        exact (substNoQueryComp_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j RespSimOk
          envMap _ hc0 ρ₁ ρ₂ hEnv).bind_pure_l fun v₁ v₂ hEq => by
            dsimp only [env_get_zero]; exact hEq
      · let stepNone := fun (x : (listElemTy l).denote) (rVal : rStTy.denote) =>
          (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
            (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
            qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p).eval
            (.cons x (.cons (t := .prod (.opt (listElemTy l)) rStTy) (none, rVal) ρ₂)) >>= fun br =>
            pure ((if br.1 then some x else none), br.2)
        have hStepEq :
            (fun (x : (listElemTy l).denote) (acc : Option (listElemTy l).denote × rStTy.denote) =>
              (Comp.caseOpt (.fst (.var (.succ .zero)))
                (.bind
                  (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
                    (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                    qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p)
                  (.ret (.pair
                    (.ite (.fst (.var .zero)) (.some (.var (.succ .zero))) .none)
                    (.snd (.var .zero)))))
                (.ret (.var (.succ (.succ .zero))))).eval
                (.cons x (.cons (t := .prod (.opt (listElemTy l)) rStTy) acc ρ₂))) =
            (fun (x : (listElemTy l).denote) (acc : Option (listElemTy l).denote × rStTy.denote) => match acc.1 with
              | none => stepNone x acc.2
              | some _ => pure acc) := by
          funext x ⟨opt, rVal⟩
          cases opt <;> rfl
        dsimp -zeta only [Comp.eval, Expr.eval] at hStepEq ⊢
        rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv, hStepEq]
        have hLoop : ∀ (xs : List (listElemTy l).denote) (rVal : rStTy.denote),
            RouterSubsumesR j RespSimOk (fun vr v => vr.1 = v)
              (ReductionDsl.foldML
                (fun (x : (listElemTy l).denote) (acc : Option (listElemTy l).denote × rStTy.denote) => match acc.1 with
                  | none => stepNone x acc.2
                  | some _ => pure acc)
                (none, rVal) xs)
              (ReductionDsl.findML (fun x => p.eval (.cons x ρ₁)) xs) := by
          intro xs
          induction xs with
          | nil => intro rVal; exact .ret rfl
          | cons x xs ihxs =>
            intro rVal
            have hSN : stepNone x rVal =
                ((substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
                  (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                  qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p).eval
                  (.cons x (.cons (t := .prod (.opt (listElemTy l)) rStTy) (none, rVal) ρ₂)) >>= fun br =>
                  pure ((if br.1 then some x else none), br.2)) := rfl
            dsimp -zeta only [ReductionDsl.foldML, ReductionDsl.findML]
            rw [hSN]
            have hP := ih (liftEnvPred2 envMap) (.snd (.var (.succ .zero)))
              (.cons x ρ₁) (.cons x (.cons (t := .prod (.opt (listElemTy l)) rStTy) (none, rVal) ρ₂)) fun
              | .zero => rfl
              | .succ w =>
                (exprWk1_eval_qsub (a := listElemTy l) _ x _).trans
                  ((exprWk1_eval_qsub (a := .prod (.opt (listElemTy l)) rStTy) (envMap w) (none, rVal) ρ₂).trans (hEnv w))
            rw [bind_assoc]
            refine hP.bind fun br b hEq => ?_
            subst hEq
            cases br.1 with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
              exact ihxs br.2
            | true =>
              simp only [↓reduceIte, pure_bind]
              have hSome : ∀ (ys : List (listElemTy l).denote) (r : rStTy.denote),
                  ReductionDsl.foldML
                    (fun (z : (listElemTy l).denote) (acc : Option (listElemTy l).denote × rStTy.denote) =>
                      match acc.1 with
                      | none => stepNone z acc.2
                      | some _ => pure acc)
                    (some x, r) ys = pure (some x, r) := by
                intro ys
                induction ys with
                | nil => intro r; rfl
                | cons _ ys ihy =>
                  intro r
                  dsimp only [ReductionDsl.foldML]
                  rw [pure_bind]
                  exact ihy r
              rw [hSome xs br.2]
              exact .ret rfl
        exact hLoop ((l.eval ρ₁).take (K + 1)) (rExpr.eval ρ₂)
  | anyM K l p ih =>
    cases K with
    | zero =>
      dsimp only [substQueryComp, Comp.eval, List.take, ReductionDsl.anyML, Expr.eval]
      exact .ret rfl
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · dsimp only [Comp.eval, Expr.eval]
        exact (substNoQueryComp_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j RespSimOk
          envMap _ hc0 ρ₁ ρ₂ hEnv).bind_pure_l fun v₁ v₂ hEq => by
            dsimp only [env_get_zero]; exact hEq
      · let stepFalse := fun (x : (listElemTy l).denote) (rVal : rStTy.denote) =>
          (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
            (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
            qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p).eval
            (.cons x (.cons (t := .prod .bool rStTy) (false, rVal) ρ₂))
        have hStepEq :
            (fun (x : (listElemTy l).denote) (acc : Bool × rStTy.denote) =>
              (Comp.ite (.fst (.var (.succ .zero)))
                (.ret (.var (.succ .zero)))
                (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
                  (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                  qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p)).eval
                (.cons x (.cons (t := .prod .bool rStTy) acc ρ₂))) =
            (fun (x : (listElemTy l).denote) (acc : Bool × rStTy.denote) =>
              if acc.1 then pure acc else stepFalse x acc.2) := by
          funext x ⟨b, rVal⟩
          cases b <;> rfl
        dsimp -zeta only [Comp.eval, Expr.eval] at hStepEq ⊢
        rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv, hStepEq]
        have hLoop : ∀ (xs : List (listElemTy l).denote) (rVal : rStTy.denote),
            RouterSubsumesR j RespSimOk (fun vr v => vr.1 = v)
              (ReductionDsl.foldML
                (fun (x : (listElemTy l).denote) (acc : Bool × rStTy.denote) =>
                  if acc.1 then pure acc else stepFalse x acc.2)
                (false, rVal) xs)
              (ReductionDsl.anyML (fun x => p.eval (.cons x ρ₁)) xs) := by
          intro xs
          induction xs with
          | nil => intro rVal; exact .ret rfl
          | cons x xs ihxs =>
            intro rVal
            have hSF : stepFalse x rVal =
                (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
                  (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                  qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p).eval
                  (.cons x (.cons (t := .prod .bool rStTy) (false, rVal) ρ₂)) := rfl
            dsimp -zeta only [ReductionDsl.foldML, ReductionDsl.anyML]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hSF]
            have hP := ih (liftEnvPred2 envMap) (.snd (.var (.succ .zero)))
              (.cons x ρ₁) (.cons x (.cons (t := .prod .bool rStTy) (false, rVal) ρ₂)) fun
              | .zero => rfl
              | .succ w =>
                (exprWk1_eval_qsub (a := listElemTy l) _ x _).trans
                  ((exprWk1_eval_qsub (a := .prod .bool rStTy) (envMap w) (false, rVal) ρ₂).trans (hEnv w))
            refine hP.bind fun ⟨b', rVal'⟩ b hEq => ?_
            subst hEq
            cases b' with
            | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ihxs rVal'
            | true => simp only [↓reduceIte, foldML_any_true_qsub]; exact .ret rfl
        exact hLoop ((l.eval ρ₁).take (K + 1)) (rExpr.eval ρ₂)
  | mapM K l f ih =>
    cases K with
    | zero =>
      dsimp only [substQueryComp, Comp.eval, List.take, ReductionDsl.mapML, Expr.eval]
      exact .ret rfl
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · dsimp only [Comp.eval, Expr.eval]
        exact (substNoQueryComp_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j RespSimOk
          envMap _ hc0 ρ₁ ρ₂ hEnv).bind_pure_l fun v₁ v₂ hEq => by
            dsimp only [env_get_zero]; exact hEq
      · dsimp only [Comp.eval, Expr.eval]
        rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv]
        let tX := listElemTy l
        let tY := compRetTy f
        have hLoop : ∀ (xs : List tX.denote) (accRev : List tY.denote) (rVal : rStTy.denote)
            (hlen : accRev.length + xs.length ≤ (K + 1)),
            RouterSubsumesR j RespSimOk (fun vr ys => vr.1 = accRev.reverse ++ ys)
              (ReductionDsl.foldML
                (fun (x : tX.denote) (acc : List tY.denote × rStTy.denote) =>
                  (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
                    (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                    qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) f).eval
                    (.cons x (.cons (t := .prod (.list tY) rStTy) acc ρ₂)) >>= fun yr =>
                  pure (yr.1 :: acc.1, yr.2))
                (accRev, rVal) xs >>= fun acc =>
                ReductionDsl.foldML (fun x ys => pure (x :: ys)) [] (acc.1.take (K + 1)) >>=
                  fun rev => pure (rev, acc.2))
              (ReductionDsl.mapML (fun x => f.eval (.cons x ρ₁)) xs) := by
          intro xs
          induction xs with
          | nil =>
            intro accRev rVal hlen
            dsimp only [ReductionDsl.foldML, ReductionDsl.mapML]
            rw [pure_bind, foldML_pure_cons_qsub, pure_bind, List.take_of_length_le (by omega)]
            refine .ret ?_
            dsimp only
            rw [List.append_nil]
            rfl
          | cons x xs ihxs =>
            intro accRev rVal hlen
            dsimp only [ReductionDsl.foldML, ReductionDsl.mapML]
            rw [bind_assoc, bind_assoc]
            have hF := ih (liftEnvPred2 envMap) (.snd (.var (.succ .zero)))
              (.cons x ρ₁) (.cons x (.cons (t := .prod (.list tY) rStTy) (accRev, rVal) ρ₂)) fun
              | .zero => rfl
              | .succ w =>
                (exprWk1_eval_qsub (a := tX) _ x _).trans
                  ((exprWk1_eval_qsub (a := .prod (.list tY) rStTy) (envMap w) (accRev, rVal) ρ₂).trans (hEnv w))
            refine hF.bind fun yr y hEq => ?_
            subst hEq
            rw [pure_bind]
            have hTail := ihxs (yr.1 :: accRev) yr.2 (by simp only [List.length_cons] at hlen ⊢; omega)
            have hB := hTail.bind
              (Rel₂ := fun vr ys => vr.1 = accRev.reverse ++ ys)
              (k₁ := pure) (k₂ := fun ys => pure (yr.1 :: ys))
              fun vr ys hVr => .ret (by
                simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hVr
                exact hVr)
            simpa only [bind_pure] using hB
        have hTakeLen : ([] : List tY.denote).length + ((l.eval ρ₁).take (K + 1)).length ≤ (K + 1) := by
          simp only [List.length_nil, zero_add]; exact List.length_take_le (K + 1) _
        have h0 := hLoop ((l.eval ρ₁).take (K + 1)) [] (rExpr.eval ρ₂) hTakeLen
        exact h0.mono_rel fun _ _ hVr => hVr
  | consumeFirstM K l p mk ih =>
    cases K with
    | zero =>
      dsimp only [substQueryComp, Comp.eval, List.take, ReductionDsl.consumeFirstML, Expr.eval]
      exact .ret rfl
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · dsimp only [Comp.eval, Expr.eval]
        exact (substNoQueryComp_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j RespSimOk
          envMap _ hc0 ρ₁ ρ₂ hEnv).bind_pure_l fun v₁ v₂ hEq => by
            dsimp only [env_get_zero]; exact hEq
      · let stepFalse := fun (x : (listElemTy l).denote) (accRev : List (listElemTy l).denote) (rVal : rStTy.denote) =>
          (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
            (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
            qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p).eval
            (.cons x (.cons (t := .prod (.prod .bool (.list (listElemTy l))) rStTy) ((false, accRev), rVal) ρ₂)) >>= fun br =>
          if br.1 then
            pure ((true, mk.eval (.cons x ρ₁) :: accRev), br.2)
          else
            pure ((false, x :: accRev), br.2)
        have hStepEq :
            (fun (x : (listElemTy l).denote) (acc : (Bool × List (listElemTy l).denote) × rStTy.denote) =>
              (Comp.ite (.fst (.fst (.var (.succ .zero))))
                (.ret (.pair
                  (.pair (.bool true) (.cons (.var .zero) (.snd (.fst (.var (.succ .zero))))))
                  (.snd (.var (.succ .zero)))))
                (.bind
                  (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
                    (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                    qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p)
                  (.ite (.fst (.var .zero))
                    (.ret (.pair
                      (.pair (.bool true)
                        (.cons (substExpr (liftEnvMk3 envMap) mk)
                          (.snd (.fst (.var (.succ (.succ .zero)))))))
                      (.snd (.var .zero))))
                    (.ret (.pair
                      (.pair (.bool false)
                        (.cons (.var (.succ .zero)) (.snd (.fst (.var (.succ (.succ .zero)))))))
                      (.snd (.var .zero))))))).eval
                (.cons x (.cons (t := .prod (.prod .bool (.list (listElemTy l))) rStTy) acc ρ₂))) =
            (fun (x : (listElemTy l).denote) (acc : (Bool × List (listElemTy l).denote) × rStTy.denote) =>
              if acc.1.1 then pure ((true, x :: acc.1.2), acc.2)
              else stepFalse x acc.1.2 acc.2) := by
          funext x ⟨⟨found, accRev⟩, rVal⟩
          cases found with
          | true => rfl
          | false =>
            dsimp only [Comp.eval, Expr.eval, env_get_zero, env_get_succ, stepFalse]
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine bind_congr fun ⟨b, rVal'⟩ => ?_
            cases b with
            | false => rfl
            | true =>
              simp only [↓reduceIte]
              exact congrArg (fun v => pure ((true, v :: accRev), rVal'))
                (substExpr_eval_qsub (liftEnvMk3 envMap) mk (.cons x ρ₁)
                  (.cons (t := .prod .bool rStTy) (true, rVal')
                    (.cons x (.cons (t := .prod (.prod .bool (.list (listElemTy l))) rStTy) ((false, accRev), rVal) ρ₂))) fun
                  | .zero => rfl
                  | .succ w =>
                    (exprWk1_eval_qsub (a := .prod .bool rStTy) _ (true, rVal') _).trans
                      ((exprWk1_eval_qsub (a := listElemTy l) _ x _).trans
                        ((exprWk1_eval_qsub (a := .prod (.prod .bool (.list (listElemTy l))) rStTy) (envMap w)
                          ((false, accRev), rVal) ρ₂).trans (hEnv w))))
        dsimp -zeta only [Comp.eval, Expr.eval] at hStepEq ⊢
        rw [substExpr_eval_qsub envMap l ρ₁ ρ₂ hEnv, hStepEq]
        have hLoop : ∀ (xs : List (listElemTy l).denote) (accRev : List (listElemTy l).denote) (rVal : rStTy.denote)
            (hlen : accRev.length + xs.length ≤ (K + 1)),
            RouterSubsumesR j RespSimOk
              (fun vr (res : Bool × List (listElemTy l).denote) => vr.1 = (res.1, accRev.reverse ++ res.2))
              (ReductionDsl.foldML
                (fun (x : (listElemTy l).denote) (acc : (Bool × List (listElemTy l).denote) × rStTy.denote) =>
                  if acc.1.1 then pure ((true, x :: acc.1.2), acc.2)
                  else stepFalse x acc.1.2 acc.2)
                ((false, accRev), rVal) xs >>= fun acc =>
                ReductionDsl.foldML (fun x ys => pure (x :: ys)) [] (acc.1.2.take (K + 1)) >>=
                  fun rev => pure ((acc.1.1, rev), acc.2))
              (ReductionDsl.consumeFirstML (fun x => p.eval (.cons x ρ₁))
                (fun x => mk.eval (.cons x ρ₁)) xs) := by
          intro xs
          induction xs with
          | nil =>
            intro accRev rVal hlen
            dsimp -zeta only [ReductionDsl.foldML, ReductionDsl.consumeFirstML]
            rw [pure_bind, foldML_pure_cons_qsub, pure_bind, List.take_of_length_le (by omega)]
            refine .ret ?_
            dsimp only
            rw [List.append_nil]
            rfl
          | cons x xs ihxs =>
            intro accRev rVal hlen
            have hSF : stepFalse x accRev rVal =
                ((substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
                  (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
                  qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p).eval
                  (.cons x (.cons (t := .prod (.prod .bool (.list (listElemTy l))) rStTy) ((false, accRev), rVal) ρ₂)) >>= fun br =>
                if br.1 then
                  pure ((true, mk.eval (.cons x ρ₁) :: accRev), br.2)
                else
                  pure ((false, x :: accRev), br.2)) := rfl
            dsimp -zeta only [ReductionDsl.foldML, ReductionDsl.consumeFirstML]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hSF, bind_assoc, bind_assoc]
            have hP := ih (liftEnvPred2 envMap) (.snd (.var (.succ .zero)))
              (.cons x ρ₁)
              (.cons x (.cons (t := .prod (.prod .bool (.list (listElemTy l))) rStTy) ((false, accRev), rVal) ρ₂)) fun
              | .zero => rfl
              | .succ w =>
                (exprWk1_eval_qsub (a := listElemTy l) _ x _).trans
                  ((exprWk1_eval_qsub (a := .prod (.prod .bool (.list (listElemTy l))) rStTy) (envMap w)
                    ((false, accRev), rVal) ρ₂).trans (hEnv w))
            refine hP.bind fun br b hEq => ?_
            subst hEq
            cases br.1 with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
              have hTail := ihxs (x :: accRev) br.2 (by simp only [List.length_cons] at hlen ⊢; omega)
              have hB := hTail.bind
                (Rel₂ := fun vr (res : Bool × List (listElemTy l).denote) => vr.1 = (res.1, accRev.reverse ++ res.2))
                (k₁ := pure) (k₂ := fun r => pure (r.1, x :: r.2))
                fun vr res hVr => .ret (by
                  simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hVr
                  exact hVr)
              simpa only [bind_pure] using hB
            | true =>
              simp only [↓reduceIte, pure_bind, foldML_consume_true_qsub, foldML_pure_cons_qsub]
              have hRevLen : (xs.reverseAux (mk.eval (.cons x ρ₁) :: accRev)).length ≤ (K + 1) := by
                have hEqR := congrArg List.length (reverse_reverseAux_qsub xs (mk.eval (.cons x ρ₁) :: accRev))
                simp only [List.length_reverse, List.length_append, List.length_cons] at hEqR hlen
                omega
              rw [List.take_of_length_le hRevLen]
              refine .ret ?_
              have hRevEq : (xs.reverseAux (mk.eval (.cons x ρ₁) :: accRev)).reverseAux [] =
                  accRev.reverse ++ (mk.eval (.cons x ρ₁) :: xs) := by
                change (xs.reverseAux (mk.eval (.cons x ρ₁) :: accRev)).reverse = _
                rw [reverse_reverseAux_qsub]
                simp [List.reverse_cons, List.append_assoc]
              rw [hRevEq]
        have hTakeLen : ([] : List (listElemTy l).denote).length + ((l.eval ρ₁).take (K + 1)).length ≤ (K + 1) := by
          simp only [List.length_nil, zero_add]; exact List.length_take_le (K + 1) _
        have h0 := hLoop ((l.eval ρ₁).take (K + 1)) [] (rExpr.eval ρ₂) hTakeLen
        exact h0.mono_rel fun _ _ hVr => by simpa using hVr

private theorem substQueryRed_routerSubsumes (qep qR B0 j : ℕ)
    (RespSimOk :
      (q : (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Domain) →
      (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Range q → Prop)
    {κ : Type} {G_sm : OracleSpec.{0, 0} κ} {C_game : GameCodec SigA G_sm}
    {rIn aIn aOut out rStTy : Ty SigA}
    (rInit : Expr OpsF [rIn] rStTy)
    (qImpl : (g : FSHdrTag) →
      Comp OpsF IfaceF
        [(fsaeadMultiAtomicIface ℓ Pt qep qR B0).dom g, rStTy]
        (.prod ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).cod g) rStTy))
    (hQuery : ∀ (g : FSHdrTag) (s : ℕ) (payload : ((IfaceF).dom (toFsTag g)).denote)
        (rSt : rStTy.denote),
      (s = j →
        (qImpl g).eval (.cons (s, payload) (.cons rSt .nil)) =
          ((IfaceF).dec (toFsTag g) payload <$>
            (liftM (OracleSpec.query (spec := unifSpec + _)
              ((IfaceF).enc (toFsTag g) payload)) : OracleComp _ _)) >>=
            fun v => pure (v, rSt)) ∧
      (s ≠ j →
        CoinOnly ((qImpl g).eval (.cons (s, payload) (.cons rSt .nil))) ∧
        ∀ p ∈ support ((qImpl g).eval (.cons (s, payload) (.cons rSt .nil))),
          RespSimOk (fsEncQuery_qsub ℓ Pt (toFsTag g) payload)
            (fsInvDec ℓ Pt (toFsTag g) (x := payload) p.1)))
    (R : CostedReduction OpsF (fsaeadMultiAtomicIface ℓ Pt qep qR B0) G_sm C_game rIn aIn aOut out)
    (adv : aIn.denote → OracleComp (unifSpec + G_sm) aOut.denote) (x : rIn.denote) :
    RouterSubsumesR j RespSimOk Eq
      ((substQueryRed
        (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
        rInit (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e) qImpl R).eval adv x)
      (R.eval adv x) := by
  let hdl' : Comp OpsF IfaceF [R.σ.prod rStTy, C_game.Q] (C_game.R.prod (R.σ.prod rStTy)) :=
    (substQueryComp (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
      (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
      qImpl envFst2 (.snd (.var .zero)) R.handle).bind
      (.ret (.pair (.fst (.fst (.var .zero))) (.pair (.snd (.fst (.var .zero))) (.snd (.var .zero)))))
  have hSim : ∀ {α : Type} (oa : OracleComp (unifSpec + G_sm) α)
      (s : R.σ.denote) (rSt : rStTy.denote),
      RouterSubsumesR j RespSimOk (fun (bs' : α × (R.σ.denote × rStTy.denote)) (bs : α × R.σ.denote) =>
        bs'.1 = bs.1 ∧ bs'.2.1 = bs.2)
        ((simulateQ (ReductionDsl.handlerImpl (C := C_game) hdl') oa).run (s, rSt))
        ((simulateQ (ReductionDsl.handlerImpl (C := C_game) R.handle) oa).run s) := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure b =>
      intro s rSt
      simp only [simulateQ_pure, StateT.run_pure]
      exact .ret ⟨rfl, rfl⟩
    | query_bind q k ih =>
      intro s rSt
      rw [simulateQ_bind, simulateQ_bind]
      erw [simulateQ_query, simulateQ_query]
      cases q with
      | inl n =>
        let G_fs := CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256))
          (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)
        have hFwdM : (fsaeadMultiAtomicIface ℓ Pt qep qR B0).fwdU n =
            liftM (OracleSpec.query (spec := unifSpec + multiSessSpec G_fs) (.inl n)) := rfl
        simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map,
          ReductionDsl.handlerImpl,
          StateT.run_bind, stateT_run_lift, hFwdM, bind_assoc, pure_bind]
        exact .coin_l n _ _ fun u => .coin_r _ n _ u (ih u s rSt)
      | inr t =>
        simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map,
          ReductionDsl.handlerImpl, StateT.run_bind, StateT.run_mk, bind_assoc]
        dsimp only [hdl', Comp.eval, Expr.eval, env_get_zero]
        simp only [bind_assoc, pure_bind]
        have hH := substQueryComp_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j
          RespSimOk qImpl hQuery envFst2 (.snd (.var .zero)) R.handle
          (.cons s (.cons (C_game.qenc t) .nil))
          (.cons (t := .prod R.σ rStTy) (s, rSt) (.cons (C_game.qenc t) .nil))
          fun | .zero => rfl | .succ .zero => rfl
        refine hH.bind fun vr v hEq => ?_
        subst hEq
        exact ih (C_game.rdec t vr.1.1) vr.1.2 vr.2
  dsimp only [CostedReduction.eval, substQueryRed, CostedReduction.impl, Comp.eval, Expr.eval, env_get_zero]
  rw [bind_assoc]
  have hI := substQueryComp_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j
    RespSimOk qImpl hQuery envId1 rInit R.init (.cons x .nil) (.cons x .nil)
    fun | .zero => rfl
  refine hI.bind fun vr v hEq => ?_
  subst hEq
  simp only [pure_bind]
  refine (hSim (adv vr.1.1) vr.1.2 vr.2).bind fun bs' bs hBs => ?_
  rcases hBs with ⟨hB, hS⟩
  have hF := substQueryComp_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j
    RespSimOk qImpl hQuery envFst2 (.snd (.var .zero)) R.finish
    (.cons bs.2 (.cons bs.1 .nil))
    (.cons (t := .prod R.σ rStTy) bs'.2 (.cons bs'.1 .nil))
    fun | .zero => hS | .succ .zero => hB
  exact hF.bind_pure_l fun _ _ hOut => hOut

private theorem routerQueryMacro_hQuery_true (stage la : Bool) (j _qep qR _B0 : ℕ)
    (g : FSHdrTag) (s : ℕ) (payload : ((IfaceF).dom (toFsTag g)).denote)
    (rSt : (routerStTy ℓ Pt).denote) :
    (s = j →
      (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
        (.cons (s, payload) (.cons rSt .nil)) =
        ((IfaceF).dec (toFsTag g) payload <$>
          (liftM (OracleSpec.query (spec := unifSpec + _)
            ((IfaceF).enc (toFsTag g) payload)) : OracleComp _ _)) >>=
          fun v => pure (v, rSt)) ∧
    (s ≠ j →
      CoinOnly
        ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
          (.cons (s, payload) (.cons rSt .nil))) ∧
      ∀ p ∈ support
        ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
          (.cons (s, payload) (.cons rSt .nil))),
        (fun _ _ => True) (fsEncQuery_qsub ℓ Pt (toFsTag g) payload)
          (fsInvDec ℓ Pt (toFsTag g) (x := payload) p.1)) := by
  have hRealNoQ : ∀ jPosR mSlotR qSim,
      Comp.NoQuery (runLazyPubSess ℓ Pt C Dh encPt encT lam
        (initRealSessComp ℓ Pt C Dh encPt encT idOf lam)
        (realTrStep ℓ Pt C Dh encPt encT idOf lam jPosR mSlotR)
        (realChStep ℓ Pt C Dh encPt encT idOf lam jPosR mSlotR)
        (realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la)
        (realCrStep ℓ Pt C Dh encPt encT lam)
        (realDlStep ℓ Pt C Dh encPt encT idOf lam qSim jPosR mSlotR la)
        (realIjStep ℓ Pt C Dh encPt encT idOf lam qSim jPosR mSlotR la)
        (toFsTag g)) := by
    intro jPosR mSlotR qSim
    refine runLazyPubSess_noQuery ℓ Pt C Dh encPt encT lam ?_ ?_ ?_ ?_ ?_ ?_ ?_ (toFsTag g)
    · exact ⟨trivial, trivial⟩
    · exact liftFsCoinComp_noQuery ℓ Pt C Dh encPt encT lam _
    · exact liftFsCoinComp_noQuery ℓ Pt C Dh encPt encT lam _
    · exact liftFsCoinComp_noQuery ℓ Pt C Dh encPt encT lam _
    · trivial
    · exact liftFsCoinComp_noQuery ℓ Pt C Dh encPt encT lam _
    · exact liftFsCoinComp_noQuery ℓ Pt C Dh encPt encT lam _
  have hSlotNoQ : ∀ qSim N,
      Comp.NoQuery (runLazyPubSess ℓ Pt C Dh encPt encT lam
        (initSlotSessComp ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam))
        (slotTrStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
        (slotChStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
        (slotCsStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) qSim la)
        (slotCrStep ℓ Pt C Dh encPt encT lam)
        (slotDlStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
        (slotIjStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
        (toFsTag g)) := by
    intro qSim N
    refine runLazyPubSess_noQuery ℓ Pt C Dh encPt encT lam ?_ ?_ ?_ ?_ ?_ ?_ ?_ (toFsTag g)
    · exact ⟨trivial, trivial⟩
    · exact liftSlotHybStep_noQuery ℓ Pt C Dh encPt encT idOf lam stage qSim _
    · exact liftSlotHybStep_noQuery ℓ Pt C Dh encPt encT idOf lam stage qSim _
    · exact ⟨trivial, (liftFsCoinComp_noQuery ℓ Pt C Dh encPt encT lam _).renameM _, trivial⟩
    · trivial
    · exact liftSlotHybStep_noQuery ℓ Pt C Dh encPt encT idOf lam stage qSim _
    · exact liftSlotHybStep_noQuery ℓ Pt C Dh encPt encT idOf lam stage qSim _
  refine ⟨fun hs => ?_, fun hs => ⟨?_, fun _ _ => trivial⟩⟩
  · subst hs
    rw [routerQueryMacro, Comp.eval]
    have hCond : (Expr.eqN (O := OpsF) (.fst (.var .zero)) (.nat s)).eval (.cons (s, payload) (.cons rSt .nil)) = true := by
      simp [Expr.eval]
    simp only [hCond, ↓reduceIte]
    rfl
  · rw [routerQueryMacro, Comp.eval]
    have hCond : ¬ ((Expr.eqN (O := OpsF) (.fst (.var .zero)) (.nat j)).eval (.cons (s, payload) (.cons rSt .nil)) = true) := by
      simp [Expr.eval, hs]
    simp only [hCond]
    refine Comp.NoQuery.eval_coinOnly (I := IfaceF) (fun _ => rfl) ?_ _
    cases stage
    · exact ⟨⟨trivial, trivial, (hSlotNoQ _ _).renameM _, trivial⟩,
        ⟨trivial, trivial, (hRealNoQ _ _ _).renameM _, trivial⟩⟩
    · exact ⟨⟨trivial, trivial, (hRealNoQ _ _ _).renameM _, trivial⟩,
        ⟨trivial, trivial, (hSlotNoQ _ _).renameM _, trivial⟩⟩

/-- Transfer `IsQueryBoundP` across pointwise-equivalent query predicates `P` and `Q`. -/
private theorem isQueryBoundP_congr_local {ι α : Type} {spec : OracleSpec.{0, 0} ι}
    {oa : OracleComp spec α} {P Q : spec.Domain → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ t, P t ↔ Q t) {k : ℕ} (h : oa.IsQueryBoundP P k) :
    oa.IsQueryBoundP Q k := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure _ => trivial
  | query_bind t m ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨h.1.imp_left (mt (hPQ t).mpr), fun u => ?_⟩
    have h2 := h.2 u
    by_cases hPt : P t
    · have hQt : Q t := (hPQ t).mp hPt
      simp only [hPt, ↓reduceIte] at h2
      simp only [hQt, ↓reduceIte]
      exact ih u h2
    · have hQt : ¬ Q t := mt (hPQ t).mpr hPt
      simp only [hPt, ↓reduceIte] at h2
      simp only [hQt, ↓reduceIte]
      exact ih u h2

theorem compileFsMultiAtomic_isQueryBoundP_base (stage la : Bool) (j qep qR B0 : ℕ)
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
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (P : (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Domain → Bool)
    (k : ℕ)
    (hP : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, q⟩ => decide (s = j) && P q) = true) k) :
    ((compileFsMultiAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr q => P q) = true) k := by
  unfold compileFsMultiAtomic
  split_ifs with hG
  · have hMid := (compilePureAuxRed_fsMulti_querySubsumes ℓ Pt C Dh encPt encT idOf lam
      qep qR B0 R A).isQueryBoundP (fun _ => by simp) hP
    exact isQueryBoundP_congr_local (fun t => by cases t <;> rfl)
      ((substQueryRed_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j
        (fun _ _ => True) (initRouterStExpr ℓ Pt C Dh encPt encT lam)
        (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR)
        (routerQueryMacro_hQuery_true ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0)
        (compilePureAuxRed
          (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
          (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
        (fun _ => A) ()).isQueryBoundP P (isQueryBoundP_congr_local (fun t => by cases t <;> rfl) hMid))
  · exact (dummyRed_eval_coinOnly (O := OpsF) (I := IfaceF)
      (Cg := fig8SmCodec ℓ Pt) (rIn := .unit) (aIn := .unit) (aOut := .bool) (out := .bool)
      (fun _ => rfl) .unit (.inl .none) (.bool false) (fun _ => A) ()).isQueryBoundP
      (fun _ => Bool.false_ne_true) k

/-- Every `IsQueryBoundP` on session `j` of `R.eval (fun _ => A) ()` transfers directly to
`(compileFsMultiDFAtomic ... stage la j qep qR B0 R).eval (fun _ => A) ()` (unconditionally in `(ℓ, j, qep, qR)`). -/
theorem compileFsMultiDFAtomic_isQueryBoundP_base (stage la : Bool) (j qep qR B0 : ℕ)
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
    (P : (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)).Domain → Bool)
    (k : ℕ)
    (hP : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, q⟩ => decide (s = j) && P q) = true) k) :
    ((compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr q => P q) = true) k := by
  unfold compileFsMultiDFAtomic
  split_ifs with hG
  · have hMid := (compilePureAuxRed_fsMultiDF_querySubsumes ℓ Pt C Dh encPt encT idOf lam
      qep qR B0 R A).isQueryBoundP (fun _ => by simp) hP
    exact isQueryBoundP_congr_local (fun t => by cases t <;> rfl)
      ((substQueryRed_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j
        (fun _ _ => True) (initRouterStExpr ℓ Pt C Dh encPt encT lam)
        (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR)
        (routerQueryMacro_hQuery_true ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0)
        (compilePureAuxRed
          (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
          (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
        (fun _ => A) ()).isQueryBoundP P (isQueryBoundP_congr_local (fun t => by cases t <;> rfl) hMid))
  · exact (dummyRed_eval_coinOnly (O := OpsF) (I := IfaceF)
      (Cg := fig8SmCodecDF ℓ Pt) (rIn := .unit) (aIn := .unit) (aOut := .bool) (out := .bool)
      (fun _ => rfl) .unit (.inl .none) (.bool false) (fun _ => A) ()).isQueryBoundP
      (fun _ => Bool.false_ne_true) k

/-- Per-session `FSAEAD.MakesAtMostQueries ... qSess` (e.g. `qSess = 2 * q`) for
`compileFsMultiAtomic` from a session-`j` query bound on `R.eval`. -/
theorem compileFsMultiAtomic_makesAtMostQueries_base (stage la : Bool) (j qep qR B0 qSess : ℕ)
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
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hQ : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, _⟩ => decide (s = j)) = true) qSess) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((compileFsMultiAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
        (fun _ => A) ()) qSess := by
  rw [CryptoGames.FSAEAD.MakesAtMostQueries]
  have hQ' : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, _⟩ => decide (s = j) && true) = true) qSess := by
    simpa only [Bool.and_true] using hQ
  have h := compileFsMultiAtomic_isQueryBoundP_base ℓ Pt C Dh encPt encT idOf lam
    stage la j qep qR B0 R A (fun _ => true) qSess hQ'
  exact isQueryBoundP_congr_local (fun t => by cases t <;> simp) h

/-- Per-session `FSAEAD.MakesAtMostQueries ... qSess` (e.g. `qSess = 2 * q`) for
`compileFsMultiDFAtomic` from a session-`j` query bound on `R.eval`. -/
theorem compileFsMultiDFAtomic_makesAtMostQueries_base (stage la : Bool) (j qep qR B0 qSess : ℕ)
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
    (hQ : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, _⟩ => decide (s = j)) = true) qSess) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
        (fun _ => A) ()) qSess := by
  rw [CryptoGames.FSAEAD.MakesAtMostQueries]
  have hQ' : (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, _⟩ => decide (s = j) && true) = true) qSess := by
    simpa only [Bool.and_true] using hQ
  have h := compileFsMultiDFAtomic_isQueryBoundP_base ℓ Pt C Dh encPt encT idOf lam
    stage la j qep qR B0 R A (fun _ => true) qSess hQ'
  exact isQueryBoundP_congr_local (fun t => by cases t <;> simp) h

/-- Per-session `FSAEAD.EncMsgsOk` transfer for `compileFsMultiAtomic`. -/
theorem compileFsMultiAtomic_encMsgsOk_base (stage la : Bool) (j qep qR B0 : ℕ)
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
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
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
      ((compileFsMultiAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
        (fun _ => A) ()) := by
  have h := compileFsMultiAtomic_isQueryBoundP_base ℓ Pt C Dh encPt encT idOf lam
    stage la j qep qR B0 R A
    (fun q => CryptoGames.FSAEAD.encBadMsg
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (C := ℕ × LCt) Pmsg (.inr q))
    0 hOk
  exact isQueryBoundP_congr_local (fun t => by cases t <;> simp [CryptoGames.FSAEAD.encBadMsg]) h

/-- Per-session `FSAEAD.EncMsgsOk` transfer for `compileFsMultiDFAtomic`. -/
theorem compileFsMultiDFAtomic_encMsgsOk_base (stage la : Bool) (j qep qR B0 : ℕ)
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
  have h := compileFsMultiDFAtomic_isQueryBoundP_base ℓ Pt C Dh encPt encT idOf lam
    stage la j qep qR B0 R A
    (fun q => CryptoGames.FSAEAD.encBadMsg
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (C := ℕ × LCt) Pmsg (.inr q))
    0 hOk
  exact isQueryBoundP_congr_local (fun t => by cases t <;> simp [CryptoGames.FSAEAD.encBadMsg]) h

/-! ### Wire-Ciphertext Length Bound (`WireCtShort`) for Simulated Sessions (`s ≠ j`, `ℓ < 10 ^ 6`) -/

private def WireCtShort (w : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote) : Prop :=
  w.1.1.length ≤ 32 * (2 * (ℓ / 32) + 24)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem WireCtShort.lt_two_pow_32 (hℓ : ℓ < 10 ^ 6)
    {w : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote} (hw : WireCtShort ℓ Pt w) :
    w.1.1.length + 8 < 2 ^ 32 := by
  have hle : w.1.1.length ≤ 32 * (2 * (ℓ / 32) + 24) := hw
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem opSym_signalMsgEncode_len_le
    {Γ : List (Ty SigA)}
    (arg : Expr (atomicFsOps ℓ Pt C encT) Γ (ReductionDsl.AtomicSymOp.signalMsgEncode.dom ℓ Pt))
    (ρ : Env Γ) :
    ((Computational.Proofs.ReductionDsl.FsAtomicOps.opSym ℓ Pt C encT .signalMsgEncode arg).eval ρ).length ≤
      32 * (2 * (ℓ / 32) + 24) := by
  rw [Computational.Proofs.ReductionDsl.FsAtomicOps.opSym_eval]
  dsimp only [ReductionDsl.AtomicSymOp.eval]
  exact List.length_take_le _ _

private theorem expr_letE_eval_slot {S : Sig} {O : Ops S} {Γ : List (Ty S)} {a b : Ty S}
    (x : Expr O Γ a) (body : Expr O (a :: Γ) b) (ρ : Env Γ) :
    (Expr.letE x body).eval ρ = body.eval (.cons (x.eval ρ) ρ) := rfl

omit [SampleableType Pt] in
private theorem aeadKEncExpr_wireCtShort
    (ρ : Env [.prod ReductionDsl.derivedMsgKeysT (.prod slotAdT PlainT)]) :
    WireCtShort ℓ Pt
      ((Computational.Proofs.ReductionDsl.FsAtomicOps.aeadKEncExpr ℓ Pt C encT idOf).eval ρ) := by
  have hlet : ∀ (raw : Expr (atomicFsOps ℓ Pt C encT) _ (ReductionDsl.B 32))
      (n : Expr (atomicFsOps ℓ Pt C encT) _ .nat)
      (tag : Expr (atomicFsOps ℓ Pt C encT) _ ReductionDsl.U64)
      (salt : Expr (atomicFsOps ℓ Pt C encT) _ BV256),
      (raw.eval ρ).length ≤ 32 * (2 * (ℓ / 32) + 24) →
      WireCtShort ℓ Pt
        ((Expr.letE raw
          (.pair (.pair (Computational.Proofs.ReductionDsl.FsAtomicOps.opPure ℓ Pt C encT (.bytesTake 32)
            (.pair n (.var .zero))) tag) salt)).eval ρ) := by
    intro raw n tag salt hraw
    dsimp only [WireCtShort]
    rw [expr_letE_eval_slot]
    change ((Computational.Proofs.ReductionDsl.FsAtomicOps.opPure ℓ Pt C encT (.bytesTake 32)
      (.pair n (.var .zero))).eval (.cons (raw.eval ρ) ρ)).length ≤ _
    rw [Computational.Proofs.ReductionDsl.FsAtomicOps.opPure_eval]
    dsimp only [Expr.eval, env_get_zero, ReductionDsl.AtomicPureOp.eval]
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans hraw
  exact hlet _ _ _ _ (opSym_signalMsgEncode_len_le ℓ Pt C encT _ ρ)

omit [SampleableType Pt] in
private theorem aeadREncExpr_wireCtShort
    (ρ : Env [.prod BV256 (.prod slotAdT PlainT)]) :
    WireCtShort ℓ Pt
      ((Computational.Proofs.ReductionDsl.FsAtomicOps.aeadREncExpr ℓ Pt C encT idOf).eval ρ) := by
  dsimp only [Computational.Proofs.ReductionDsl.FsAtomicOps.aeadREncExpr, Expr.eval]
  rw [Computational.Proofs.ReductionDsl.FsAtomicOps.exprWkTop1_eval]
  exact aeadKEncExpr_wireCtShort ℓ Pt C encT idOf _

omit [SampleableType Pt] in
private theorem signalEncodeSerOnlyExpr_len_le
    (ρ : Env [.prod ReductionDsl.wireSignalHdrT (ReductionDsl.B 32)]) :
    ((Computational.Proofs.ReductionDsl.FsAtomicOps.signalEncodeSerOnlyExpr ℓ Pt C encT).eval ρ).length ≤
      32 * (2 * (ℓ / 32) + 24) := by
  have hlet : ∀ (raw : Expr (atomicFsOps ℓ Pt C encT) _ (ReductionDsl.B 32))
      (n : Expr (atomicFsOps ℓ Pt C encT) _ .nat),
      (raw.eval ρ).length ≤ 32 * (2 * (ℓ / 32) + 24) →
      ((Expr.letE raw
        (Computational.Proofs.ReductionDsl.FsAtomicOps.opPure ℓ Pt C encT (.bytesTake 32)
          (.pair n (.var .zero)))).eval ρ).length ≤ 32 * (2 * (ℓ / 32) + 24) := by
    intro raw n hraw
    rw [expr_letE_eval_slot, Computational.Proofs.ReductionDsl.FsAtomicOps.opPure_eval]
    dsimp only [Expr.eval, env_get_zero, ReductionDsl.AtomicPureOp.eval]
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans hraw
  exact hlet _ _ (opSym_signalMsgEncode_len_le ℓ Pt C encT _ ρ)

private def evalEnvMapQ {S : Sig} {O : Ops S} {Δ : List (Ty S)} :
    {Γ : List (Ty S)} → (∀ ⦃u⦄, Var Γ u → Expr O Δ u) → Env Δ → Env Γ
  | [], _, _ => .nil
  | _ :: _, envMap, ρ₂ =>
    .cons ((envMap .zero).eval ρ₂) (evalEnvMapQ (fun _ v => envMap (.succ v)) ρ₂)

private theorem get_evalEnvMapQ {S : Sig} {O : Ops S} {Δ : List (Ty S)} :
    ∀ {Γ : List (Ty S)} (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (ρ₂ : Env Δ)
      {u : Ty S} (v : Var Γ u),
      (evalEnvMapQ envMap ρ₂).get v = (envMap v).eval ρ₂
  | _ :: _, _, _, _, .zero => rfl
  | _ :: _, envMap, ρ₂, _, .succ v => get_evalEnvMapQ (fun _ w => envMap (.succ w)) ρ₂ v

private theorem substExpr_eval_any {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (e : Expr O Γ t) (ρ₂ : Env Δ) :
    (substExpr envMap e).eval ρ₂ = e.eval (evalEnvMapQ envMap ρ₂) :=
  substExpr_eval_qsub envMap e (evalEnvMapQ envMap ρ₂) ρ₂ fun v => (get_evalEnvMapQ envMap ρ₂ v).symm

private def evalRenEnvQ {S : Sig} {Δ : List (Ty S)} :
    {Γ : List (Ty S)} → (∀ ⦃u⦄, Var Γ u → Var Δ u) → Env Δ → Env Γ
  | [], _, _ => .nil
  | _ :: _, ren, ρ₂ => .cons (ρ₂.get (ren .zero)) (evalRenEnvQ (fun _ v => ren (.succ v)) ρ₂)

private theorem get_evalRenEnvQ {S : Sig} {Δ : List (Ty S)} :
    ∀ {Γ : List (Ty S)} (ren : ∀ ⦃u⦄, Var Γ u → Var Δ u) (ρ₂ : Env Δ)
      {u : Ty S} (v : Var Γ u),
      (evalRenEnvQ ren ρ₂).get v = ρ₂.get (ren v)
  | _ :: _, _, _, _, .zero => rfl
  | _ :: _, ren, ρ₂, _, .succ v => get_evalRenEnvQ (fun _ w => ren (.succ w)) ρ₂ v

private theorem exprRenameM_eval_any {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (ren : ∀ ⦃u⦄, Var Γ u → Var Δ u) (e : Expr O Γ t) (ρ₂ : Env Δ) :
    (e.renameM ren).eval ρ₂ = e.eval (evalRenEnvQ ren ρ₂) :=
  exprRenameM_eval ren e (evalRenEnvQ ren ρ₂) ρ₂ fun v => (get_evalRenEnvQ ren ρ₂ v).symm

private theorem compRenameM_eval_any {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (ren : ∀ ⦃u⦄, Var Γ u → Var Δ u) (c : Comp O I Γ t) (ρ₂ : Env Δ) :
    (c.renameM ren).eval ρ₂ = c.eval (evalRenEnvQ ren ρ₂) :=
  compRenameM_eval ren c (evalRenEnvQ ren ρ₂) ρ₂ fun v => (get_evalRenEnvQ ren ρ₂ v).symm

omit [SampleableType Pt] in
private theorem liftFsExpr_eval_qsub {Γ : List (Ty SigA)} {t : Ty SigA}
    (e : Expr (atomicFsOps ℓ Pt C encT) Γ t) (ρ : Env Γ) :
    (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam) e).eval ρ = e.eval ρ := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb
  | and _ _ iha ihb | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb
  | appendL _ _ _ iha ihb | tget _ _ iha ihb =>
    simp [liftFsExpr, Expr.eval, iha ρ, ihb ρ]
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | len _ iha | tconst _ iha =>
    simp [liftFsExpr, Expr.eval, iha ρ]
  | op o a iha =>
    change (atomicFsOps ℓ Pt C encT).eval o ((liftFsExpr a).eval ρ) =
      (atomicFsOps ℓ Pt C encT).eval o (a.eval ρ)
    rw [iha ρ]
  | tset _ _ _ ihm ihi iha =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihm ρ, ihi ρ, iha ρ]
  | ite _ _ _ ihc iha ihb =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihc ρ, iha ρ, ihb ρ]
  | caseOpt e _ _ ihe ihn ihs =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihe ρ]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e _ _ ihe ihl ihr =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihe ρ]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | letE e _ ihe ihb =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihe ρ]; exact ihb (.cons (e.eval ρ) ρ)
  | findB K l _ ihl ihp =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihl ρ]
    congr 1; funext x; exact ihp (.cons x ρ)
  | anyB K l _ ihl ihp =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihl ρ]
    congr 1; funext x; exact ihp (.cons x ρ)
  | mapB K l _ ihl ihf =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihl ρ]
    congr 1; funext x; exact ihf (.cons x ρ)
  | foldrB K l z _ ihl ihz ihf =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihl ρ, ihz ρ]
    congr 1; funext x; funext acc; exact ihf (.cons x (.cons acc ρ))

private theorem liftFsCoinComp_sampleIdeal_wireCtShort
    {Δ : List (Ty SigA)}
    (ren : ∀ ⦃u⦄, Var [slotAdT (ℓ := ℓ) (Pt := Pt)] u → Var Δ u)
    (ρ : Env Δ) {w : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote}
    (hw : w ∈ support ((liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam)
      ((Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp ℓ Pt C encT
        (fun b => Comp.sample (I := coinOnlyBaseIface ℓ Pt) (UniformSamplerTag.base b) .unit)).renameM
        ren)).eval ρ)) :
    WireCtShort ℓ Pt w := by
  dsimp only [Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp,
    Comp.renameM, liftFsCoinComp, Comp.eval] at hw
  rw [mem_support_bind_iff] at hw
  obtain ⟨_, _, hw⟩ := hw
  rw [mem_support_bind_iff] at hw
  obtain ⟨_, _, hw⟩ := hw
  rw [mem_support_pure_iff] at hw
  subst hw
  rw [liftFsExpr_eval_qsub, exprRenameM_eval_any]
  dsimp only [WireCtShort, Expr.eval]
  rw [Computational.Proofs.ReductionDsl.FsAtomicOps.exprWkTop1_eval]
  exact signalEncodeSerOnlyExpr_len_le ℓ Pt C encT _

private theorem substQueryComp_sampleIdeal_wireCtShort
    {Δ₁ Δ₂ : List (Ty SigA)} {rStTy : Ty SigA}
    (mapSamp : ∀ (s : (slotOtccaTargetIface ℓ Pt).smp.Samp) {Δ : List (Ty SigA)},
      Expr OpsF Δ ((slotOtccaTargetIface ℓ Pt).smp.sDom s) →
        Comp OpsF IfaceF Δ ((slotOtccaTargetIface ℓ Pt).smp.sTy s))
    (qImpl : (g : OTCCATag) →
      Comp OpsF IfaceF [(slotOtccaTargetIface ℓ Pt).dom g, rStTy]
        (.prod ((slotOtccaTargetIface ℓ Pt).cod g) rStTy))
    (envMap : ∀ ⦃u⦄, Var Δ₁ u → Expr OpsF Δ₂ u)
    (rExpr : Expr OpsF Δ₂ rStTy)
    (ren : ∀ ⦃u⦄, Var [slotAdT (ℓ := ℓ) (Pt := Pt)] u → Var Δ₁ u)
    (ρ : Env Δ₂) {p : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote × rStTy.denote}
    (hp : p ∈ support ((substQueryComp (I₁ := slotOtccaTargetIface ℓ Pt) (I₂ := IfaceF)
      mapSamp qImpl envMap rExpr
      (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam)
        ((Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp ℓ Pt C encT
          (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)).renameM
          ren))).eval ρ)) :
    WireCtShort ℓ Pt p.1 := by
  dsimp only [Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp,
    Comp.renameM, liftFsSlotComp, substQueryComp, Comp.eval] at hp
  rw [mem_support_bind_iff] at hp
  obtain ⟨_, _, hp⟩ := hp
  rw [mem_support_bind_iff] at hp
  obtain ⟨_, _, hp⟩ := hp
  rw [mem_support_pure_iff] at hp
  subst hp
  dsimp only [Expr.eval]
  rw [substExpr_eval_any, liftFsExpr_eval_qsub, exprRenameM_eval_any]
  dsimp only [WireCtShort, Expr.eval]
  rw [Computational.Proofs.ReductionDsl.FsAtomicOps.exprWkTop1_eval]
  exact signalEncodeSerOnlyExpr_len_le ℓ Pt C encT _

omit [SampleableType Pt] in
private theorem compileSlotEncKE_wireCtShort
    {Γ : List (Ty (CryptoGames.AEAD.Costed.saltWireSig Pt ℓ))}
    (mk : Expr (CryptoGames.AEAD.Costed.saltWireOps C clampedProtoSignalCodec ℓ encT idOf 1) Γ (.base .msgKey))
    (a : Expr (CryptoGames.AEAD.Costed.saltWireOps C clampedProtoSignalCodec ℓ encT idOf 1) Γ
      (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ))
    (m : Expr (CryptoGames.AEAD.Costed.saltWireOps C clampedProtoSignalCodec ℓ encT idOf 1) Γ (.base .plain))
    (ρ : Env (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureCtx (swBaseTy (Pt := Pt) (ℓ := ℓ)) Γ)) :
    WireCtShort ℓ Pt
      ((liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam)
        (compilePureExpr (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
          (CryptoGames.Ratchet.LibsignalInst.Costed.encKE C clampedProtoSignalCodec ℓ encT idOf 1 mk a m))).eval ρ) := by
  refine Eq.mp (congrArg (WireCtShort ℓ Pt)
    (liftFsExpr_eval_qsub ℓ Pt C Dh encPt encT lam _ ρ).symm) ?_
  dsimp only [CryptoGames.Ratchet.LibsignalInst.Costed.encKE, compilePureExpr,
    slotSwMacroBundle, Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, Expr.eval]
  exact Eq.mp
    (congrArg (WireCtShort ℓ Pt)
      (Expr.wkTop1_eval (Computational.Proofs.ReductionDsl.FsAtomicOps.aeadKEncExpr ℓ Pt C encT idOf)
        _ _).symm)
    (aeadKEncExpr_wireCtShort ℓ Pt C encT idOf _)

omit [SampleableType Pt] in
private theorem compilePrgAeadEncE_wireCtShort
    {Γ : List (Ty (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))}
    (x : Expr _ Γ (.prod (.base .rs) (.prod (.prod .nat (.base .ad)) (.base .msg))))
    (ρ : Env (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureCtx (hybBaseTy (Pt := Pt) (ℓ := ℓ)) Γ)) :
    WireCtShort ℓ Pt
      ((liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam)
        (compilePureExpr (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
          (CryptoGames.FSAEAD.Thm5.Costed.aeadEncE
            (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 x))).eval ρ) := by
  refine Eq.mp (congrArg (WireCtShort ℓ Pt)
    (liftFsExpr_eval_qsub ℓ Pt C Dh encPt encT lam _ ρ).symm) ?_
  dsimp only [CryptoGames.FSAEAD.Thm5.Costed.aeadEncE, compilePureExpr,
    prgZeroMacroBundle, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybOpMacro, Expr.eval]
  exact Eq.mp
    (congrArg (WireCtShort ℓ Pt)
      (Expr.wkTop1_eval (Computational.Proofs.ReductionDsl.FsAtomicOps.aeadREncExpr ℓ Pt C encT idOf)
        _ _).symm)
    (aeadREncExpr_wireCtShort ℓ Pt C encT idOf _)

omit [SampleableType Pt] in
private theorem compileMultiAeadEncE_wireCtShort
    (Γ : List (Ty (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)))
    {Δ : List (Ty SigA)}
    (envMap : ∀ ⦃u⦄,
      Var (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureCtx
        (multiMacroBundle (Pt := Pt) C ℓ encT idOf).baseTy Γ) u →
        Expr OpsF Δ u)
    (x : Expr _ Γ (.prod (.base .rs) (.prod (.prod .nat (.base .ad)) (.base .msg))))
    (ρ : Env Δ) :
    WireCtShort ℓ Pt
      ((substExpr envMap
        (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam)
          (compilePureExpr (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
            (CryptoGames.FSAEAD.Thm5.Costed.aeadEncE
              (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 x)))).eval ρ) := by
  rw [substExpr_eval_any, liftFsExpr_eval_qsub]
  dsimp only [CryptoGames.FSAEAD.Thm5.Costed.aeadEncE, compilePureExpr,
    multiMacroBundle, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybOpMacro, Expr.eval]
  exact Eq.mp
    (congrArg (WireCtShort ℓ Pt)
      (Expr.wkTop1_eval (Computational.Proofs.ReductionDsl.FsAtomicOps.aeadREncExpr ℓ Pt C encT idOf)
        _ _).symm)
    (aeadREncExpr_wireCtShort ℓ Pt C encT idOf _)

private theorem slotOtccaImpl_enc_wireCtShort (nf : Bool) (qSim : ℕ)
    (ρ : Env [(slotOtccaTargetIface ℓ Pt).dom .enc, .tbl (saltSlotStAtomTy ℓ Pt)])
    {p : ((slotOtccaTargetIface ℓ Pt).cod .enc).denote × (Ty.tbl (saltSlotStAtomTy ℓ Pt)).denote}
    (hp : p ∈ support ((slotOtccaImpl ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim .enc).eval ρ)) :
    ∀ w, p.1 = some w → WireCtShort ℓ Pt w := by
  dsimp only [slotOtccaImpl, slotSwMacroBundle, Comp.eval] at hp
  rw [pure_bind, mem_support_bind_iff] at hp
  obtain ⟨res, hres, hp⟩ := hp
  rw [mem_support_pure_iff] at hp
  subst hp
  rw [compRenameM_eval_any] at hres
  dsimp only [CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC,
    compilePureComp, liftNoQuerySlotComp, Comp.eval] at hres
  split_ifs at hres
  · rw [mem_support_pure_iff] at hres
    subst hres
    intro w hw
    simp [liftFsExpr, compilePureExpr, Expr.eval] at hw
  · simp only [pure_bind] at hres
    rw [mem_support_bind_iff] at hres
    obtain ⟨_, _, hres⟩ := hres
    simp only [liftFsExpr, compilePureExpr, Expr.eval] at hres
    subst hres
    intro w hw
    dsimp only [Expr.eval, liftFsExpr, compilePureExpr] at hw
    injection hw with hw'
    subst hw'
    exact compileSlotEncKE_wireCtShort ℓ Pt C Dh encPt encT idOf lam _ _ _ _

private theorem realEncIdx_wireCtShort (mSlot : ℕ)
    {Γ : List (Ty (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))}
    (ρ : Env (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureCtx (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (.prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg)))
        CryptoGames.FSAEAD.Thm5.Costed.hsTy :: Γ)))
    {ct : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote}
    (hct : ct ∈ support ((liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam)
      (compilePureComp (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
        (CryptoGames.FSAEAD.Thm5.Costed.encIdxBody
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot
          (fun a => Comp.sample
            (I := (Iface.withSamp
              (CryptoGames.PRG.Costed.prgIface
                (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                  (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
              (CryptoGames.OTCCA.Costed.idealSamplers
                (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
                (CryptoGames.FSAEAD.Costed.bt .ct)
                (lIdeal C clampedProtoSignalCodec ℓ encT) 1)).withSamp _)
            (Sum.inl (Sum.inr ())) a)
          (some fun x => Comp.sample
            (I := (Iface.withSamp
              (CryptoGames.PRG.Costed.prgIface
                (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                  (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
              (CryptoGames.OTCCA.Costed.idealSamplers
                (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
                (CryptoGames.FSAEAD.Costed.bt .ct)
                (lIdeal C clampedProtoSignalCodec ℓ encT) 1)).withSamp _)
            (Sum.inl (Sum.inr ())) x.fst)))).eval ρ)) :
    WireCtShort ℓ Pt ct := by
  dsimp only [CryptoGames.FSAEAD.Thm5.Costed.encIdxBody, prgZeroMacroBundle,
    compilePureComp, liftFsCoinComp, Comp.eval] at hct
  split_ifs at hct
  · try rw [pure_bind] at hct
    exact liftFsCoinComp_sampleIdeal_wireCtShort ℓ Pt C Dh encPt encT lam _ _ hct
  · try rw [pure_bind] at hct
    exact liftFsCoinComp_sampleIdeal_wireCtShort ℓ Pt C Dh encPt encT lam _ _ hct
  · split at hct
    · try rw [pure_bind] at hct
      exact liftFsCoinComp_sampleIdeal_wireCtShort ℓ Pt C Dh encPt encT lam _ _ hct
    · obtain rfl := ((mem_support_pure_iff _ _).mp hct).symm
      exact compilePrgAeadEncE_wireCtShort ℓ Pt C Dh encPt encT idOf lam _ _

private theorem mem_support_compRenameM_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    {ren : ∀ ⦃u⦄, Var Γ u → Var Δ u} {c : Comp O I Γ t} {ρ₂ : Env Δ} {x : t.denote}
    (hx : x ∈ support ((c.renameM ren).eval ρ₂)) :
    x ∈ support (c.eval (evalRenEnvQ ren ρ₂)) := by
  rwa [compRenameM_eval_any] at hx

section SlotEncIdxWireShortIrred

attribute [local irreducible] slotOtccaImpl

private theorem slotEncIdx_wireCtShort (nf : Bool) (qSim mSlot : ℕ)
    (Γ : List (Ty (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)))
    {Δ : List (Ty SigA)}
    {envMap : ∀ ⦃u⦄,
      Var (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureCtx
        (multiMacroBundle (Pt := Pt) C ℓ encT idOf).baseTy
        (.prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg)))
          CryptoGames.FSAEAD.Thm5.Costed.hsTy :: Γ)) u →
        Expr OpsF Δ u}
    {rExpr : Expr OpsF Δ (.tbl (saltSlotStAtomTy ℓ Pt))}
    {ρ : Env Δ}
    {p : ((wireSaltCtT (ℓ := ℓ) (Pt := Pt)).prod (.tbl (saltSlotStAtomTy ℓ Pt))).denote}
    (hp : p ∈ support ((substQueryComp
      (I₁ := slotOtccaTargetIface ℓ Pt) (I₂ := IfaceF)
      (fun s {_} e => liftBaseSamp s e)
      (slotOtccaImpl ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
      envMap rExpr
      (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam)
        (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
          (CryptoGames.FSAEAD.Thm5.Costed.encIdxBody
            (I := (CryptoGames.OTCCA.Costed.otccaIface
              (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
              (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
              (CryptoGames.FSAEAD.Costed.bt .msg)
              (CryptoGames.FSAEAD.Costed.bt .ct)
              (lIdeal C clampedProtoSignalCodec ℓ encT) 1).withSamp
              (ReductionDsl.unifSamplers
                (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                  (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
                CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)))
            (Γ := Γ)
            (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1 mSlot
            (fun a => Comp.sample
              (I := (CryptoGames.OTCCA.Costed.otccaIface
                (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                  (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
                (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
                (CryptoGames.FSAEAD.Costed.bt .msg)
                (CryptoGames.FSAEAD.Costed.bt .ct)
                (lIdeal C clampedProtoSignalCodec ℓ encT) 1).withSamp
                (ReductionDsl.unifSamplers
                  (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                    (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
                  CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)))
              (Sum.inl ()) a)
            (some (fun iam =>
              .bind (Comp.query
                (I := (CryptoGames.OTCCA.Costed.otccaIface
                  (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                    (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
                  (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
                  (CryptoGames.FSAEAD.Costed.bt .msg)
                  (CryptoGames.FSAEAD.Costed.bt .ct)
                  (lIdeal C clampedProtoSignalCodec ℓ encT) 1).withSamp
                  (ReductionDsl.unifSamplers
                    (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
                    CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)))
                CryptoGames.OTCCA.Costed.OtccaTag.enc iam)
                (.caseOpt (.var .zero)
                  (Comp.sample
                    (I := (CryptoGames.OTCCA.Costed.otccaIface
                      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
                      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
                      (CryptoGames.FSAEAD.Costed.bt .msg)
                      (CryptoGames.FSAEAD.Costed.bt .ct)
                      (lIdeal C clampedProtoSignalCodec ℓ encT) 1).withSamp
                      (ReductionDsl.unifSamplers
                        (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
                          (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
                        CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)))
                    (Sum.inl ()) (.fst (exprWk1 iam)))
                  (.ret (.var .zero))))))))).eval ρ)) :
    WireCtShort ℓ Pt p.1 := by
  dsimp only [CryptoGames.FSAEAD.Thm5.Costed.encIdxBody,
    compilePureComp, liftFsSlotComp, substQueryComp, Comp.eval] at hp
  split_ifs at hp
  · dsimp only [multiMacroBundle] at hp
    rw [pure_bind] at hp
    exact substQueryComp_sampleIdeal_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ hp
  · dsimp only [multiMacroBundle, Computational.Proofs.ReductionDsl.FsAtomicMacros.compWkTop1,
      Comp.renameM, callBinaryComp, liftFsSlotComp, substQueryComp, Comp.eval] at hp
    simp only [pure_bind] at hp
    obtain ⟨⟨qOpt, rSt'⟩, hqRes, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
    have hqShort := slotOtccaImpl_enc_wireCtShort ℓ Pt C Dh encPt encT idOf lam nf qSim _
      (mem_support_compRenameM_eval hqRes)
    dsimp only [substExpr, liftEnv1, liftEnvFst, liftFsExpr, compilePureExpr,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureVar,
      Expr.eval, Env.get] at hp
    cases qOpt with
    | none =>
      exact substQueryComp_sampleIdeal_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ hp
    | some w =>
      obtain rfl := ((mem_support_pure_iff _ _).mp hp).symm
      exact hqShort w rfl
  · split at hp
    · dsimp only [multiMacroBundle] at hp
      rw [pure_bind] at hp
      exact substQueryComp_sampleIdeal_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ hp
    · obtain rfl := ((mem_support_pure_iff _ _).mp hp).symm
      dsimp only [Expr.eval]
      exact compileMultiAeadEncE_wireCtShort ℓ Pt C Dh encPt encT idOf lam
        (.base .rs :: .prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg)))
          CryptoGames.FSAEAD.Thm5.Costed.hsTy :: Γ)
        _ _ _

end SlotEncIdxWireShortIrred

section StepWireShortIrred

attribute [local irreducible]
  CryptoGames.FSAEAD.Thm5.Costed.genUpToC
  CryptoGames.FSAEAD.Thm5.Costed.encIdxBody

private theorem realTrStep_wireCtShort (jPos mSlot : ℕ)
    (ρ : Env [.prod fig8PubAdT PlainT, hybSessStTy ℓ Pt])
    {p : Option (lctT (ℓ := ℓ) (Pt := Pt)).denote × (hybSessStTy ℓ Pt).denote}
    (hp : p ∈ support ((realTrStep ℓ Pt C Dh encPt encT idOf lam jPos mSlot).eval ρ)) :
    ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2 := by
  dsimp only [realTrStep, CryptoGames.FSAEAD.Thm5.Costed.transmitBody,
    CryptoGames.FSAEAD.Thm5.Costed.callC, compilePureComp, liftFsCoinComp, Comp.eval] at hp
  rw [pure_bind] at hp
  split_ifs at hp
  · rw [mem_support_pure_iff] at hp
    subst hp
    intro cv hcv
    simp [liftFsExpr, compilePureExpr, Expr.eval] at hcv
  · simp only [pure_bind] at hp
    rw [mem_support_bind_iff] at hp
    obtain ⟨_, _, hp⟩ := hp
    rw [mem_support_bind_iff] at hp
    obtain ⟨ct, hct, hp⟩ := hp
    have hctShort := realEncIdx_wireCtShort ℓ Pt C Dh encPt encT idOf lam mSlot _ hct
    rw [mem_support_pure_iff] at hp
    subst hp
    intro cv hcv
    dsimp only [liftFsExpr, compilePureExpr, Expr.eval, Env.get,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureVar] at hcv
    injection hcv with hcv'
    subst hcv'
    exact hctShort

private theorem realChStep_wireCtShort (jPos mSlot : ℕ)
    (ρ : Env [.prod fig8PubAdT (.prod PlainT PlainT), hybSessStTy ℓ Pt])
    {p : Option (lctT (ℓ := ℓ) (Pt := Pt)).denote × (hybSessStTy ℓ Pt).denote}
    (hp : p ∈ support ((realChStep ℓ Pt C Dh encPt encT idOf lam jPos mSlot).eval ρ)) :
    ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2 := by
  dsimp only [realChStep, CryptoGames.FSAEAD.Thm5.Costed.challengeBody,
    CryptoGames.FSAEAD.Thm5.Costed.callC, compilePureComp, liftFsCoinComp, Comp.eval] at hp
  rw [pure_bind] at hp
  split_ifs at hp
  · rw [mem_support_pure_iff] at hp
    subst hp
    intro cv hcv
    simp [liftFsExpr, compilePureExpr, Expr.eval] at hcv
  · simp only [pure_bind] at hp
    rw [mem_support_bind_iff] at hp
    obtain ⟨_, _, hp⟩ := hp
    rw [mem_support_bind_iff] at hp
    obtain ⟨ct, hct, hp⟩ := hp
    have hctShort := realEncIdx_wireCtShort ℓ Pt C Dh encPt encT idOf lam mSlot _ hct
    rw [mem_support_pure_iff] at hp
    subst hp
    intro cv hcv
    dsimp only [liftFsExpr, compilePureExpr, Expr.eval, Env.get,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureVar] at hcv
    injection hcv with hcv'
    subst hcv'
    exact hctShort

private theorem slotTrStep_wireCtShort (nf : Bool) (qSim N : ℕ)
    (ρ : Env [.prod fig8PubAdT PlainT, slotSessStTy ℓ Pt])
    {p : Option (lctT (ℓ := ℓ) (Pt := Pt)).denote × (slotSessStTy ℓ Pt).denote}
    (hp : p ∈ support ((slotTrStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim N).eval ρ)) :
    ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2 := by
  dsimp only [slotTrStep, liftSlotHybStep, CryptoGames.FSAEAD.Thm5.Costed.transmitBody,
    CryptoGames.FSAEAD.Thm5.Costed.callC,
    compilePureComp, liftFsSlotComp, substQueryComp, Comp.eval] at hp
  rw [mem_support_bind_iff] at hp
  obtain ⟨res, hres, hp⟩ := hp
  rw [mem_support_pure_iff] at hp
  subst hp
  rw [pure_bind] at hres
  split_ifs at hres
  · rw [mem_support_pure_iff] at hres
    subst hres
    intro cv hcv
    simp [substExpr, liftFsExpr, compilePureExpr, Expr.eval] at hcv
  · simp only [pure_bind] at hres
    obtain ⟨_, _, hres⟩ := (mem_support_bind_iff _ _ _).mp hres
    obtain ⟨ctP, hctP, hres⟩ := (mem_support_bind_iff _ _ _).mp hres
    have hctShort := slotEncIdx_wireCtShort ℓ Pt C Dh encPt encT idOf lam nf qSim N
      [CryptoGames.FSAEAD.Thm5.Costed.stTy,
       .prod (.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg))
         CryptoGames.FSAEAD.Thm5.Costed.stTy,
       .prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      hctP
    obtain rfl := ((mem_support_pure_iff _ _).mp hres).symm
    intro cv hcv
    dsimp only [substExpr, liftEnvFst, liftFsExpr, compilePureExpr, Expr.eval, Env.get,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureVar] at hcv
    injection hcv with hcv'
    subst hcv'
    exact hctShort

private theorem slotChStep_wireCtShort (nf : Bool) (qSim N : ℕ)
    (ρ : Env [.prod fig8PubAdT (.prod PlainT PlainT), slotSessStTy ℓ Pt])
    {p : Option (lctT (ℓ := ℓ) (Pt := Pt)).denote × (slotSessStTy ℓ Pt).denote}
    (hp : p ∈ support ((slotChStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim N).eval ρ)) :
    ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2 := by
  dsimp only [slotChStep, liftSlotHybStep, CryptoGames.FSAEAD.Thm5.Costed.challengeBody,
    CryptoGames.FSAEAD.Thm5.Costed.callC,
    compilePureComp, liftFsSlotComp, substQueryComp, Comp.eval] at hp
  rw [mem_support_bind_iff] at hp
  obtain ⟨res, hres, hp⟩ := hp
  rw [mem_support_pure_iff] at hp
  subst hp
  rw [pure_bind] at hres
  split_ifs at hres
  · rw [mem_support_pure_iff] at hres
    subst hres
    intro cv hcv
    simp [substExpr, liftFsExpr, compilePureExpr, Expr.eval] at hcv
  · simp only [pure_bind] at hres
    obtain ⟨_, _, hres⟩ := (mem_support_bind_iff _ _ _).mp hres
    obtain ⟨ctP, hctP, hres⟩ := (mem_support_bind_iff _ _ _).mp hres
    have hctShort := slotEncIdx_wireCtShort ℓ Pt C Dh encPt encT idOf lam nf qSim N
      [CryptoGames.FSAEAD.Thm5.Costed.stTy,
       .prod (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
         (.prod (CryptoGames.FSAEAD.Costed.bt .msg) (CryptoGames.FSAEAD.Costed.bt .msg)))
         CryptoGames.FSAEAD.Thm5.Costed.stTy,
       .prod (CryptoGames.FSAEAD.Costed.bt .ad)
         (.prod (CryptoGames.FSAEAD.Costed.bt .msg) (CryptoGames.FSAEAD.Costed.bt .msg)),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      hctP
    obtain rfl := ((mem_support_pure_iff _ _).mp hres).symm
    intro cv hcv
    dsimp only [substExpr, liftEnvFst, liftFsExpr, compilePureExpr, Expr.eval, Env.get,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureVar] at hcv
    injection hcv with hcv'
    subst hcv'
    exact hctShort

end StepWireShortIrred

private theorem runLazyPubSess_tr_wireCtShort {sTy : Ty SigA}
    (mkInit : Comp OpsF IfaceF [] sTy)
    (trS : Comp OpsF IfaceF [.prod fig8PubAdT PlainT, sTy] (.prod (.opt lctT) sTy))
    (chS : Comp OpsF IfaceF [.prod fig8PubAdT (.prod PlainT PlainT), sTy] (.prod (.opt lctT) sTy))
    (csS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt fsSendStT) sTy))
    (crS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt (.prod fsSendStT fsRecvStT)) sTy))
    (dlS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy))
    (ijS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy))
    (htr : ∀ ρ (p : Option (lctT (ℓ := ℓ) (Pt := Pt)).denote × sTy.denote),
      p ∈ support (trS.eval ρ) → ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2)
    (ρ : Env [(IfaceF).dom .tr, .prod .bool (.opt sTy)])
    {p : ((IfaceF).cod .tr).denote × (Ty.prod .bool (.opt sTy)).denote}
    (hp : p ∈ support ((runLazyPubSess ℓ Pt C Dh encPt encT lam mkInit trS chS csS crS dlS ijS .tr).eval ρ)) :
    ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2 := by
  dsimp only [runLazyPubSess, Comp.eval] at hp
  rw [pure_bind, mem_support_bind_iff] at hp
  obtain ⟨_, _, hp⟩ := hp
  rw [pure_bind, mem_support_bind_iff] at hp
  obtain ⟨res, hres, hp⟩ := hp
  rw [compRenameM_eval_any] at hres
  rw [mem_support_pure_iff] at hp
  subst hp
  exact htr _ res hres

private theorem runLazyPubSess_ch_wireCtShort {sTy : Ty SigA}
    (mkInit : Comp OpsF IfaceF [] sTy)
    (trS : Comp OpsF IfaceF [.prod fig8PubAdT PlainT, sTy] (.prod (.opt lctT) sTy))
    (chS : Comp OpsF IfaceF [.prod fig8PubAdT (.prod PlainT PlainT), sTy] (.prod (.opt lctT) sTy))
    (csS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt fsSendStT) sTy))
    (crS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt (.prod fsSendStT fsRecvStT)) sTy))
    (dlS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy))
    (ijS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy))
    (hch : ∀ ρ (p : Option (lctT (ℓ := ℓ) (Pt := Pt)).denote × sTy.denote),
      p ∈ support (chS.eval ρ) → ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2)
    (ρ : Env [(IfaceF).dom .ch, .prod .bool (.opt sTy)])
    {p : ((IfaceF).cod .ch).denote × (Ty.prod .bool (.opt sTy)).denote}
    (hp : p ∈ support ((runLazyPubSess ℓ Pt C Dh encPt encT lam mkInit trS chS csS crS dlS ijS .ch).eval ρ)) :
    ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2 := by
  dsimp only [runLazyPubSess, Comp.eval] at hp
  rw [pure_bind, mem_support_bind_iff] at hp
  obtain ⟨_, _, hp⟩ := hp
  rw [pure_bind, mem_support_bind_iff] at hp
  obtain ⟨res, hres, hp⟩ := hp
  rw [compRenameM_eval_any] at hres
  rw [mem_support_pure_iff] at hp
  subst hp
  exact hch _ res hres

section RouterMacroShortIrred

attribute [local irreducible] runLazyPubSess

private theorem routerQueryMacro_hQuery_short (hℓ : ℓ < 10 ^ 6)
    (stage la : Bool) (j qep qR B0 : ℕ)
    (g : FSHdrTag) (s : ℕ) (payload : ((IfaceF).dom (toFsTag g)).denote)
    (rSt : (routerStTy ℓ Pt).denote) :
    (s = j →
      (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
        (.cons (s, payload) (.cons rSt .nil)) =
        ((IfaceF).dec (toFsTag g) payload <$>
          (liftM (OracleSpec.query (spec := unifSpec + _)
            ((IfaceF).enc (toFsTag g) payload)) : OracleComp _ _)) >>=
          fun v => pure (v, rSt)) ∧
    (s ≠ j →
      CoinOnly
        ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
          (.cons (s, payload) (.cons rSt .nil))) ∧
      ∀ p ∈ support
        ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
          (.cons (s, payload) (.cons rSt .nil))),
        CryptoGames.Ratchet.LibsignalInst.fsRespShort
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (.inr (fsEncQuery_qsub ℓ Pt (toFsTag g) payload))
          (fsInvDec ℓ Pt (toFsTag g) (x := payload) p.1)) := by
  have hBase := routerQueryMacro_hQuery_true ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 g s payload rSt
  refine ⟨hBase.1, fun hs => ⟨(hBase.2 hs).1, ?_⟩⟩
  cases g with
  | cs | cr | dl | ij => intro _ _; trivial
  | tr =>
    change ∀ p : Option (lctT (ℓ := ℓ) (Pt := Pt)).denote × (routerStTy ℓ Pt).denote,
      p ∈ support
        ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR .tr).eval
          (.cons (s, payload) (.cons rSt .nil))) →
      CryptoGames.Ratchet.LibsignalInst.fsRespShort
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (.inr (fsEncQuery_qsub ℓ Pt .tr payload))
        (fsInvDec ℓ Pt .tr (x := payload) p.1)
    intro p hp
    dsimp only [routerQueryMacro, toFsTag, Comp.eval, Expr.eval] at hp
    simp only [Env.get, hs, decide_false, Bool.false_eq_true, ↓reduceIte] at hp
    have hcvShort : ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2 := by
      cases stage with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Comp.eval, pure_bind] at hp
        split_ifs at hp <;>
          (obtain ⟨res, hres, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
           obtain rfl := ((mem_support_pure_iff _ _).mp hp).symm
           rw [compRenameM_eval_any] at hres
           dsimp only [Expr.eval, Env.get])
        · exact runLazyPubSess_tr_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ _
            (fun ρ' p' hp' => slotTrStep_wireCtShort ℓ Pt C Dh encPt encT idOf lam false _ _ ρ' hp')
            _ hres
        · exact runLazyPubSess_tr_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ _
            (fun ρ' p' hp' => realTrStep_wireCtShort ℓ Pt C Dh encPt encT idOf lam _ _ ρ' hp')
            _ hres
      | true =>
        simp only [↓reduceIte, Comp.eval, pure_bind] at hp
        split_ifs at hp <;>
          (obtain ⟨res, hres, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
           obtain rfl := ((mem_support_pure_iff _ _).mp hp).symm
           rw [compRenameM_eval_any] at hres
           dsimp only [Expr.eval, Env.get])
        · exact runLazyPubSess_tr_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ _
            (fun ρ' p' hp' => realTrStep_wireCtShort ℓ Pt C Dh encPt encT idOf lam _ _ ρ' hp')
            _ hres
        · exact runLazyPubSess_tr_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ _
            (fun ρ' p' hp' => slotTrStep_wireCtShort ℓ Pt C Dh encPt encT idOf lam true _ _ ρ' hp')
            _ hres
    intro ie hie
    dsimp only [fsInvDec] at hie
    rw [Option.map_eq_some_iff] at hie
    obtain ⟨cv, hcv, rfl⟩ := hie
    exact (hcvShort cv hcv).lt_two_pow_32 ℓ Pt hℓ
  | ch =>
    change ∀ p : Option (lctT (ℓ := ℓ) (Pt := Pt)).denote × (routerStTy ℓ Pt).denote,
      p ∈ support
        ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR .ch).eval
          (.cons (s, payload) (.cons rSt .nil))) →
      CryptoGames.Ratchet.LibsignalInst.fsRespShort
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (.inr (fsEncQuery_qsub ℓ Pt .ch payload))
        (fsInvDec ℓ Pt .ch (x := payload) p.1)
    intro p hp
    dsimp only [routerQueryMacro, toFsTag, Comp.eval, Expr.eval] at hp
    simp only [Env.get, hs, decide_false, Bool.false_eq_true, ↓reduceIte] at hp
    have hcvShort : ∀ cv, p.1 = some cv → WireCtShort ℓ Pt cv.2 := by
      cases stage with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Comp.eval, pure_bind] at hp
        split_ifs at hp <;>
          (obtain ⟨res, hres, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
           obtain rfl := ((mem_support_pure_iff _ _).mp hp).symm
           rw [compRenameM_eval_any] at hres
           dsimp only [Expr.eval, Env.get])
        · exact runLazyPubSess_ch_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ _
            (fun ρ' p' hp' => slotChStep_wireCtShort ℓ Pt C Dh encPt encT idOf lam false _ _ ρ' hp')
            _ hres
        · exact runLazyPubSess_ch_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ _
            (fun ρ' p' hp' => realChStep_wireCtShort ℓ Pt C Dh encPt encT idOf lam _ _ ρ' hp')
            _ hres
      | true =>
        simp only [↓reduceIte, Comp.eval, pure_bind] at hp
        split_ifs at hp <;>
          (obtain ⟨res, hres, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
           obtain rfl := ((mem_support_pure_iff _ _).mp hp).symm
           rw [compRenameM_eval_any] at hres
           dsimp only [Expr.eval, Env.get])
        · exact runLazyPubSess_ch_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ _
            (fun ρ' p' hp' => realChStep_wireCtShort ℓ Pt C Dh encPt encT idOf lam _ _ ρ' hp')
            _ hres
        · exact runLazyPubSess_ch_wireCtShort ℓ Pt C Dh encPt encT lam _ _ _ _ _ _ _
            (fun ρ' p' hp' => slotChStep_wireCtShort ℓ Pt C Dh encPt encT idOf lam true _ _ ρ' hp')
            _ hres
    intro ie hie
    dsimp only [fsInvDec] at hie
    rw [Option.map_eq_some_iff] at hie
    obtain ⟨cv, hcv, rfl⟩ := hie
    exact (hcvShort cv hcv).lt_two_pow_32 ℓ Pt hℓ

end RouterMacroShortIrred

private theorem querySubsumes_guardedSafePost {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    {RespOk : (t : (unifSpec + G).Domain) → (unifSpec + G).Range t → Prop}
    {Q : (unifSpec + G).Domain → Prop}
    {oa₁ oa₂ : OracleComp (unifSpec + G) α}
    (hsub : QuerySubsumes oa₁ oa₂)
    (hQu : ∀ n, ¬ Q (.inl n))
    (hRu : ∀ n u, RespOk (.inl n) u)
    (h₂ : CryptoGames.GuardedSafe.GuardedSafePost RespOk Q (fun _ => True) oa₂) :
    CryptoGames.GuardedSafe.GuardedSafePost RespOk Q (fun _ => True) oa₁ := by
  induction hsub with
  | ret _ => exact .pure trivial
  | coin_l n _ _ _ ih => exact .query_bind (hQu n) fun u _ => ih u h₂
  | coin_r _ n _ u _ ih =>
    exact ih ((guardedSafePost_inv_query_bind_local h₂).2 u (hRu n u))
  | game _ _ _ _ ih =>
    obtain ⟨hQt, hcont⟩ := guardedSafePost_inv_query_bind_local h₂
    exact .query_bind hQt fun r hr => ih r (hcont r hr)

/-- `GuardedFSInjectShort` transfer from `GuardedMultiInjectShort` on `R.eval` to `compileFsMultiAtomic`. -/
theorem compileFsMultiAtomic_guardedFSInjectShort_base (stage la : Bool) (j qep qR B0 : ℕ)
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
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hG : CryptoVerification.E2E.Signed.SessionWireQueries.GuardedMultiInjectShort
      (R.eval (fun _ => A) ())) :
    CryptoGames.Ratchet.LibsignalInst.GuardedFSInjectShort
      ((compileFsMultiAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
        (fun _ => A) ()) := by
  unfold CryptoGames.Ratchet.LibsignalInst.GuardedFSInjectShort compileFsMultiAtomic
  split_ifs with hG_guard
  · let R_aux := compilePureAuxRed
      (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R
    have hMid : CryptoVerification.E2E.Signed.SessionWireQueries.GuardedMultiInjectShort
        (R_aux.eval (fun _ => A) ()) :=
      querySubsumes_guardedSafePost
        (compilePureAuxRed_fsMulti_querySubsumes ℓ Pt C Dh encPt encT idOf lam qep qR B0 R A)
        (fun _ => not_false) (fun _ _ => trivial) hG
    exact (substQueryRed_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j
      (fun q r => CryptoGames.Ratchet.LibsignalInst.fsRespShort
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (.inr q) r)
      (initRouterStExpr ℓ Pt C Dh encPt encT lam)
      (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR)
      (routerQueryMacro_hQuery_short ℓ Pt C Dh encPt encT idOf lam hG_guard.1 stage la j qep qR B0)
      R_aux (fun _ => A) ()).guardedFSInjectShort hMid
  · exact CoinOnly.guardedSafePost (fun _ => not_false)
      (dummyRed_eval_coinOnly (O := OpsF) (I := IfaceF) (Cg := fig8SmCodec ℓ Pt)
        (rIn := .unit) (aOut := .bool)
        (fun _ => rfl) .unit (.inl .none) (.bool false) (fun _ => A) ())

/-- `GuardedFSInjectShort` transfer from `GuardedMultiInjectShort` on `R.eval` to `compileFsMultiDFAtomic`. -/
theorem compileFsMultiDFAtomic_guardedFSInjectShort_base (stage la : Bool) (j qep qR B0 : ℕ)
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
  unfold CryptoGames.Ratchet.LibsignalInst.GuardedFSInjectShort compileFsMultiDFAtomic
  split_ifs with hG_guard
  · let R_aux := compilePureAuxRed
      (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R
    have hMid : CryptoVerification.E2E.Signed.SessionWireQueries.GuardedMultiInjectShort
        (R_aux.eval (fun _ => A) ()) :=
      querySubsumes_guardedSafePost
        (compilePureAuxRed_fsMultiDF_querySubsumes ℓ Pt C Dh encPt encT idOf lam qep qR B0 R A)
        (fun _ => not_false) (fun _ _ => trivial) hG
    exact (substQueryRed_routerSubsumes ℓ Pt C Dh encPt encT lam qep qR B0 j
      (fun q r => CryptoGames.Ratchet.LibsignalInst.fsRespShort
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (.inr q) r)
      (initRouterStExpr ℓ Pt C Dh encPt encT lam)
      (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR)
      (routerQueryMacro_hQuery_short ℓ Pt C Dh encPt encT idOf lam hG_guard.1 stage la j qep qR B0)
      R_aux (fun _ => A) ()).guardedFSInjectShort hMid
  · exact CoinOnly.guardedSafePost (fun _ => not_false)
      (dummyRed_eval_coinOnly (O := OpsF) (I := IfaceF) (Cg := fig8SmCodecDF ℓ Pt)
        (rIn := .unit) (aOut := .bool)
        (fun _ => rfl) .unit (.inl .none) (.bool false) (fun _ => A) ())

end RouterDSL

end Computational.Proofs.SessionCostedFig8.BundlesMultiFsSlot

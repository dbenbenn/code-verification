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
public import Computational.Proofs.HeadlineV1.Stage2RouterHelpers -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.ReductionDsl.MacroLift
import Computational.Proofs.ReductionDsl.PureAuxMacroLift
import Computational.Proofs.ReductionDsl.Fig8Atomic
import Computational.Proofs.ReductionDsl.FsAtomicOps
import Computational.Proofs.ReductionDsl.FsAtomicMacros
import Computational.Proofs.ReductionDsl.FsAtomicBundles
import Computational.Proofs.ReductionDsl.FSAEAD.HybridCosted
import Computational.Proofs.ReductionDsl.FSAEAD.HybridInv
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedBase
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWireCosted
import Computational.Proofs.ReductionDsl.SM.Engine
import Computational.Proofs.E2E.SessionAuthQueries
import VCVio.OracleComp.EvalDist.Measure
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
import Computational.Specifications.Reductions.ReductionDsl.Core
import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs

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
open Computational.Proofs.ReductionDsl.FsAtomicMacros
  (mapPureEnv compilePureExpr_eval compilePureComp_coinSimEquiv
   salt32OfV_salt32V salt32V_salt32OfV wireSignalHdrOfV_wireSignalHdrV
   wireSaltCtOfV_wireSaltCtV wireSaltCtV_wireSaltCtOfV
   lctOfV_lctV lctV_lctOfV fig8PubAdOfV_fig8PubAdV fig8PubAdV_fig8PubAdOfV
   slotAdOfV_slotAdV fsSendStOfV_fsSendStV fsRecvStOfV_fsRecvStV fsRrDec_fsRrEnc)
open Computational.Proofs.ReductionDsl.FsAtomicOps (env_get_zero env_get_succ)
open ReductionDsl
  (AtomicSort AtomicBaseUnif atomicBaseSamplers unifSamplers
   salt32V salt32OfV wireSignalHdrV wireSignalHdrOfV
   wireSaltCtV wireSaltCtOfV fig8PubAdV fig8PubAdOfV
   slotAdV slotAdOfV)
open Computational.Proofs.ReductionDsl.FsAtomicBundles (hybToDen swToDen)

namespace Computational.Proofs.SessionCostedFig8.BundlesMultiFsEval

section RouterDSL

set_option linter.unusedSectionVars false

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

local notation "SigA" => (atomicSig ℓ Pt)
local notation "OpsF" => (atomicFig8Ops ℓ Pt C Dh encPt encT lam)
local notation "IfaceF" => (fsaeadHeaderIface ℓ Pt)

private theorem renEmpty_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I [] t) (ρ : Env Γ) :
    (c.renameM renEmpty).eval ρ = c.eval .nil :=
  c.renameM_eval (fun _ v => nomatch v)

private theorem renId1_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {a : Ty S} {Γ : List (Ty S)} {t : Ty S}
    (c : Comp O I [a] t) (x : a.denote) (ρ : Env Γ) :
    (c.renameM renId1).eval (.cons x ρ) = c.eval (.cons x .nil) :=
  c.renameM_eval (fun _ v => match v with | .zero => rfl)

private theorem renId2_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {a b : Ty S} {Γ : List (Ty S)} {t : Ty S}
    (c : Comp O I [a, b] t) (x : a.denote) (y : b.denote) (ρ : Env Γ) :
    (c.renameM renId2).eval (.cons x (.cons y ρ)) = c.eval (.cons x (.cons y .nil)) :=
  c.renameM_eval (fun _ v => match v with | .zero => rfl | .succ .zero => rfl)

private theorem renUnit2_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {a b : Ty S} {Γ : List (Ty S)} {t : Ty S}
    (c : Comp O I [.unit, a] t) (x : a.denote) (y : b.denote) (ρ : Env Γ) :
    (c.renameM renUnit2).eval (.cons x (.cons y (.cons () ρ))) =
      c.eval (.cons () (.cons x .nil)) :=
  c.renameM_eval (fun _ v => match v with | .zero => rfl | .succ .zero => rfl)

private theorem ensureSessInit_coinSimEquiv {sTy : Ty SigA} {σ : Type}
    (encS : σ → sTy.denote) (init : ProbComp σ)
    (mkInit : Comp OpsF IfaceF [] sTy)
    (hInit : CoinSimEquiv (IfaceF).fwdU (mkInit.eval .nil) ((IfaceF).liftP (encS <$> init)))
    (os : Option σ) :
    CoinSimEquiv (IfaceF).fwdU
      ((ensureSessInit ℓ Pt C Dh encPt encT lam mkInit).eval (.cons (os.map encS) .nil))
      ((IfaceF).liftP (encS <$> (match os with | some s => pure s | none => init))) := by
  cases os with
  | none =>
    dsimp only [ensureSessInit, Option.map, Comp.eval, Expr.eval, Env.get]
    rw [renEmpty_eval]
    exact hInit
  | some s =>
    dsimp only [ensureSessInit, Option.map, Comp.eval, Expr.eval, Env.get]
    rw [map_pure]
    exact coinSimEquiv_liftP_pure IfaceF (encS s)

omit [SampleableType Pt] in
private theorem mapRrWithPubExpr_eval {Γ : List (Ty SigA)}
    (optRrE : Expr OpsF Γ (.opt (fsRrT PlainT)))
    (pubE : Expr OpsF Γ lpubT) (ρ : Env Γ)
    (optRr : Option (CryptoGames.FSAEAD.ReceiveResult (Plain ℓ)))
    (p : LibsignalMsgPublicPart)
    (hrr : optRrE.eval ρ = optRr.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
    (hp : pubE.eval ρ = ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p) :
    (mapRrWithPubExpr ℓ Pt C Dh encPt encT lam optRrE pubE).eval ρ =
      (optRr.map (CryptoGames.FSAEAD.withPub p)).map
        (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := .prod lpubT PlainT)
          fun (p', m) => (ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p', m)) := by
  dsimp only [mapRrWithPubExpr, Expr.eval]
  rw [hrr]
  cases optRr with
  | none => rfl
  | some rr =>
    cases rr with
    | rejected => rfl
    | accepted i optM =>
      cases optM with
      | none => rfl
      | some m =>
        simp only [Option.map, ReductionDsl.fsRrEnc, CryptoGames.FSAEAD.withPub,
          Env.get, exprWk1_eval, hp, id_eq]

omit [DecidableEq Pt] [Zero Pt] in
private theorem pubRedImpl_lazyInit_tr {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT σ ProbComp))
    (hdr : Header Pt) (pv : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m : Plain ℓ)
    (endedPub : Bool) (os : Option σ) :
    (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
      (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl))
      ((CryptoGames.FSAEAD.pubRedImpl
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
        ((IfaceF).enc .tr (hdr, (pv, m)))).run endedPub)).run os =
      ((match os with | some s => pure s | none => init) >>= fun s0 =>
        (impl (.inl (.inl (.inl (.inl (.inl (
          (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv), m))))))).run s0 >>=
          fun r => pure ((r.1, endedPub), some r.2)) := by
  cases os <;>
    simp [fsaeadHeaderIface, CryptoGames.FSAEAD.pubRedImpl, CryptoGames.FSAEAD.transmitQuery,
      StateT.run_lift, map_eq_bind_pure_comp]

omit [DecidableEq Pt] [Zero Pt] in
private theorem pubRedImpl_lazyInit_ch {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT σ ProbComp))
    (hdr : Header Pt)
    (pv0 : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m0 : Plain ℓ)
    (pv1 : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m1 : Plain ℓ)
    (endedPub : Bool) (os : Option σ) :
    (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
      (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl))
      ((CryptoGames.FSAEAD.pubRedImpl
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
        ((IfaceF).enc .ch (hdr, ((pv0, m0), (pv1, m1))))).run endedPub)).run os =
      ((match os with | some s => pure s | none => init) >>= fun s0 =>
        (impl (.inl (.inl (.inl (.inl (.inr (
          (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0), m0, m1))))))).run s0 >>=
          fun r => pure ((r.1, endedPub), some r.2)) := by
  cases os <;>
    simp [fsaeadHeaderIface, CryptoGames.FSAEAD.pubRedImpl, CryptoGames.FSAEAD.challengeQuery,
      StateT.run_lift, map_eq_bind_pure_comp]

omit [DecidableEq Pt] [Zero Pt] in
private theorem pubRedImpl_lazyInit_cs {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT σ ProbComp))
    (endedPub : Bool) (os : Option σ) :
    (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
      (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl))
      ((CryptoGames.FSAEAD.pubRedImpl
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
        ((IfaceF).enc .cs ())).run endedPub)).run os =
      ((match os with | some s => pure s | none => init) >>= fun s0 =>
        (impl (.inl (.inl (.inl (.inr ()))))).run s0 >>=
          fun r => pure ((r.1, endedPub), some r.2)) := by
  cases os <;>
    simp [fsaeadHeaderIface, CryptoGames.FSAEAD.pubRedImpl, CryptoGames.FSAEAD.corruptSenderQuery,
      StateT.run_lift, map_eq_bind_pure_comp]

omit [DecidableEq Pt] [Zero Pt] in
private theorem pubRedImpl_lazyInit_cr {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT σ ProbComp))
    (endedPub : Bool) (os : Option σ) :
    (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
      (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl))
      ((CryptoGames.FSAEAD.pubRedImpl
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
        ((IfaceF).enc .cr ())).run endedPub)).run os =
      ((match os with | some s => pure s | none => init) >>= fun s0 =>
        (impl (.inl (.inl (.inr ())))).run s0 >>=
          fun r => pure ((r.1, if r.1.isSome then true else endedPub), some r.2)) := by
  cases os with
  | none =>
    simp only [fsaeadHeaderIface, CryptoGames.FSAEAD.pubRedImpl,
      CryptoGames.FSAEAD.corruptReceiverQuery, StateT.run_bind, StateT.run_lift]
    simp [map_eq_bind_pure_comp]
    refine bind_congr fun s0 => bind_congr fun ⟨r1, r2⟩ => ?_
    cases r1 <;> simp
  | some s =>
    simp only [fsaeadHeaderIface, CryptoGames.FSAEAD.pubRedImpl,
      CryptoGames.FSAEAD.corruptReceiverQuery, StateT.run_bind, StateT.run_lift]
    simp [map_eq_bind_pure_comp]
    refine bind_congr fun ⟨r1, r2⟩ => ?_
    cases r1 <;> simp

omit [DecidableEq Pt] [Zero Pt] in
private theorem pubRedImpl_lazyInit_dl_some {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT σ ProbComp))
    (hdr : Header Pt) (cv : (lctT (ℓ := ℓ) (Pt := Pt)).denote) (p : LibsignalMsgPublicPart)
    (hp : lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2 = some p)
    (endedPub : Bool) (os : Option σ) :
    (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
      (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl))
      ((CryptoGames.FSAEAD.pubRedImpl
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
        ((IfaceF).enc .dl (hdr, cv))).run endedPub)).run os =
      ((match os with | some s => pure s | none => init) >>= fun s0 =>
        (impl (.inl (.inr ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv)))).run s0 >>=
          fun r => pure ((r.1.map (CryptoGames.FSAEAD.withPub p), endedPub), some r.2)) := by
  cases os <;>
    simp [fsaeadHeaderIface, CryptoGames.FSAEAD.pubRedImpl, CryptoGames.FSAEAD.deliverQuery, hp,
      StateT.run_lift, map_eq_bind_pure_comp]

omit [DecidableEq Pt] [Zero Pt] in
private theorem pubRedImpl_lazyInit_ij_some {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT σ ProbComp))
    (hdr : Header Pt) (cv : (lctT (ℓ := ℓ) (Pt := Pt)).denote) (p : LibsignalMsgPublicPart)
    (hp : lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2 = some p)
    (endedPub : Bool) (os : Option σ) :
    (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
      (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl))
      ((CryptoGames.FSAEAD.pubRedImpl
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AD := Header Pt) (M := Plain ℓ)
        (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
        ((IfaceF).enc .ij (hdr, cv))).run endedPub)).run os =
      ((match os with | some s => pure s | none => init) >>= fun s0 =>
        (impl (.inr ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv))).run s0 >>=
          fun r => pure ((r.1.map (CryptoGames.FSAEAD.withPub p), endedPub), some r.2)) := by
  cases os <;>
    simp [fsaeadHeaderIface, CryptoGames.FSAEAD.pubRedImpl, CryptoGames.FSAEAD.injectQuery, hp,
      StateT.run_lift, map_eq_bind_pure_comp]

/-- Generic single-step `CoinSimEquiv` for `runLazyPubSess` against `pubRedImpl` simulated by
`fwd (lazyInit init impl)`. Parameterized so both the real-side (`hybSessStTy` / `fsImpl`) and
slot-side (`slotSessStTy` / `fsSlotImpl`) session handlers instantiate it directly. -/
private theorem runLazyPubSess_coinSimEquiv {sTy : Ty SigA} {σ : Type}
    (encS : σ → sTy.denote) (Inv : σ → Prop)
    (init : ProbComp σ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT σ ProbComp))
    (mkInit : Comp OpsF IfaceF [] sTy)
    (trS : Comp OpsF IfaceF [.prod fig8PubAdT PlainT, sTy] (.prod (.opt lctT) sTy))
    (chS : Comp OpsF IfaceF [.prod fig8PubAdT (.prod PlainT PlainT), sTy] (.prod (.opt lctT) sTy))
    (csS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt fsSendStT) sTy))
    (crS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt (.prod fsSendStT fsRecvStT)) sTy))
    (dlS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy))
    (ijS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy))
    (g : FSAEADTag) (payload : ((IfaceF).dom g).denote)
    (endedPub : Bool) (os : Option σ)
    (hInit : CoinSimEquiv (IfaceF).fwdU (mkInit.eval .nil) ((IfaceF).liftP (encS <$> init)))
    (hInitInv : ∀ s ∈ support init, Inv s)
    (hos : ∀ s, os = some s → Inv s)
    (hTr : ∀ (hdr : Header Pt) (pv : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m : Plain ℓ),
      g = .tr → HEq payload (hdr, (pv, m)) →
      ∀ s, Inv s →
        CoinSimEquiv (IfaceF).fwdU
          (trS.eval (.cons ((hdr, pv), m) (.cons (encS s) .nil)))
          ((IfaceF).liftP
            (Prod.map (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) encS <$>
              (impl (.inl (.inl (.inl (.inl (.inl (
                (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv), m))))))).run s)))
    (hCh : ∀ (hdr : Header Pt) (pv0 : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m0 : Plain ℓ)
        (pv1 : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m1 : Plain ℓ),
      g = .ch → HEq payload (hdr, ((pv0, m0), (pv1, m1))) →
      ∀ s, Inv s →
        CoinSimEquiv (IfaceF).fwdU
          (chS.eval (.cons ((hdr, pv0), (m0, m1)) (.cons (encS s) .nil)))
          ((IfaceF).liftP
            (Prod.map (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) encS <$>
              (impl (.inl (.inl (.inl (.inl (.inr (
                (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0), m0, m1))))))).run s)))
    (hCs : g = .cs →
      ∀ s, Inv s →
        CoinSimEquiv (IfaceF).fwdU
          (csS.eval (.cons () (.cons (encS s) .nil)))
          ((IfaceF).liftP
            (Prod.map (Option.map (ReductionDsl.fsSendStV (ℓ := ℓ) (Pt := Pt))) encS <$>
              (impl (.inl (.inl (.inl (.inr ()))))).run s)))
    (hCr : g = .cr →
      ∀ s, Inv s →
        CoinSimEquiv (IfaceF).fwdU
          (crS.eval (.cons () (.cons (encS s) .nil)))
          ((IfaceF).liftP
            (Prod.map
              (Option.map fun (ss, rs) =>
                (ReductionDsl.fsSendStV (ℓ := ℓ) (Pt := Pt) ss,
                 ReductionDsl.fsRecvStV (ℓ := ℓ) (Pt := Pt) rs)) encS <$>
              (impl (.inl (.inl (.inr ())))).run s)))
    (hDl : ∀ (hdr : Header Pt) (cv : (lctT (ℓ := ℓ) (Pt := Pt)).denote)
        (p : LibsignalMsgPublicPart),
      g = .dl → HEq payload (hdr, cv) →
      lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2 = some p →
      ∀ s, Inv s →
        CoinSimEquiv (IfaceF).fwdU
          (dlS.eval (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
            (.cons (encS s) .nil)))
          ((IfaceF).liftP
            (Prod.map
              (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id)) encS <$>
              (impl (.inl (.inr ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv)))).run s)))
    (hIj : ∀ (hdr : Header Pt) (cv : (lctT (ℓ := ℓ) (Pt := Pt)).denote)
        (p : LibsignalMsgPublicPart),
      g = .ij → HEq payload (hdr, cv) →
      lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2 = some p →
      ∀ s, Inv s →
        CoinSimEquiv (IfaceF).fwdU
          (ijS.eval (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
            (.cons (encS s) .nil)))
          ((IfaceF).liftP
            (Prod.map
              (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id)) encS <$>
              (impl (.inr ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv))).run s))) :
    CoinSimEquiv (IfaceF).fwdU
      ((runLazyPubSess ℓ Pt C Dh encPt encT lam mkInit trS chS csS crS dlS ijS g).eval
        (.cons payload (.cons (endedPub, os.map encS) .nil)))
      ((IfaceF).liftP
        ((fun z => ((IfaceF).dec g payload z.1.1, (z.1.2, z.2.map encS))) <$>
          (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
            (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl))
            ((CryptoGames.FSAEAD.pubRedImpl
              (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
              (AD := Header Pt) (M := Plain ℓ)
              (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
              ((IfaceF).enc g payload)).run endedPub)).run os)) := by
  have hGetInv : ∀ s0 ∈ support (match os with | some s => pure s | none => init), Inv s0 := by
    intro s0 hs0
    cases os with
    | none => exact hInitInv s0 hs0
    | some s =>
      simp only [support_pure, Set.mem_singleton_iff] at hs0
      subst s0
      exact hos s rfl
  have hEns := ensureSessInit_coinSimEquiv ℓ Pt C Dh encPt encT lam encS init mkInit hInit os
  cases g with
  | tr =>
    rcases payload with ⟨hdr, ⟨pv, m⟩⟩
    rw [pubRedImpl_lazyInit_tr ℓ Pt init impl hdr pv m endedPub os]
    simp only [map_bind, map_pure]
    dsimp only [runLazyPubSess, Comp.eval, Expr.eval, Env.get, fsaeadHeaderIface]
    rw [pure_bind, renId1_eval]
    refine coinSimEquiv_liftP_map_bind_of_support IfaceF encS hEns fun s0 hs0 => ?_
    dsimp only [Expr.eval, Env.get]
    rw [pure_bind, renId2_eval]
    refine coinSimEquiv_liftP_map_bind_of_support IfaceF
      (Prod.map (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) encS)
      (hTr hdr pv m rfl HEq.rfl s0 (hGetInv s0 hs0))
      fun r _ => ?_
    dsimp only [Prod.map, Expr.eval, Env.get, Option.map]
    exact coinSimEquiv_liftP_pure IfaceF _
  | ch =>
    rcases payload with ⟨hdr, ⟨⟨pv0, m0⟩, ⟨pv1, m1⟩⟩⟩
    rw [pubRedImpl_lazyInit_ch ℓ Pt init impl hdr pv0 m0 pv1 m1 endedPub os]
    simp only [map_bind, map_pure]
    dsimp only [runLazyPubSess, Comp.eval, Expr.eval, Env.get, fsaeadHeaderIface]
    rw [pure_bind, renId1_eval]
    refine coinSimEquiv_liftP_map_bind_of_support IfaceF encS hEns fun s0 hs0 => ?_
    dsimp only [Expr.eval, Env.get]
    rw [pure_bind, renId2_eval]
    refine coinSimEquiv_liftP_map_bind_of_support IfaceF
      (Prod.map (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) encS)
      (hCh hdr pv0 m0 pv1 m1 rfl HEq.rfl s0 (hGetInv s0 hs0))
      fun r _ => ?_
    dsimp only [Prod.map, Expr.eval, Env.get, Option.map]
    exact coinSimEquiv_liftP_pure IfaceF _
  | cs =>
    cases payload
    rw [pubRedImpl_lazyInit_cs ℓ Pt init impl endedPub os]
    simp only [map_bind, map_pure]
    dsimp only [runLazyPubSess, Comp.eval, Expr.eval, Env.get, fsaeadHeaderIface]
    rw [pure_bind, renId1_eval]
    refine coinSimEquiv_liftP_map_bind_of_support IfaceF encS hEns fun s0 hs0 => ?_
    rw [renUnit2_eval]
    refine coinSimEquiv_liftP_map_bind_of_support IfaceF
      (Prod.map (Option.map (ReductionDsl.fsSendStV (ℓ := ℓ) (Pt := Pt))) encS)
      (hCs rfl s0 (hGetInv s0 hs0))
      fun r _ => ?_
    dsimp only [Prod.map, Expr.eval, Env.get, Option.map]
    exact coinSimEquiv_liftP_pure IfaceF _
  | cr =>
    cases payload
    rw [pubRedImpl_lazyInit_cr ℓ Pt init impl endedPub os]
    simp only [map_bind, map_pure]
    dsimp only [runLazyPubSess, Comp.eval, Expr.eval, Env.get, fsaeadHeaderIface]
    rw [pure_bind, renId1_eval]
    refine coinSimEquiv_liftP_map_bind_of_support IfaceF encS hEns fun s0 hs0 => ?_
    rw [renUnit2_eval]
    refine coinSimEquiv_liftP_map_bind_of_support IfaceF
      (Prod.map
        (Option.map fun (ss, rs) =>
          (ReductionDsl.fsSendStV (ℓ := ℓ) (Pt := Pt) ss,
           ReductionDsl.fsRecvStV (ℓ := ℓ) (Pt := Pt) rs)) encS)
      (hCr rfl s0 (hGetInv s0 hs0))
      fun ⟨r1, r2⟩ _ => ?_
    cases r1 with
    | none => exact coinSimEquiv_liftP_pure IfaceF _
    | some x =>
      rcases x with ⟨ss, rs⟩
      exact coinSimEquiv_liftP_pure IfaceF _
  | dl =>
    rcases payload with ⟨hdr, cv⟩
    dsimp only [runLazyPubSess, Comp.eval]
    have hpub : (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam)
          (lPubOfExpr ℓ Pt C encT (Γ := [(IfaceF).dom .dl, .prod .bool (.opt sTy)])
            (.snd (.snd (.var .zero))))).eval
        (.cons (t := (IfaceF).dom .dl) (hdr, cv)
          (.cons (t := .prod .bool (.opt sTy)) (endedPub, os.map encS) .nil)) =
        (lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2).map
          (ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt)) := by
      rw [liftFsExpr_eval, Computational.Proofs.ReductionDsl.FsAtomicOps.lPubOfExpr_eval]
      rfl
    rw [hpub]
    cases hp : lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2 with
    | none =>
      rw [Option.map_none]
      dsimp only [Comp.eval, Expr.eval, Env.get, fsaeadHeaderIface,
        CryptoGames.FSAEAD.pubRedImpl, CryptoGames.FSAEAD.deliverQuery]
      simpa [hp, StateT.run_pure, simulateQ_pure, Iface.liftP] using
        coinSimEquiv_liftP_pure IfaceF
          ((none : ((IfaceF).cod .dl).denote), (endedPub, os.map encS))
    | some p =>
      rw [pubRedImpl_lazyInit_dl_some ℓ Pt init impl hdr cv p hp endedPub os]
      simp only [Option.map_some, map_bind, map_pure]
      dsimp only [Comp.eval, Expr.eval, Env.get, fsaeadHeaderIface]
      rw [pure_bind, renId1_eval]
      refine coinSimEquiv_liftP_map_bind_of_support IfaceF encS hEns fun s0 hs0 => ?_
      dsimp only [Expr.eval, Env.get]
      rw [pure_bind, renId2_eval]
      refine coinSimEquiv_liftP_map_bind_of_support IfaceF
        (Prod.map (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
          encS)
        (hDl hdr cv p rfl HEq.rfl hp s0 (hGetInv s0 hs0))
        fun r _ => ?_
      dsimp only [Prod.map, Comp.eval, Expr.eval, Env.get]
      rw [pure_bind, mapRrWithPubExpr_eval ℓ Pt C Dh encPt encT lam
        (.var .zero) (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
        _ r.1 p rfl rfl]
      dsimp only [Expr.eval, Env.get, Option.map]
      exact coinSimEquiv_liftP_pure IfaceF _
  | ij =>
    rcases payload with ⟨hdr, cv⟩
    dsimp only [runLazyPubSess, Comp.eval]
    have hpub : (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam)
          (lPubOfExpr ℓ Pt C encT (Γ := [(IfaceF).dom .ij, .prod .bool (.opt sTy)])
            (.snd (.snd (.var .zero))))).eval
        (.cons (t := (IfaceF).dom .ij) (hdr, cv)
          (.cons (t := .prod .bool (.opt sTy)) (endedPub, os.map encS) .nil)) =
        (lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2).map
          (ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt)) := by
      rw [liftFsExpr_eval, Computational.Proofs.ReductionDsl.FsAtomicOps.lPubOfExpr_eval]
      rfl
    rw [hpub]
    cases hp : lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2 with
    | none =>
      rw [Option.map_none]
      dsimp only [Comp.eval, Expr.eval, Env.get, fsaeadHeaderIface,
        CryptoGames.FSAEAD.pubRedImpl, CryptoGames.FSAEAD.injectQuery]
      cases endedPub <;>
        simpa [hp, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure,
          ReductionDsl.fsRrEnc, Iface.liftP] using
          coinSimEquiv_liftP_pure IfaceF _
    | some p =>
      rw [pubRedImpl_lazyInit_ij_some ℓ Pt init impl hdr cv p hp endedPub os]
      simp only [Option.map_some, map_bind, map_pure]
      dsimp only [Comp.eval, Expr.eval, Env.get, fsaeadHeaderIface]
      rw [pure_bind, renId1_eval]
      refine coinSimEquiv_liftP_map_bind_of_support IfaceF encS hEns fun s0 hs0 => ?_
      dsimp only [Expr.eval, Env.get]
      rw [pure_bind, renId2_eval]
      refine coinSimEquiv_liftP_map_bind_of_support IfaceF
        (Prod.map (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
          encS)
        (hIj hdr cv p rfl HEq.rfl hp s0 (hGetInv s0 hs0))
        fun r _ => ?_
      dsimp only [Prod.map, Comp.eval, Expr.eval, Env.get]
      rw [pure_bind, mapRrWithPubExpr_eval ℓ Pt C Dh encPt encT lam
        (.var .zero) (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
        _ r.1 p rfl rfl]
      dsimp only [Expr.eval, Env.get, Option.map]
      exact coinSimEquiv_liftP_pure IfaceF _

omit [DecidableEq Pt] [Zero Pt] in
/-- Pure `ProbComp` support/invariant preservation for one `pubRedImpl` + `lazyInit init impl` step. -/
private theorem lazyPubSess_support_step {σ : Type}
    {P_pre P_post : Option σ → Prop} {Q : σ → Prop}
    (init : ProbComp σ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT σ ProbComp))
    (g : FSAEADTag) (payload : ((IfaceF).dom g).denote)
    (endedPub : Bool) (os : Option σ)
    (hpre : P_pre os)
    (hKeep : P_pre os → P_post os)
    (hInit : P_pre none → ∀ s0 ∈ support init, Q s0)
    (hSome : ∀ s, os = some s → P_pre (some s) → Q s)
    (hStep : ∀ q0 s0, Q s0 → ∀ r ∈ support ((impl q0).run s0), P_post (some r.2)) :
    ∀ z ∈ support
      ((simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
        (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl))
        ((CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
          ((IfaceF).enc g payload)).run endedPub)).run os),
      P_post z.2 := by
  have hGetQ : ∀ s0 ∈ support (match os with | some s => pure s | none => init), Q s0 := by
    intro s0 hs0
    cases os with
    | none => exact hInit hpre s0 hs0
    | some s =>
      simp only [support_pure, Set.mem_singleton_iff] at hs0
      subst s0
      exact hSome s rfl hpre
  intro z hz
  cases g with
  | tr =>
    rcases payload with ⟨hdr, ⟨pv, m⟩⟩
    rw [pubRedImpl_lazyInit_tr ℓ Pt init impl hdr pv m endedPub os] at hz
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨s0, hs0, r, hr, rfl⟩ := hz
    exact hStep _ s0 (hGetQ s0 hs0) r hr
  | ch =>
    rcases payload with ⟨hdr, ⟨⟨pv0, m0⟩, ⟨pv1, m1⟩⟩⟩
    rw [pubRedImpl_lazyInit_ch ℓ Pt init impl hdr pv0 m0 pv1 m1 endedPub os] at hz
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨s0, hs0, r, hr, rfl⟩ := hz
    exact hStep _ s0 (hGetQ s0 hs0) r hr
  | cs =>
    cases payload
    rw [pubRedImpl_lazyInit_cs ℓ Pt init impl endedPub os] at hz
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨s0, hs0, r, hr, rfl⟩ := hz
    exact hStep _ s0 (hGetQ s0 hs0) r hr
  | cr =>
    cases payload
    rw [pubRedImpl_lazyInit_cr ℓ Pt init impl endedPub os] at hz
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨s0, hs0, r, hr, rfl⟩ := hz
    exact hStep _ s0 (hGetQ s0 hs0) r hr
  | dl =>
    rcases payload with ⟨hdr, cv⟩
    cases hp : lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2 with
    | none =>
      dsimp only [fsaeadHeaderIface, CryptoGames.FSAEAD.pubRedImpl,
        CryptoGames.FSAEAD.deliverQuery] at hz
      simp [hp, StateT.run_pure, simulateQ_pure] at hz
      subst hz
      exact hKeep hpre
    | some p =>
      rw [pubRedImpl_lazyInit_dl_some ℓ Pt init impl hdr cv p hp endedPub os] at hz
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨s0, hs0, r, hr, rfl⟩ := hz
      exact hStep _ s0 (hGetQ s0 hs0) r hr
  | ij =>
    rcases payload with ⟨hdr, cv⟩
    cases hp : lPubOf protoSignalCodec (ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv).2 with
    | none =>
      dsimp only [fsaeadHeaderIface, CryptoGames.FSAEAD.pubRedImpl,
        CryptoGames.FSAEAD.injectQuery] at hz
      simp [hp, StateT.run_get, StateT.run_pure, simulateQ_pure] at hz
      subst hz
      exact hKeep hpre
    | some p =>
      rw [pubRedImpl_lazyInit_ij_some ℓ Pt init impl hdr cv p hp endedPub os] at hz
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨s0, hs0, r, hr, rfl⟩ := hz
      exact hStep _ s0 (hGetQ s0 hs0) r hr

/-! ### Real-side (`fsImpl` / `fsInit`) session handler soundness -/

omit [Zero Pt] [SampleableType Pt] in
private theorem hybOpMacro_eval_local (hinj : Function.Injective encT) (o) (x) :
    (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybOpMacro (Pt := Pt) C ℓ encT idOf o).eval
      (.cons (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
        (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) _ x) .nil) =
    toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) _
      ((Ops.sum
        (CryptoGames.PRG.Costed.prgOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
          (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
        (CryptoGames.OTCCA.Costed.otccaOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))).eval o x) := by
  rcases o with ⟨⟩ | (_ | _ | _ | _ | _ | _ | _)
  · rcases x with ⟨p, ck⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.hybOpMacro,
      hybBaseTy, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen,
      mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.PRG.Costed.prgOps, CryptoGames.FSAEAD.Costed.bt]
    exact Computational.Proofs.ReductionDsl.FsAtomicOps.chainGenExpr_eval ℓ Pt C encT
      (.snd (.var .zero))
      (.cons (t := .prod .nat (ReductionDsl.BV256 (ℓ := ℓ) (Pt := Pt))) (p, ck) .nil) p
  · rcases x with ⟨seed, ⟨i, a⟩, m⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.hybOpMacro,
      hybBaseTy, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen,
      mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt, id]
    rw [Computational.Proofs.ReductionDsl.FsAtomicOps.aeadREncExpr_eval]
    simp [ReductionDsl.slotAdOfV,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.fig8PubAdOfV_fig8PubAdV]
  · rcases x with ⟨seed, ⟨i, a⟩, e⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.hybOpMacro,
      hybBaseTy, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen,
      mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt, id]
    rw [Computational.Proofs.ReductionDsl.FsAtomicOps.aeadRDecExpr_eval]
    have hsl : ReductionDsl.slotAdOfV (ℓ := ℓ) (Pt := Pt)
        (i, ReductionDsl.fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
      simp [ReductionDsl.slotAdOfV,
        Computational.Proofs.ReductionDsl.FsAtomicMacros.fig8PubAdOfV_fig8PubAdV]
    simp only [hsl, Computational.Proofs.ReductionDsl.FsAtomicMacros.wireSaltCtOfV_wireSaltCtV]
    cases (lAeadR C clampedProtoSignalCodec ℓ encT idOf).dec seed (i, a) e <;> rfl
  · rfl
  · rcases x with ⟨a₁, a₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.hybOpMacro,
      hybBaseTy, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen,
      mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt]
    rw [Computational.Proofs.ReductionDsl.FsAtomicOps.eqFig8PubAdExpr_eval ℓ Pt C encT hinj]
    simp only [Expr.eval, Computational.Proofs.ReductionDsl.FsAtomicOps.env_get_zero,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.fig8PubAdOfV_fig8PubAdV]
    by_cases h : a₁ = a₂ <;> simp [h]
  · rcases x with ⟨m₁, m₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.hybOpMacro,
      hybBaseTy, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen,
      mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt]
    rw [Computational.Proofs.ReductionDsl.FsAtomicOps.eqPlainExpr_eval]
    simp only [Expr.eval, Computational.Proofs.ReductionDsl.FsAtomicOps.env_get_zero]
    by_cases h : m₁ = m₂ <;> simp [h]
  · rcases x with ⟨c₁, c₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.hybOpMacro,
      hybBaseTy, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen,
      mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt]
    rw [Computational.Proofs.ReductionDsl.FsAtomicOps.eqWireSaltCtExpr_eval]
    simp only [Expr.eval, Computational.Proofs.ReductionDsl.FsAtomicOps.env_get_zero,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.wireSaltCtOfV_wireSaltCtV]
    by_cases h : c₁ = c₂ <;> simp [h]
  · rcases x with ⟨s₁, s₂⟩; rfl

private theorem liftFsCoinComp_prgZero_coinSimEquiv (hinj : Function.Injective encT)
    {Γ : List (Ty (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))}
    {t : Ty (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)}
    (c : Comp
      (Ops.sum
        (CryptoGames.PRG.Costed.prgOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
          (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
        (CryptoGames.OTCCA.Costed.otccaOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ())))
      (Iface.withSamp
        (Iface.withSamp
          (CryptoGames.PRG.Costed.prgIface
            (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
              (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
          (CryptoGames.OTCCA.Costed.idealSamplers (.prod .nat (.base .ad)) (.base .ct)
            (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
        (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)))
      Γ t)
    (ρ : Env Γ) :
    CoinSimEquiv (IfaceF).fwdU
      ((liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam)
        (compilePureComp (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) c)).eval
        (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
          (hybBaseTy (Pt := Pt) (ℓ := ℓ))
          (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ))
      ((IfaceF).liftP
        (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
          (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) t <$>
          c.eval ρ)) := by
  have hpure : CoinSimEquiv (coinOnlyBaseIface ℓ Pt).fwdU
      ((compilePureComp (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) c).eval
        (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
          (hybBaseTy (Pt := Pt) (ℓ := ℓ))
          (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ))
      (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
        (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) t <$>
        c.eval ρ) :=
    Computational.Proofs.ReductionDsl.FsAtomicMacros.compilePureComp_coinSimEquiv
      (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      (hybOpMacro_eval_local ℓ Pt C encT idOf hinj)
      (fun s x => by
        cases s with
        | inl s =>
          cases s with
          | inl e => exact nomatch e
          | inr u =>
            cases u; rcases x with ⟨i, a⟩
            refine (Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp_coinSimEquiv
              ℓ Pt C encT (I := coinOnlyBaseIface ℓ Pt)
              (fun b => Comp.sample (I := coinOnlyBaseIface ℓ Pt) (UniformSamplerTag.base b) .unit)
              (fun b _ => by cases b <;> rfl)
              (i, ReductionDsl.fig8PubAdV a)).trans (CoinSimEquiv.of_eq ?_)
            have hsl : ReductionDsl.slotAdOfV (ℓ := ℓ) (Pt := Pt)
                (i, ReductionDsl.fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
              simp [ReductionDsl.slotAdOfV,
                Computational.Proofs.ReductionDsl.FsAtomicMacros.fig8PubAdOfV_fig8PubAdV]
            rw [hsl]
            dsimp only [prgZeroMacroBundle, Iface.withSamp, ReductionDsl.Samplers.sum,
              CryptoGames.PRG.Costed.prgIface, CryptoGames.OTCCA.Costed.idealSamplers,
              coinOnlyBaseIface, Iface.liftP, toVal,
              Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen, hybBaseTy, mapTy,
              CryptoGames.FSAEAD.Costed.bt]
            rfl
        | inr t =>
          rcases t with _ | N | (_ | _)
          · exact CoinSimEquiv.of_eq rfl
          · exact CoinSimEquiv.of_eq (by
              dsimp only [prgZeroMacroBundle, coinOnlyBaseIface, Iface.withSamp,
                ReductionDsl.Samplers.sum, Sum.elim, CryptoGames.PRG.Costed.prgIface, Iface.liftP,
                ReductionDsl.unifSamplers, CryptoGames.FSAEAD.Costed.fsStateSampleSort,
                CryptoGames.FSAEAD.Costed.fsSig, Comp.eval, ReductionDsl.atomicBaseSamplers,
                ReductionDsl.AtomicBaseUnif.sort, ReductionDsl.AtomicSort.den,
                toVal, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen,
                hybBaseTy, mapTy]
              exact (id_map _).symm)
          · exact CoinSimEquiv.of_eq rfl
          · exact CoinSimEquiv.of_eq rfl)
      (fun g => nomatch g) c ρ
  exact (CoinSimEquiv.of_eq (liftFsCoinComp_eval (Dh := Dh) (encPt := encPt) (lam := lam)
    (compilePureComp (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) c) _)).trans
    (Computational.Proofs.ReductionDsl.FsAtomicMacros.coinSimEquiv_liftP IfaceF
      hpure.evalDistEq_unifSpec)

private def encHybSessSt
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt) : (hybSessStTy ℓ Pt).denote :=
  toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
    (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
    (CryptoGames.FSAEAD.Thm5.Costed.stTy
      (CK := BitVec 256) (MK := BitVec 256)
      (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt))
    (CryptoGames.FSAEAD.Thm5.Costed.encSt s)

omit [SampleableType Pt] in
private theorem initHybSessStExpr_eval (hinj : Function.Injective encT) (b : Bool) :
    (initHybSessStExpr ℓ Pt C Dh encPt encT idOf lam).eval (.cons (t := .bool) b .nil) =
      encHybSessSt ℓ Pt (CryptoGames.FSAEAD.Thm5.hInit b .unknown) := by
  dsimp only [initHybSessStExpr, encHybSessSt]
  refine (liftFsExpr_eval (Dh := Dh) (encPt := encPt) (lam := lam) _ _).trans ?_
  have he := Computational.Proofs.ReductionDsl.FsAtomicMacros.compilePureExpr_eval
    (t := CryptoGames.FSAEAD.Thm5.Costed.stTy
      (CK := BitVec 256) (MK := BitVec 256)
      (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt))
    (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
    (hybOpMacro_eval_local ℓ Pt C encT idOf hinj)
    (.pair
      (CryptoGames.FSAEAD.Thm5.Costed.initHSE
        (CK := BitVec 256) (MK := BitVec 256)
        (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt) (.var .zero))
      (.inl .unit))
    (.cons (t := .bool) b .nil)
  exact he.trans (congrArg
    (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
      (CryptoGames.FSAEAD.Thm5.Costed.stTy
        (CK := BitVec 256) (MK := BitVec 256)
        (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)))
    (Prod.ext
      (CryptoGames.FSAEAD.Thm5.Costed.initHSE_eval (.cons (t := .bool) b .nil) (.var .zero))
      rfl))

private theorem initRealSessComp_coinSimEquiv (hinj : Function.Injective encT) :
    CoinSimEquiv (IfaceF).fwdU
      ((initRealSessComp ℓ Pt C Dh encPt encT idOf lam).eval .nil)
      ((IfaceF).liftP (encHybSessSt ℓ Pt <$>
        (CryptoVerification.E2E.Signed.SessionFS.fsInit :
          ProbComp (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)))) := by
  refine CoinSimEquiv.of_eq ?_
  have hbind : ∀ {α β : Type} (p : ProbComp α) (k : α → ProbComp β),
      (IfaceF).liftP (p >>= k) = (IfaceF).liftP p >>= fun x => (IfaceF).liftP (k x) := by
    intro α β p k
    simp [Iface.liftP]
  dsimp only [initRealSessComp, Comp.eval, CryptoVerification.E2E.Signed.SessionFS.fsInit]
  have hmap :
      (encHybSessSt ℓ Pt <$>
        (do
          let b ← ($ᵗ Bool : ProbComp Bool)
          pure (CryptoGames.FSAEAD.Thm5.hInit b .unknown))) =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        pure (encHybSessSt ℓ Pt (CryptoGames.FSAEAD.Thm5.hInit b .unknown))) := by
    simp
  rw [hmap, hbind]
  refine bind_congr fun b => ?_
  rw [initHybSessStExpr_eval ℓ Pt C Dh encPt encT idOf lam hinj b]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fsInit_hInv :
    ∀ s ∈ support
      (CryptoVerification.E2E.Signed.SessionFS.fsInit :
        ProbComp (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
          (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)),
      CryptoGames.FSAEAD.Thm5.HInv maxForwardJumps 0 s.1 := by
  intro s hs
  simp only [CryptoVerification.E2E.Signed.SessionFS.fsInit, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hs
  obtain ⟨b, -, rfl⟩ := hs
  exact CryptoGames.FSAEAD.Thm5.HInv.init b

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem genStep_j_eq {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType MK]
    (G : ℕ → PRGScheme CK (CK × MK))
    (P₁ P₂ : CryptoGames.FSAEAD.Thm5.Params)
    (D : ℕ → ProbComp (CK × MK)) (hj : P₁.j = P₂.j) :
    CryptoGames.FSAEAD.Thm5.genStep (m := m) (AD := AD) (M := M) (C := C) G P₁ D =
      CryptoGames.FSAEAD.Thm5.genStep (m := m) (AD := AD) (M := M) (C := C) G P₂ D := by
  unfold CryptoGames.FSAEAD.Thm5.genStep
  rw [hj]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem genN_j_eq {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType MK]
    (G : ℕ → PRGScheme CK (CK × MK))
    (P₁ P₂ : CryptoGames.FSAEAD.Thm5.Params)
    (D : ℕ → ProbComp (CK × MK)) (hj : P₁.j = P₂.j) (n : ℕ) :
    CryptoGames.FSAEAD.Thm5.genN (m := m) (AD := AD) (M := M) (C := C) G P₁ D n =
      CryptoGames.FSAEAD.Thm5.genN (m := m) (AD := AD) (M := M) (C := C) G P₂ D n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [CryptoGames.FSAEAD.Thm5.genN, genStep_j_eq G P₁ P₂ D hj, ih]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem genUpTo_j_eq {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType MK]
    (G : ℕ → PRGScheme CK (CK × MK))
    (P₁ P₂ : CryptoGames.FSAEAD.Thm5.Params)
    (D : ℕ → ProbComp (CK × MK)) (hj : P₁.j = P₂.j) :
    CryptoGames.FSAEAD.Thm5.genUpTo (m := m) (AD := AD) (M := M) (C := C) G P₁ D =
      CryptoGames.FSAEAD.Thm5.genUpTo (m := m) (AD := AD) (M := M) (C := C) G P₂ D := by
  funext i
  unfold CryptoGames.FSAEAD.Thm5.genUpTo
  simp only [genN_j_eq G P₁ P₂ D hj]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem corruptSenderH_la_eq {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (G : ℕ → PRGScheme CK (CK × MK))
    (P₁ P₂ : CryptoGames.FSAEAD.Thm5.Params) (hla : P₁.la = P₂.la) :
    CryptoGames.FSAEAD.Thm5.corruptSenderH (m := m) (AD := AD) (M := M) (C := C) G P₁ =
      CryptoGames.FSAEAD.Thm5.corruptSenderH (m := m) (AD := AD) (M := M) (C := C) G P₂ := by
  funext u
  unfold CryptoGames.FSAEAD.Thm5.corruptSenderH
  rw [hla]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem corruptReceiverH_la_eq {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (G : ℕ → PRGScheme CK (CK × MK))
    (P₁ P₂ : CryptoGames.FSAEAD.Thm5.Params) (hla : P₁.la = P₂.la) :
    CryptoGames.FSAEAD.Thm5.corruptReceiverH (m := m) (AD := AD) (M := M) (C := C) (MK := MK) G P₁ =
      CryptoGames.FSAEAD.Thm5.corruptReceiverH (m := m) (AD := AD) (M := M) (C := C) (MK := MK) G P₂ := by
  funext u
  unfold CryptoGames.FSAEAD.Thm5.corruptReceiverH
  rw [hla]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem multiDecIdx_specialIdeal {CK MK AD M C : Type}
    (ideal : ℕ × AD → ProbComp C) (ae : CryptoGames.AEADScheme MK (ℕ × AD) M C)
    (mSlot : ℕ) (la : Bool) :
    CryptoGames.FSAEAD.Thm5.multiDecIdx ae ((hp mSlot 0 la).t.getD 0) mSlot
      (some ({ enc := fun ia _ => ideal ia, dec := fun _ _ => pure none } :
        CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) =
      CryptoGames.FSAEAD.Thm5.decIdx (CK := CK) ae (hp mSlot mSlot la)
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) := by
  funext hint i a e
  apply StateT.ext
  intro ⟨h, sl⟩
  cases hint with
  | some msg => rfl
  | none =>
    dsimp only [CryptoGames.FSAEAD.Thm5.multiDecIdx, CryptoGames.FSAEAD.Thm5.decIdx,
      CryptoGames.FSAEAD.Thm5.multiKind, CryptoGames.FSAEAD.Thm5.kind,
      CryptoGames.FSAEAD.Thm5.getH, CryptoGames.FSAEAD.Thm5.onH, hp,
      Option.getD, Option.all, Option.isSome]
    by_cases hc : h.isCompromised i = true
    · simp [hc]
    · have hcF : h.isCompromised i = false := Bool.eq_false_iff.mpr hc
      by_cases hi0 : i ≤ 0
      · have him : i ≤ mSlot := by omega
        simp [hcF, hi0, him]
      · by_cases him : i ≤ mSlot
        · simp [hcF, hi0, him]
        · simp [hi0, him]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem multiEncIdxWith_specialIdeal {CK MK AD M C : Type}
    (ideal : ℕ × AD → ProbComp C) (ae : CryptoGames.AEADScheme MK (ℕ × AD) M C)
    (mSlot : ℕ) (la : Bool) :
    CryptoGames.FSAEAD.Thm5.multiEncIdxWith ideal ae ((hp mSlot 0 la).t.getD 0) mSlot
      (some ({ enc := fun ia _ => ideal ia, dec := fun _ _ => pure none } :
        CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) =
      CryptoGames.FSAEAD.Thm5.encIdxWith (CK := CK) ideal ae (hp mSlot mSlot la)
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) := by
  funext i a msg
  apply StateT.ext
  intro ⟨h, sl⟩
  dsimp only [CryptoGames.FSAEAD.Thm5.multiEncIdxWith, CryptoGames.FSAEAD.Thm5.encIdxWith,
    CryptoGames.FSAEAD.Thm5.multiKind, CryptoGames.FSAEAD.Thm5.kind,
    CryptoGames.FSAEAD.Thm5.getH, CryptoGames.FSAEAD.Thm5.onH,
    CryptoGames.FSAEAD.Thm5.sampleH, hp, Option.getD, Option.all, Option.isSome]
  by_cases hc : h.isCompromised i = true
  · simp [hc]
  · have hcF : h.isCompromised i = false := Bool.eq_false_iff.mpr hc
    by_cases hi0 : i ≤ 0
    · have him : i ≤ mSlot := by omega
      simp [hcF, hi0, him]
    · by_cases him : i ≤ mSlot
      · simp [hcF, hi0, him]
      · simp [hi0, him]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem multiReceiveH_specialIdeal {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    (ideal : ℕ × AD → ProbComp C) (ae : CryptoGames.AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip mSlot : ℕ) (la : Bool)
    (D : ℕ → ProbComp (CK × MK)) :
    CryptoGames.FSAEAD.Thm5.multiReceiveH ae G maxSkip (hp mSlot 0 la) mSlot D
      (some ({ enc := fun ia _ => ideal ia, dec := fun _ _ => pure none } :
        CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) =
      CryptoGames.FSAEAD.Thm5.receiveH ae G maxSkip (hp mSlot mSlot la) D
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) := by
  funext hint a ⟨i, e⟩
  unfold CryptoGames.FSAEAD.Thm5.multiReceiveH CryptoGames.FSAEAD.Thm5.receiveH
  rw [multiDecIdx_specialIdeal ideal ae mSlot la,
    genUpTo_j_eq G (hp mSlot 0 la) (hp mSlot mSlot la) D rfl]
  refine CryptoGames.FSAEAD.Thm5.Costed.bind_congr' _ fun st => ?_
  split
  · refine CryptoGames.FSAEAD.Thm5.Costed.bind_congr' _ fun r => ?_
    cases r <;> rfl
  · split
    · rfl
    · dsimp only [hp]
      rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem multiOraclesWith_specialIdeal_eq_fsImpl {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : CryptoGames.AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip mSlot : ℕ) (la : Bool) :
    CryptoGames.FSAEAD.Thm5.multiOraclesWith ideal ae G maxSkip (hp mSlot 0 la) mSlot
      (CryptoGames.FSAEAD.Thm5.DG G)
      (some ({ enc := fun ia _ => ideal ia, dec := fun _ _ => pure none } :
        CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) =
      CryptoVerification.E2E.Signed.SessionFS.fsImpl ideal ae G maxSkip (hp mSlot mSlot la) := by
  have htx :
      CryptoGames.FSAEAD.Thm5.multiTransmitHWith ideal ae G (hp mSlot 0 la) mSlot
        (CryptoGames.FSAEAD.Thm5.DG G)
        (some ({ enc := fun ia _ => ideal ia, dec := fun _ _ => pure none } :
          CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) =
      CryptoGames.FSAEAD.Thm5.transmitHWith ideal ae G (hp mSlot mSlot la)
        (CryptoGames.FSAEAD.Thm5.DG G)
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) := by
    funext q
    unfold CryptoGames.FSAEAD.Thm5.multiTransmitHWith CryptoGames.FSAEAD.Thm5.transmitHWith
    rw [genUpTo_j_eq G (hp mSlot 0 la) (hp mSlot mSlot la) _ rfl,
      multiEncIdxWith_specialIdeal ideal ae mSlot la]
  have hch :
      CryptoGames.FSAEAD.Thm5.multiChallengeHWith ideal ae G (hp mSlot 0 la) mSlot
        (CryptoGames.FSAEAD.Thm5.DG G)
        (some ({ enc := fun ia _ => ideal ia, dec := fun _ _ => pure none } :
          CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) =
      CryptoGames.FSAEAD.Thm5.challengeHWith ideal ae G (hp mSlot mSlot la)
        (CryptoGames.FSAEAD.Thm5.DG G)
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) := by
    funext q
    unfold CryptoGames.FSAEAD.Thm5.multiChallengeHWith CryptoGames.FSAEAD.Thm5.challengeHWith
    rw [genUpTo_j_eq G (hp mSlot 0 la) (hp mSlot mSlot la) _ rfl,
      multiEncIdxWith_specialIdeal ideal ae mSlot la]
  have hdl :
      CryptoGames.FSAEAD.Thm5.multiDeliverH ae G maxSkip (hp mSlot 0 la) mSlot
        (CryptoGames.FSAEAD.Thm5.DG G)
        (some ({ enc := fun ia _ => ideal ia, dec := fun _ _ => pure none } :
          CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) =
      CryptoGames.FSAEAD.Thm5.deliverH ae G maxSkip (hp mSlot mSlot la)
        (CryptoGames.FSAEAD.Thm5.DG G)
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) := by
    funext q
    unfold CryptoGames.FSAEAD.Thm5.multiDeliverH CryptoGames.FSAEAD.Thm5.deliverH
    rw [multiReceiveH_specialIdeal ideal ae G maxSkip mSlot la]
    refine CryptoGames.FSAEAD.Thm5.Costed.bind_congr' _ fun st => ?_
    split
    · rfl
    · cases st.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
      | none => rfl
      | some r =>
        dsimp only
        refine CryptoGames.FSAEAD.Thm5.Costed.bind_congr' _ fun res => ?_
        cases res <;> rfl
  have hinj :
      CryptoGames.FSAEAD.Thm5.multiInjectH ae G maxSkip (hp mSlot 0 la) mSlot
        (CryptoGames.FSAEAD.Thm5.DG G)
        (some ({ enc := fun ia _ => ideal ia, dec := fun _ _ => pure none } :
          CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) =
      CryptoGames.FSAEAD.Thm5.injectH ae G maxSkip (hp mSlot mSlot la)
        (CryptoGames.FSAEAD.Thm5.DG G)
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp)) := by
    funext q
    unfold CryptoGames.FSAEAD.Thm5.multiInjectH CryptoGames.FSAEAD.Thm5.injectH
    rw [multiReceiveH_specialIdeal ideal ae G maxSkip mSlot la]
    refine CryptoGames.FSAEAD.Thm5.Costed.bind_congr' _ fun st => ?_
    split
    · rfl
    · refine CryptoGames.FSAEAD.Thm5.Costed.bind_congr' _ fun res => ?_
      cases res <;> rfl
  unfold CryptoGames.FSAEAD.Thm5.multiOraclesWith
    CryptoVerification.E2E.Signed.SessionFS.fsImpl CryptoGames.FSAEAD.Thm5.oraclesWith
  rw [htx, hch, corruptSenderH_la_eq G (hp mSlot 0 la) (hp mSlot mSlot la) rfl,
    corruptReceiverH_la_eq G (hp mSlot 0 la) (hp mSlot mSlot la) rfl, hdl, hinj]

omit [Zero Pt] [SampleableType Pt] in
private theorem fsImpl_clamped_tr_eq (P : CryptoGames.FSAEAD.Thm5.Params)
    (a : Header Pt × LibsignalMsgPublicPart) (m : Plain ℓ)
    (hshort : atomicShortB a.2 = true) :
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inl (.inl (.inl (.inl (.inl (a, m)))))) =
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inl (.inl (.inl (.inl (.inl (a, m)))))) := by
  have henc : ∀ i msg,
      CryptoGames.FSAEAD.Thm5.encIdxWith (CK := BitVec 256)
        (lIdeal C clampedProtoSignalCodec ℓ encT)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) P
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp)) i a msg =
      CryptoGames.FSAEAD.Thm5.encIdxWith (CK := BitVec 256)
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) P
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp)) i a msg := by
    intro i msg
    unfold CryptoGames.FSAEAD.Thm5.encIdxWith
    simp only [
      Computational.Proofs.ReductionDsl.FsAtomicOps.lIdeal_clamped_eq C ℓ encT (i, a) hshort,
      Computational.Proofs.ReductionDsl.FsAtomicOps.lAeadR_clamped_enc_eq
        C ℓ encT idOf _ (i, a) msg hshort]
  change CryptoGames.FSAEAD.Thm5.transmitHWith (m := ProbComp)
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) P (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) none (a, m) =
    CryptoGames.FSAEAD.Thm5.transmitHWith (m := ProbComp)
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) P (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) none (a, m)
  unfold CryptoGames.FSAEAD.Thm5.transmitHWith
  simp only [henc]

omit [Zero Pt] [SampleableType Pt] in
private theorem fsImpl_clamped_ch_eq (P : CryptoGames.FSAEAD.Thm5.Params)
    (a : Header Pt × LibsignalMsgPublicPart) (m₀ m₁ : Plain ℓ)
    (hshort : atomicShortB a.2 = true) :
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁)))))) =
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁)))))) := by
  have henc : ∀ i msg,
      CryptoGames.FSAEAD.Thm5.encIdxWith (CK := BitVec 256)
        (lIdeal C clampedProtoSignalCodec ℓ encT)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) P
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp)) i a msg =
      CryptoGames.FSAEAD.Thm5.encIdxWith (CK := BitVec 256)
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) P
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp)) i a msg := by
    intro i msg
    unfold CryptoGames.FSAEAD.Thm5.encIdxWith
    simp only [
      Computational.Proofs.ReductionDsl.FsAtomicOps.lIdeal_clamped_eq C ℓ encT (i, a) hshort,
      Computational.Proofs.ReductionDsl.FsAtomicOps.lAeadR_clamped_enc_eq
        C ℓ encT idOf _ (i, a) msg hshort]
  change CryptoGames.FSAEAD.Thm5.challengeHWith (m := ProbComp)
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) P (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) none (a, m₀, m₁) =
    CryptoGames.FSAEAD.Thm5.challengeHWith (m := ProbComp)
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) P (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) none (a, m₀, m₁)
  unfold CryptoGames.FSAEAD.Thm5.challengeHWith
  simp only [henc]

omit [Zero Pt] [SampleableType Pt] in
private theorem fsImpl_clamped_cs_eq (P : CryptoGames.FSAEAD.Thm5.Params) :
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inl (.inl (.inl (.inr ())))) =
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inl (.inl (.inl (.inr ())))) := by
  change CryptoGames.FSAEAD.Thm5.corruptSenderH (m := ProbComp)
      (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
      (lChainPRG C.F) P () =
    CryptoGames.FSAEAD.Thm5.corruptSenderH (m := ProbComp)
      (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
      (lChainPRG C.F) P ()
  rfl

omit [Zero Pt] [SampleableType Pt] in
private theorem fsImpl_clamped_dl_eq (P : CryptoGames.FSAEAD.Thm5.Params)
    (q : (Header Pt × LibsignalMsgPublicPart) × (ℕ × LCt)) :
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inl (.inr q)) =
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inl (.inr q)) := by
  have hdec :
      CryptoGames.FSAEAD.Thm5.decIdx (CK := BitVec 256)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) P
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp)) =
      CryptoGames.FSAEAD.Thm5.decIdx (CK := BitVec 256)
        (lAeadR C protoSignalCodec ℓ encT idOf) P
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp)) := by
    funext hint i a e
    unfold CryptoGames.FSAEAD.Thm5.decIdx
    simp only [Computational.Proofs.ReductionDsl.FsAtomicOps.lAeadR_clamped_dec_eq]
  change CryptoGames.FSAEAD.Thm5.deliverH (m := ProbComp)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) none q =
    CryptoGames.FSAEAD.Thm5.deliverH (m := ProbComp)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) none q
  unfold CryptoGames.FSAEAD.Thm5.deliverH CryptoGames.FSAEAD.Thm5.receiveH
  rw [hdec]

omit [Zero Pt] [SampleableType Pt] in
private theorem fsImpl_clamped_ij_eq (P : CryptoGames.FSAEAD.Thm5.Params)
    (q : (Header Pt × LibsignalMsgPublicPart) × (ℕ × LCt)) :
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inr q) =
    CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (.inr q) := by
  have hdec :
      CryptoGames.FSAEAD.Thm5.decIdx (CK := BitVec 256)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) P
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp)) =
      CryptoGames.FSAEAD.Thm5.decIdx (CK := BitVec 256)
        (lAeadR C protoSignalCodec ℓ encT idOf) P
        (none : Option (CryptoGames.FSAEAD.Thm5.SpecialOps _ _ _ ProbComp)) := by
    funext hint i a e
    unfold CryptoGames.FSAEAD.Thm5.decIdx
    simp only [Computational.Proofs.ReductionDsl.FsAtomicOps.lAeadR_clamped_dec_eq]
  change CryptoGames.FSAEAD.Thm5.injectH (m := ProbComp)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) none q =
    CryptoGames.FSAEAD.Thm5.injectH (m := ProbComp)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps P (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) none q
  unfold CryptoGames.FSAEAD.Thm5.injectH CryptoGames.FSAEAD.Thm5.receiveH
  rw [hdec]

private theorem realTrStep_coinSimEquiv (hinj : Function.Injective encT)
    (mSlot : ℕ) (la : Bool)
    (hdr : Header Pt) (pv : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m : Plain ℓ)
    (hshort : atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv) = true)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (hks : s.1.lastSentIdx ≤ s.1.keys.length) :
    CoinSimEquiv (IfaceF).fwdU
      ((realTrStep ℓ Pt C Dh encPt encT idOf lam mSlot mSlot).eval
        (.cons ((hdr, pv), m) (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((IfaceF).liftP
        (Prod.map (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) (encHybSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hp mSlot mSlot la)
            (.inl (.inl (.inl (.inl (.inl (
              (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv), m))))))).run s)) := by
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := Iface.withSamp
    (CryptoGames.PRG.Costed.prgIface
      (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
    (CryptoGames.OTCCA.Costed.idealSamplers
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1)
  let O_hyb := Ops.sum
    (CryptoGames.PRG.Costed.prgOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
      (fun pw => (G pw.1).gen pw.2) 1)
    (CryptoGames.OTCCA.Costed.otccaOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
      ae 1 .unit (fun _ => ()))
  let I_hyb := I₀.withSamp
    (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))
  let sIdeal : ∀ {Δ}, Expr O_hyb Δ (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad)) →
      Comp O_hyb I_hyb Δ (CryptoGames.FSAEAD.Costed.bt .ct) := fun ia =>
    Comp.sample (I := I_hyb) (Sum.inl (Sum.inr ())) ia
  let opsC : Option (CryptoGames.FSAEAD.Thm5.SpecialOps
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ProbComp) :=
    some { enc := fun ia _ => ideal ia, dec := fun _ _ => pure none }
  have hliftP : ∀ {α : Type} (p : ProbComp α), I₀.liftP p = (liftM p : ProbComp α) :=
    fun p => (CryptoGames.FSAEAD.Thm5.Costed.liftP_withSamp _ _ p).trans
      (CryptoGames.FSAEAD.Thm5.Costed.prgIface_liftP p)
  have hIdeal : CryptoGames.FSAEAD.Thm5.Costed.SampleIdealRel ae G 1 1 sIdeal ideal := by
    intro Δ ρ' ia
    exact hliftP (ideal (ia.eval ρ'))
  have hEnc : CryptoGames.FSAEAD.Thm5.Costed.SpecialEncRel ae G 1 1
      (some (fun x => sIdeal (.fst x))) opsC := by
    intro Δ ρ' iam
    exact hliftP (ideal (iam.eval ρ').1)
  let a : Header Pt × LibsignalMsgPublicPart :=
    (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv)
  let ρ_src : Env [.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg),
      CryptoGames.FSAEAD.Thm5.Costed.stTy] :=
    .cons (a, m) (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) .nil)
  have hρ : Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
      (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src =
      .cons ((hdr, pv), m) (.cons (encHybSessSt ℓ Pt s) .nil) := by
    change Env.cons (t := .prod fig8PubAdT PlainT)
        ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt)
          (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv)), m)
        (Env.cons (t := hybSessStTy ℓ Pt) (encHybSessSt ℓ Pt s) Env.nil) = _
    rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubV_lpubOfV]
  dsimp only [realTrStep]
  rw [← hρ]
  refine (liftFsCoinComp_prgZero_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj _ ρ_src).trans
    (CoinSimEquiv.of_eq ?_)
  refine congrArg (IfaceF).liftP ?_
  change toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) _ <$>
    (Comp.bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.transmitBody ae G 1 1
        maxForwardJumps mSlot mSlot sIdeal (some (fun x => sIdeal (.fst x))))).eval ρ_src = _
  have hsrc :
      (Comp.bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
        (CryptoGames.FSAEAD.Thm5.Costed.transmitBody ae G 1 1
          maxForwardJumps mSlot mSlot sIdeal (some (fun x => sIdeal (.fst x))))).eval ρ_src =
      (CryptoGames.FSAEAD.Thm5.Costed.transmitBody ae G 1 1
        maxForwardJumps mSlot mSlot sIdeal (some (fun x => sIdeal (.fst x)))).eval
        (.cons ((a, m), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) := by
    dsimp only [Comp.eval]
    rw [pure_bind]
    rfl
  have hbody := CryptoGames.FSAEAD.Thm5.Costed.transmitBody_eval ae G 1 1 hliftP ρ_src
    maxForwardJumps mSlot (hp mSlot 0 la) rfl ideal sIdeal hIdeal
    (some (fun x => sIdeal (.fst x))) opsC hEnc a m s hks
  change (CryptoGames.FSAEAD.Thm5.Costed.transmitBody ae G 1 1
      maxForwardJumps mSlot mSlot sIdeal (some (fun x => sIdeal (.fst x)))).eval
      (.cons ((a, m), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) =
    Prod.map id CryptoGames.FSAEAD.Thm5.Costed.encSt <$>
      (CryptoGames.FSAEAD.Thm5.multiTransmitHWith ideal ae G (hp mSlot 0 la) mSlot
        (CryptoGames.FSAEAD.Thm5.DG G) opsC (a, m)).run s at hbody
  rw [hsrc, hbody, Functor.map_map]
  have hor := congrFun (multiOraclesWith_specialIdeal_eq_fsImpl
    (CK := BitVec 256) ideal ae G maxForwardJumps mSlot la)
    (.inl (.inl (.inl (.inl (.inl (a, m))))))
  change CryptoGames.FSAEAD.Thm5.multiTransmitHWith ideal ae G (hp mSlot 0 la) mSlot
      (CryptoGames.FSAEAD.Thm5.DG G) opsC (a, m) = _ at hor
  rw [hor]
  dsimp only [ae, G, ideal, a]
  rw [fsImpl_clamped_tr_eq ℓ Pt C encT idOf (hp mSlot mSlot la)
    (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv) m hshort]
  refine congrFun (congrArg Functor.map ?_) _
  funext ⟨r1, s'⟩
  rcases r1 with _ | ⟨i, c⟩ <;> rfl

private theorem realChStep_coinSimEquiv (hinj : Function.Injective encT)
    (mSlot : ℕ) (la : Bool)
    (hdr : Header Pt)
    (pv0 : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m0 m1 : Plain ℓ)
    (hshort : atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0) = true)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (hks : s.1.lastSentIdx ≤ s.1.keys.length) :
    CoinSimEquiv (IfaceF).fwdU
      ((realChStep ℓ Pt C Dh encPt encT idOf lam mSlot mSlot).eval
        (.cons ((hdr, pv0), (m0, m1)) (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((IfaceF).liftP
        (Prod.map (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) (encHybSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hp mSlot mSlot la)
            (.inl (.inl (.inl (.inl (.inr (
              (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0), m0, m1))))))).run s)) := by
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := Iface.withSamp
    (CryptoGames.PRG.Costed.prgIface
      (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
    (CryptoGames.OTCCA.Costed.idealSamplers
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1)
  let O_hyb := Ops.sum
    (CryptoGames.PRG.Costed.prgOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
      (fun pw => (G pw.1).gen pw.2) 1)
    (CryptoGames.OTCCA.Costed.otccaOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
      ae 1 .unit (fun _ => ()))
  let I_hyb := I₀.withSamp
    (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))
  let sIdeal : ∀ {Δ}, Expr O_hyb Δ (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad)) →
      Comp O_hyb I_hyb Δ (CryptoGames.FSAEAD.Costed.bt .ct) := fun ia =>
    Comp.sample (I := I_hyb) (Sum.inl (Sum.inr ())) ia
  let opsC : Option (CryptoGames.FSAEAD.Thm5.SpecialOps
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ProbComp) :=
    some { enc := fun ia _ => ideal ia, dec := fun _ _ => pure none }
  have hliftP : ∀ {α : Type} (p : ProbComp α), I₀.liftP p = (liftM p : ProbComp α) :=
    fun p => (CryptoGames.FSAEAD.Thm5.Costed.liftP_withSamp _ _ p).trans
      (CryptoGames.FSAEAD.Thm5.Costed.prgIface_liftP p)
  have hIdeal : CryptoGames.FSAEAD.Thm5.Costed.SampleIdealRel ae G 1 1 sIdeal ideal := by
    intro Δ ρ' ia
    exact hliftP (ideal (ia.eval ρ'))
  have hEnc : CryptoGames.FSAEAD.Thm5.Costed.SpecialEncRel ae G 1 1
      (some (fun x => sIdeal (.fst x))) opsC := by
    intro Δ ρ' iam
    exact hliftP (ideal (iam.eval ρ').1)
  let a : Header Pt × LibsignalMsgPublicPart :=
    (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0)
  let ρ_src : Env [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod (CryptoGames.FSAEAD.Costed.bt .msg) (CryptoGames.FSAEAD.Costed.bt .msg)),
      CryptoGames.FSAEAD.Thm5.Costed.stTy] :=
    .cons (a, (m0, m1)) (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) .nil)
  have hρ : Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
      (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src =
      .cons ((hdr, pv0), (m0, m1)) (.cons (encHybSessSt ℓ Pt s) .nil) := by
    change Env.cons (t := .prod fig8PubAdT (.prod PlainT PlainT))
        ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt)
          (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0)), (m0, m1))
        (Env.cons (t := hybSessStTy ℓ Pt) (encHybSessSt ℓ Pt s) Env.nil) = _
    rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubV_lpubOfV]
  dsimp only [realChStep]
  rw [← hρ]
  refine (liftFsCoinComp_prgZero_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj _ ρ_src).trans
    (CoinSimEquiv.of_eq ?_)
  refine congrArg (IfaceF).liftP ?_
  change toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) _ <$>
    (Comp.bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.challengeBody ae G 1 1
        maxForwardJumps mSlot mSlot sIdeal (some (fun x => sIdeal (.fst x))))).eval ρ_src = _
  have hsrc :
      (Comp.bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
        (CryptoGames.FSAEAD.Thm5.Costed.challengeBody ae G 1 1
          maxForwardJumps mSlot mSlot sIdeal (some (fun x => sIdeal (.fst x))))).eval ρ_src =
      (CryptoGames.FSAEAD.Thm5.Costed.challengeBody ae G 1 1
        maxForwardJumps mSlot mSlot sIdeal (some (fun x => sIdeal (.fst x)))).eval
        (.cons ((a, (m0, m1)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) := by
    dsimp only [Comp.eval]
    rw [pure_bind]
    rfl
  have hbody := CryptoGames.FSAEAD.Thm5.Costed.challengeBody_eval ae G 1 1 hliftP ρ_src
    maxForwardJumps mSlot (hp mSlot 0 la) rfl ideal sIdeal hIdeal
    (some (fun x => sIdeal (.fst x))) opsC hEnc a m0 m1 s hks
  change (CryptoGames.FSAEAD.Thm5.Costed.challengeBody ae G 1 1
      maxForwardJumps mSlot mSlot sIdeal (some (fun x => sIdeal (.fst x)))).eval
      (.cons ((a, (m0, m1)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) =
    Prod.map id CryptoGames.FSAEAD.Thm5.Costed.encSt <$>
      (CryptoGames.FSAEAD.Thm5.multiChallengeHWith ideal ae G (hp mSlot 0 la) mSlot
        (CryptoGames.FSAEAD.Thm5.DG G) opsC (a, m0, m1)).run s at hbody
  rw [hsrc, hbody, Functor.map_map]
  have hor := congrFun (multiOraclesWith_specialIdeal_eq_fsImpl
    (CK := BitVec 256) ideal ae G maxForwardJumps mSlot la)
    (.inl (.inl (.inl (.inl (.inr (a, m0, m1))))))
  change CryptoGames.FSAEAD.Thm5.multiChallengeHWith ideal ae G (hp mSlot 0 la) mSlot
      (CryptoGames.FSAEAD.Thm5.DG G) opsC (a, m0, m1) = _ at hor
  rw [hor]
  dsimp only [ae, G, ideal, a]
  rw [fsImpl_clamped_ch_eq ℓ Pt C encT idOf (hp mSlot mSlot la)
    (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0) m0 m1 hshort]
  refine congrFun (congrArg Functor.map ?_) _
  funext ⟨r1, s'⟩
  rcases r1 with _ | ⟨i, c⟩ <;> rfl

private theorem realCsStep_coinSimEquiv (hinj : Function.Injective encT)
    (qSim mSlot : ℕ) (la : Bool)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (hsent : s.1.lastSentIdx ≤ qSim) :
    CoinSimEquiv (IfaceF).fwdU
      ((realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la).eval
        (.cons () (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((IfaceF).liftP
        (Prod.map (Option.map (ReductionDsl.fsSendStV (ℓ := ℓ) (Pt := Pt))) (encHybSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hp mSlot mSlot la)
            (.inl (.inl (.inl (.inr ()))))).run s)) := by
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := Iface.withSamp
    (CryptoGames.PRG.Costed.prgIface
      (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
    (CryptoGames.OTCCA.Costed.idealSamplers
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1)
  have hliftP : ∀ {α : Type} (p : ProbComp α), I₀.liftP p = (liftM p : ProbComp α) :=
    fun p => (CryptoGames.FSAEAD.Thm5.Costed.liftP_withSamp _ _ p).trans
      (CryptoGames.FSAEAD.Thm5.Costed.prgIface_liftP p)
  let stT := CryptoGames.FSAEAD.Thm5.Costed.stTy
    (CK := BitVec 256) (MK := BitVec 256)
    (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
  let ρ_src : Env [.unit, stT] :=
    .cons () (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) .nil)
  have hρ : Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
      (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src =
      .cons () (.cons (encHybSessSt ℓ Pt s) .nil) := rfl
  dsimp only [realCsStep]
  rw [← hρ]
  refine (liftFsCoinComp_prgZero_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj _ ρ_src).trans
    (CoinSimEquiv.of_eq ?_)
  refine congrArg (IfaceF).liftP ?_
  change toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
      (.prod (.opt CryptoGames.FSAEAD.Costed.rssTy) stT) <$>
    (Comp.bind (.ret (.var (.succ .zero)))
      (CryptoGames.FSAEAD.Thm5.Costed.corruptSenderBody (I₀ := I₀) ae G 1 1 qSim la)).eval ρ_src = _
  have hsrc :
      (Comp.bind (.ret (.var (.succ .zero)))
        (CryptoGames.FSAEAD.Thm5.Costed.corruptSenderBody (I₀ := I₀) ae G 1 1 qSim la)).eval ρ_src =
      (CryptoGames.FSAEAD.Thm5.Costed.corruptSenderBody (I₀ := I₀) ae G 1 1 qSim la).eval
        (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) := by
    dsimp only [Comp.eval]
    rw [pure_bind]
    rfl
  have hbody := CryptoGames.FSAEAD.Thm5.Costed.corruptSenderBody_eval
    (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
    ae G 1 1 hliftP ρ_src qSim (hp mSlot mSlot la) s hsent
  change Prod.map (Option.map CryptoGames.FSAEAD.Costed.rssDec) id <$>
      (CryptoGames.FSAEAD.Thm5.Costed.corruptSenderBody (I₀ := I₀) ae G 1 1 qSim la).eval
        (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) =
    Prod.map id CryptoGames.FSAEAD.Thm5.Costed.encSt <$>
      (CryptoVerification.E2E.Signed.SessionFS.fsImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp mSlot mSlot la)
        (.inl (.inl (.inl (.inr ()))))).run s at hbody
  have hmap (p : ProbComp _) :
      toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
        (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
        (.prod (.opt CryptoGames.FSAEAD.Costed.rssTy) stT) <$> p =
      Prod.map (Option.map (ReductionDsl.fsSendStV (ℓ := ℓ) (Pt := Pt)))
        (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
          (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) stT) <$>
        (Prod.map (Option.map CryptoGames.FSAEAD.Costed.rssDec) id <$> p) := by
    rw [Functor.map_map]
    refine congrFun (congrArg Functor.map ?_) p
    funext ⟨r1, s'⟩
    rcases r1 with _ | ⟨ck, idx⟩ <;> rfl
  rw [hsrc, hmap, hbody, Functor.map_map]
  refine congrFun (congrArg Functor.map ?_) _
  funext ⟨r1, s'⟩
  rfl

private theorem realDlStep_coinSimEquiv (hinj : Function.Injective encT)
    (qSim mSlot : ℕ) (la : Bool)
    (hdr : Header Pt) (cv : (lctT (ℓ := ℓ) (Pt := Pt)).denote)
    (p : LibsignalMsgPublicPart)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (hrecv : s.1.receiverIdx ≤ s.1.keys.length)
    (htr : s.1.inTransit.length ≤ qSim)
    (hch : s.1.challengesInTransit.length ≤ qSim) :
    CoinSimEquiv (IfaceF).fwdU
      ((realDlStep ℓ Pt C Dh encPt encT idOf lam qSim mSlot mSlot la).eval
        (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
          (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((IfaceF).liftP
        (Prod.map
          (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
          (encHybSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hp mSlot mSlot la)
            (.inl (.inr ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv)))).run s)) := by
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := Iface.withSamp
    (CryptoGames.PRG.Costed.prgIface
      (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
    (CryptoGames.OTCCA.Costed.idealSamplers
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1)
  let I_hyb := I₀.withSamp
    (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))
  let opsC : Option (CryptoGames.FSAEAD.Thm5.SpecialOps
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ProbComp) :=
    some { enc := fun ia _ => ideal ia, dec := fun _ _ => pure none }
  have hliftP : ∀ {α : Type} (p : ProbComp α), I₀.liftP p = (liftM p : ProbComp α) :=
    fun p => (CryptoGames.FSAEAD.Thm5.Costed.liftP_withSamp _ _ p).trans
      (CryptoGames.FSAEAD.Thm5.Costed.prgIface_liftP p)
  have hDec : CryptoGames.FSAEAD.Thm5.Costed.SpecialDecRel (I := I_hyb) ae G 1 1
      (some (fun _ => .ret .none)) opsC := by
    intro Δ ρ' iae
    rfl
  let stT := CryptoGames.FSAEAD.Thm5.Costed.stTy
    (CK := BitVec 256) (MK := BitVec 256)
    (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
  let c0 := ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv
  let ρ_src : Env [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)), stT] :=
    .cons ((hdr, p), (c0.1, c0.2)) (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) .nil)
  have hρ : Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
      (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src =
      .cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
        (.cons (encHybSessSt ℓ Pt s) .nil) := by
    rcases cv with ⟨i, wv⟩
    change Env.cons (t := .prod fig8PubAdT lctT)
        ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p),
         (i, ReductionDsl.wireSaltCtV (ℓ := ℓ) (Pt := Pt)
           (ReductionDsl.wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) wv)))
        (Env.cons (t := hybSessStTy ℓ Pt) (encHybSessSt ℓ Pt s) Env.nil) = _
    rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.wireSaltCtV_wireSaltCtOfV]
  dsimp only [realDlStep]
  rw [← hρ]
  refine (liftFsCoinComp_prgZero_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj _ ρ_src).trans
    (CoinSimEquiv.of_eq ?_)
  refine congrArg (IfaceF).liftP ?_
  change toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
      (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg))) stT) <$>
    (Comp.bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim mSlot mSlot la (some (fun _ => .ret .none)))).eval ρ_src = _
  have hsrc :
      (Comp.bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
        (CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀) ae G 1 1
          maxForwardJumps qSim mSlot mSlot la (some (fun _ => .ret .none)))).eval ρ_src =
      (CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim mSlot mSlot la (some (fun _ => .ret .none))).eval
        (.cons (((hdr, p), (c0.1, c0.2)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) := by
    dsimp only [Comp.eval]
    rw [pure_bind]
    rfl
  have hbody := CryptoGames.FSAEAD.Thm5.Costed.deliverBody_eval ae G 1 1 hliftP ρ_src
    maxForwardJumps qSim mSlot (hp mSlot 0 la) rfl (some (fun _ => .ret .none)) opsC hDec
    (hdr, p) c0.1 c0.2 s hrecv htr hch
  change Prod.map (Option.map CryptoGames.FSAEAD.Costed.rrDecM) id <$>
      (CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim mSlot mSlot la (some (fun _ => .ret .none))).eval
        (.cons (((hdr, p), (c0.1, c0.2)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) =
    Prod.map id CryptoGames.FSAEAD.Thm5.Costed.encSt <$>
      (CryptoGames.FSAEAD.Thm5.multiDeliverH ae G maxForwardJumps (hp mSlot 0 la) mSlot
        (CryptoGames.FSAEAD.Thm5.DG G) opsC ((hdr, p), (c0.1, c0.2))).run s at hbody
  have hmap (p0 : ProbComp _) :
      toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
        (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
        (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg))) stT) <$> p0 =
      Prod.map
        (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
        (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
          (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) stT) <$>
        (Prod.map (Option.map CryptoGames.FSAEAD.Costed.rrDecM) id <$> p0) := by
    rw [Functor.map_map]
    refine congrFun (congrArg Functor.map ?_) p0
    funext ⟨r1, s'⟩
    rcases r1 with _ | (⟨⟩ | ⟨st, _ | m⟩) <;> rfl
  have hc0 : (c0.1, c0.2) = c0 := Prod.eta c0
  rw [hsrc, hmap, hbody, Functor.map_map, hc0]
  have hor := congrFun (multiOraclesWith_specialIdeal_eq_fsImpl
    (CK := BitVec 256) ideal ae G maxForwardJumps mSlot la)
    (.inl (.inr ((hdr, p), c0)))
  change CryptoGames.FSAEAD.Thm5.multiDeliverH ae G maxForwardJumps (hp mSlot 0 la) mSlot
      (CryptoGames.FSAEAD.Thm5.DG G) opsC ((hdr, p), c0) = _ at hor
  rw [hor]
  dsimp only [ae, G, ideal, c0]
  rw [fsImpl_clamped_dl_eq ℓ Pt C encT idOf (hp mSlot mSlot la)
    ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv)]
  refine congrFun (congrArg Functor.map ?_) _
  funext ⟨r1, s'⟩
  rfl

private theorem realIjStep_coinSimEquiv (hinj : Function.Injective encT)
    (qSim mSlot : ℕ) (la : Bool)
    (hdr : Header Pt) (cv : (lctT (ℓ := ℓ) (Pt := Pt)).denote)
    (p : LibsignalMsgPublicPart)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (hrecv : s.1.receiverIdx ≤ s.1.keys.length)
    (htr : s.1.inTransit.length ≤ qSim)
    (hch : s.1.challengesInTransit.length ≤ qSim) :
    CoinSimEquiv (IfaceF).fwdU
      ((realIjStep ℓ Pt C Dh encPt encT idOf lam qSim mSlot mSlot la).eval
        (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
          (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((IfaceF).liftP
        (Prod.map
          (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
          (encHybSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps (hp mSlot mSlot la)
            (.inr ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv))).run s)) := by
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := Iface.withSamp
    (CryptoGames.PRG.Costed.prgIface
      (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
    (CryptoGames.OTCCA.Costed.idealSamplers
      (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1)
  let I_hyb := I₀.withSamp
    (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))
  let opsC : Option (CryptoGames.FSAEAD.Thm5.SpecialOps
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ProbComp) :=
    some { enc := fun ia _ => ideal ia, dec := fun _ _ => pure none }
  have hliftP : ∀ {α : Type} (p : ProbComp α), I₀.liftP p = (liftM p : ProbComp α) :=
    fun p => (CryptoGames.FSAEAD.Thm5.Costed.liftP_withSamp _ _ p).trans
      (CryptoGames.FSAEAD.Thm5.Costed.prgIface_liftP p)
  have hDec : CryptoGames.FSAEAD.Thm5.Costed.SpecialDecRel (I := I_hyb) ae G 1 1
      (some (fun _ => .ret .none)) opsC := by
    intro Δ ρ' iae
    rfl
  let stT := CryptoGames.FSAEAD.Thm5.Costed.stTy
    (CK := BitVec 256) (MK := BitVec 256)
    (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
  let c0 := ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv
  let ρ_src : Env [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)), stT] :=
    .cons ((hdr, p), (c0.1, c0.2)) (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) .nil)
  have hρ : Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
      (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src =
      .cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
        (.cons (encHybSessSt ℓ Pt s) .nil) := by
    rcases cv with ⟨i, wv⟩
    change Env.cons (t := .prod fig8PubAdT lctT)
        ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p),
         (i, ReductionDsl.wireSaltCtV (ℓ := ℓ) (Pt := Pt)
           (ReductionDsl.wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) wv)))
        (Env.cons (t := hybSessStTy ℓ Pt) (encHybSessSt ℓ Pt s) Env.nil) = _
    rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.wireSaltCtV_wireSaltCtOfV]
  dsimp only [realIjStep]
  rw [← hρ]
  refine (liftFsCoinComp_prgZero_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj _ ρ_src).trans
    (CoinSimEquiv.of_eq ?_)
  refine congrArg (IfaceF).liftP ?_
  change toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
      (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg))) stT) <$>
    (Comp.bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim mSlot mSlot la (some (fun _ => .ret .none)))).eval ρ_src = _
  have hsrc :
      (Comp.bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
        (CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀) ae G 1 1
          maxForwardJumps qSim mSlot mSlot la (some (fun _ => .ret .none)))).eval ρ_src =
      (CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim mSlot mSlot la (some (fun _ => .ret .none))).eval
        (.cons (((hdr, p), (c0.1, c0.2)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) := by
    dsimp only [Comp.eval]
    rw [pure_bind]
    rfl
  have hbody := CryptoGames.FSAEAD.Thm5.Costed.injectBody_eval ae G 1 1 hliftP ρ_src
    maxForwardJumps qSim mSlot (hp mSlot 0 la) rfl (some (fun _ => .ret .none)) opsC hDec
    (hdr, p) c0.1 c0.2 s hrecv htr hch
  change Prod.map (Option.map CryptoGames.FSAEAD.Costed.rrDecM) id <$>
      (CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim mSlot mSlot la (some (fun _ => .ret .none))).eval
        (.cons (((hdr, p), (c0.1, c0.2)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) =
    Prod.map id CryptoGames.FSAEAD.Thm5.Costed.encSt <$>
      (CryptoGames.FSAEAD.Thm5.multiInjectH ae G maxForwardJumps (hp mSlot 0 la) mSlot
        (CryptoGames.FSAEAD.Thm5.DG G) opsC ((hdr, p), (c0.1, c0.2))).run s at hbody
  have hmap (p0 : ProbComp _) :
      toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
        (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
        (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg))) stT) <$> p0 =
      Prod.map
        (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
        (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
          (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) stT) <$>
        (Prod.map (Option.map CryptoGames.FSAEAD.Costed.rrDecM) id <$> p0) := by
    rw [Functor.map_map]
    refine congrFun (congrArg Functor.map ?_) p0
    funext ⟨r1, s'⟩
    rcases r1 with _ | (⟨⟩ | ⟨st, _ | m⟩) <;> rfl
  have hc0 : (c0.1, c0.2) = c0 := Prod.eta c0
  rw [hsrc, hmap, hbody, Functor.map_map, hc0]
  have hor := congrFun (multiOraclesWith_specialIdeal_eq_fsImpl
    (CK := BitVec 256) ideal ae G maxForwardJumps mSlot la)
    (.inr ((hdr, p), c0))
  change CryptoGames.FSAEAD.Thm5.multiInjectH ae G maxForwardJumps (hp mSlot 0 la) mSlot
      (CryptoGames.FSAEAD.Thm5.DG G) opsC ((hdr, p), c0) = _ at hor
  rw [hor]
  dsimp only [ae, G, ideal, c0]
  rw [fsImpl_clamped_ij_eq ℓ Pt C encT idOf (hp mSlot mSlot la)
    ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv)]
  refine congrFun (congrArg Functor.map ?_) _
  funext ⟨r1, s'⟩
  rfl

private def RealOptInv (n : ℕ)
    (os : Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)) : Prop :=
  match os with
  | none => True
  | some s => CryptoGames.FSAEAD.Thm5.HInv maxForwardJumps n s.1

/-- Packaged single-step `CoinSimEquiv` for `routerQueryMacro`'s `realStep` (`stage = false` at
`hp 0 0 la` and `stage = true` at `hp N N la` unified via `mSlotR := if stage then N else 0`). -/
private theorem realStep_coinSimEquiv (hinj : Function.Injective encT)
    (stage la : Bool) (qR : ℕ)
    (g : FSAEADTag) (payload : ((IfaceF).dom g).denote)
    (endedPub : Bool)
    (os : Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt))
    (n : ℕ) (hn : n < 2 * qR + 4)
    (hInv : RealOptInv ℓ Pt n os)
    (hNoCr : g ≠ .cr)
    (hShort : ¬ CryptoGames.FSAEAD.encBadMsg
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (C := ℕ × LCt)
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
      ((IfaceF).enc g payload) = true) :
    let N := authHopCutoff maxForwardJumps qR la
    let qSim := 2 * qR + 4
    let mSlotR := if stage then N else 0
    CoinSimEquiv (IfaceF).fwdU
      ((runLazyPubSess ℓ Pt C Dh encPt encT lam
        (initRealSessComp ℓ Pt C Dh encPt encT idOf lam)
        (realTrStep ℓ Pt C Dh encPt encT idOf lam mSlotR mSlotR)
        (realChStep ℓ Pt C Dh encPt encT idOf lam mSlotR mSlotR)
        (realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la)
        (realCrStep ℓ Pt C Dh encPt encT lam)
        (realDlStep ℓ Pt C Dh encPt encT idOf lam qSim mSlotR mSlotR la)
        (realIjStep ℓ Pt C Dh encPt encT idOf lam qSim mSlotR mSlotR la)
        g).eval
        (.cons payload (.cons (endedPub, os.map (encHybSessSt ℓ Pt)) .nil)))
      ((IfaceF).liftP
        ((fun z => ((IfaceF).dec g payload z.1.1, (z.1.2, z.2.map (encHybSessSt ℓ Pt)))) <$>
          (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
            (CryptoVerification.E2E.Signed.SessionRouter.lazyInit
              CryptoVerification.E2E.Signed.SessionFS.fsInit
              (CryptoVerification.E2E.Signed.SessionFS.fsImpl
                (lIdeal C protoSignalCodec ℓ encT)
                (lAeadR C protoSignalCodec ℓ encT idOf)
                (lChainPRG C.F) maxForwardJumps
                (hp mSlotR mSlotR la))))
            ((CryptoGames.FSAEAD.pubRedImpl
              (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
              (AD := Header Pt) (M := Plain ℓ)
              (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
              ((IfaceF).enc g payload)).run endedPub)).run os)) := by
  intro N qSim mSlotR
  refine runLazyPubSess_coinSimEquiv ℓ Pt C Dh encPt encT lam
    (encHybSessSt ℓ Pt)
    (fun s => CryptoGames.FSAEAD.Thm5.HInv maxForwardJumps n s.1)
    CryptoVerification.E2E.Signed.SessionFS.fsInit
    (CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp mSlotR mSlotR la))
    (initRealSessComp ℓ Pt C Dh encPt encT idOf lam)
    (realTrStep ℓ Pt C Dh encPt encT idOf lam mSlotR mSlotR)
    (realChStep ℓ Pt C Dh encPt encT idOf lam mSlotR mSlotR)
    (realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la)
    (realCrStep ℓ Pt C Dh encPt encT lam)
    (realDlStep ℓ Pt C Dh encPt encT idOf lam qSim mSlotR mSlotR la)
    (realIjStep ℓ Pt C Dh encPt encT idOf lam qSim mSlotR mSlotR la)
    g payload endedPub os
    (initRealSessComp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj)
    (fun s hs => (fsInit_hInv ℓ Pt s hs).mono (Nat.zero_le n))
    (fun s hos => by subst hos; exact hInv)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro hdr pv m hg hpay s hs
    subst hg; cases hpay
    have hsh : atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv) = true := by
      dsimp only [fsaeadHeaderIface, CryptoGames.FSAEAD.encBadMsg] at hShort
      simpa using hShort
    exact realTrStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj mSlotR la
      hdr pv m hsh s hs.keys_sent
  · intro hdr pv0 m0 pv1 m1 hg hpay s hs
    subst hg; cases hpay
    have hsh : atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0) = true := by
      dsimp only [fsaeadHeaderIface, CryptoGames.FSAEAD.encBadMsg] at hShort
      rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hShort) with ⟨h0, -⟩
      revert h0
      cases atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0) <;> decide
    exact realChStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj mSlotR la
      hdr pv0 m0 m1 hsh s hs.keys_sent
  · intro _ s hs
    exact realCsStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj qSim mSlotR la s
      (hs.sent_le.trans (Nat.le_of_lt hn))
  · intro hg
    exact (hNoCr hg).elim
  · intro hdr cv p _ _ _ s hs
    exact realDlStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj qSim mSlotR la hdr cv p s
      hs.keys_recv (hs.transit_len.trans (Nat.le_of_lt hn)) (hs.chal_len.trans (Nat.le_of_lt hn))
  · intro hdr cv p _ _ _ s hs
    exact realIjStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj qSim mSlotR la hdr cv p s
      hs.keys_recv (hs.transit_len.trans (Nat.le_of_lt hn)) (hs.chal_len.trans (Nat.le_of_lt hn))

omit [Zero Pt] in
/-- Pure `ProbComp` invariant step advancing `RealOptInv n os` to `RealOptInv (n + 1) z.2` across
one real-session router step. -/
private theorem realStep_support_step
    (stage la : Bool) (qR : ℕ)
    (g : FSAEADTag) (payload : ((IfaceF).dom g).denote)
    (endedPub : Bool)
    (os : Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt))
    (n : ℕ) (hInv : RealOptInv ℓ Pt n os) :
    let N := authHopCutoff maxForwardJumps qR la
    let mSlotR := if stage then N else 0
    ∀ z ∈ support
      ((simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
        (CryptoVerification.E2E.Signed.SessionRouter.lazyInit
          CryptoVerification.E2E.Signed.SessionFS.fsInit
          (CryptoVerification.E2E.Signed.SessionFS.fsImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps
            (hp mSlotR mSlotR la))))
        ((CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
          ((IfaceF).enc g payload)).run endedPub)).run os),
      RealOptInv ℓ Pt (n + 1) z.2 := by
  intro N mSlotR
  refine lazyPubSess_support_step ℓ Pt
    (P_pre := RealOptInv ℓ Pt n)
    (P_post := RealOptInv ℓ Pt (n + 1))
    (Q := fun s => CryptoGames.FSAEAD.Thm5.HInv maxForwardJumps n s.1)
    CryptoVerification.E2E.Signed.SessionFS.fsInit
    (CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp mSlotR mSlotR la))
    g payload endedPub os hInv
    (fun hpre => by
      cases os with
      | none => trivial
      | some s => exact hpre.mono (Nat.le_succ n))
    (fun _ s0 hs0 => (fsInit_hInv ℓ Pt s0 hs0).mono (Nat.zero_le n))
    (fun s hos hpre => hpre)
    (fun q0 s0 hQ r hr => ?_)
  rw [← multiOraclesWith_specialIdeal_eq_fsImpl
    (lIdeal C protoSignalCodec ℓ encT)
    (lAeadR C protoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) maxForwardJumps mSlotR la] at hr
  change r ∈ support
    (((CryptoGames.FSAEAD.Thm5.multiImplWith (m := ProbComp)
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp mSlotR 0 la) mSlotR
      (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
      (some { enc := fun ia _ => lIdeal C protoSignalCodec ℓ encT ia, dec := fun _ _ => pure none }))
      (.inr q0)).run s0) at hr
  exact CryptoGames.FSAEAD.Thm5.multiImplWith_inv
    (T := unifSpec)
    (lIdeal C protoSignalCodec ℓ encT)
    (lAeadR C protoSignalCodec ℓ encT idOf)
    (lChainPRG C.F)
    (hp mSlotR 0 la)
    mSlotR
    (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
    (some { enc := fun ia _ => lIdeal C protoSignalCodec ℓ encT ia, dec := fun _ _ => pure none })
    (.inr q0) s0 hQ r hr

section SlotSideEval

open Computational.Proofs.ReductionDsl.FsAtomicOps
  (eqFig8PubAdExpr_eval eqSlotAdExpr_eval eqPlainExpr_eval eqWireSaltCtExpr_eval eqSaltExpr_eval
   aeadKEncExpr_eval aeadKDecExpr_eval aeadREncExpr_eval aeadRDecExpr_eval
   saltOfSlotAdExpr_eval lIdsExpr_eval lHeaderExpr_eval eqWireSignalHdrExpr_eval fitPlainExpr_eval
   chainGenExpr_eval lPubOfExpr_eval sampleIdealComp_coinSimEquiv sampleMsgKeyComp_coinSimEquiv)

private lemma coinSimEquiv_of_fsMacro {ι : Type} {T : OracleSpec.{0, 0} ι}
    {fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))} {α : Type}
    {oa₁ oa₂ : OracleComp T α}
    (h : Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv fwdU oa₁ oa₂) :
    CoinSimEquiv fwdU oa₁ oa₂ :=
  h

private abbrev encSaltSlotAtom
    (st : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) : (saltSlotStAtomTy ℓ Pt).denote :=
  toVal (swBaseTy (Pt := Pt) (ℓ := ℓ))
    Computational.Proofs.ReductionDsl.FsAtomicBundles.swToDen _
    (CryptoGames.Ratchet.LibsignalInst.Costed.encSaltSlotSt ℓ st)

private abbrev encSlotTbl
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) :
    (Ty.tbl (saltSlotStAtomTy ℓ Pt)).denote :=
  fun i => encSaltSlotAtom ℓ Pt (σ i)

private abbrev encSlotSessSt
    (p : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ×
      (ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)) : (slotSessStTy ℓ Pt).denote :=
  (encHybSessSt ℓ Pt p.1, encSlotTbl ℓ Pt p.2)

private lemma encSlotTbl_update
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) (i : ℕ)
    (st : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) :
    Function.update (encSlotTbl ℓ Pt σ) i (encSaltSlotAtom ℓ Pt st) =
      encSlotTbl ℓ Pt (Function.update σ i st) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [encSlotTbl]
  · simp [encSlotTbl, hk]

private theorem liftFsExpr_eval' {Γ : List (Ty SigA)} {t : Ty SigA}
    (e : Expr (atomicFsOps ℓ Pt C encT) Γ t) (ρ : Env Γ) :
    (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam) e).eval ρ = e.eval ρ :=
  liftFsExpr_eval e ρ

private lemma liftBaseSamp_eval_slot {Γ : List (Ty SigA)}
    (s : UniformSamplerTag ReductionDsl.AtomicBaseUnif)
    (e : Expr OpsF Γ ((ReductionDsl.atomicBaseSamplers ℓ Pt).sDom s))
    (ρ : Env Γ) :
    (liftBaseSamp (Dh := Dh) (encPt := encPt) (lam := lam) s e).eval ρ =
      (IfaceF).liftP ((ReductionDsl.atomicBaseSamplers ℓ Pt).samp s (e.eval ρ)) := by
  rcases s with _ | N | (_ | _ | _) <;> rfl

private def noQuerySlot :
    {Γ : List (Ty SigA)} → {t : Ty SigA} →
      Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .bind c k => noQuerySlot c && noQuerySlot k
  | _, _, .ite _ c d => noQuerySlot c && noQuerySlot d
  | _, _, .caseOpt _ n s => noQuerySlot n && noQuerySlot s
  | _, _, .caseSum _ l r => noQuerySlot l && noQuerySlot r
  | _, _, .sample _ _ => true
  | _, _, .query _ _ => false
  | _, _, .iter _ _ body => noQuerySlot body
  | _, _, .findM _ _ p => noQuerySlot p
  | _, _, .anyM _ _ p => noQuerySlot p
  | _, _, .mapM _ _ f => noQuerySlot f
  | _, _, .consumeFirstM _ _ p _ => noQuerySlot p
  | _, _, .foldM _ _ _ f => noQuerySlot f

private def retagSlotToI2 :
    QueryImpl
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
      (OracleComp
        (unifSpec + CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)))
  | .inl n => (IfaceF).fwdU n
  | .inr (.inl _) => pure none
  | .inr (.inr _) => pure none

private lemma simulateQ_retagSlotToI2_liftP {α : Type} (p : ProbComp α) :
    simulateQ (retagSlotToI2 ℓ Pt) ((slotOtccaTargetIface ℓ Pt).liftP p) = (IfaceF).liftP p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    simp only [ReductionDsl.Iface.liftP, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact bind_congr ih

private lemma simulateQ_iterM {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} (impl : QueryImpl S₁ (OracleComp S₂))
    {α : Type} (f : α → OracleComp S₁ α) (n : ℕ) (a : α) :
    simulateQ impl (ReductionDsl.iterM f n a) =
      ReductionDsl.iterM (fun x => simulateQ impl (f x)) n a := by
  induction n generalizing a with
  | zero => simp [ReductionDsl.iterM]
  | succ n ih =>
    simp only [ReductionDsl.iterM, simulateQ_bind]
    exact bind_congr ih

private lemma simulateQ_findML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} (impl : QueryImpl S₁ (OracleComp S₂))
    {α : Type} (p : α → OracleComp S₁ Bool) (xs : List α) :
    simulateQ impl (ReductionDsl.findML p xs) =
      ReductionDsl.findML (fun x => simulateQ impl (p x)) xs := by
  induction xs with
  | nil => simp [ReductionDsl.findML]
  | cons x xs ih =>
    simp only [ReductionDsl.findML, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b <;> simp [ih]

private lemma simulateQ_anyML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} (impl : QueryImpl S₁ (OracleComp S₂))
    {α : Type} (p : α → OracleComp S₁ Bool) (xs : List α) :
    simulateQ impl (ReductionDsl.anyML p xs) =
      ReductionDsl.anyML (fun x => simulateQ impl (p x)) xs := by
  induction xs with
  | nil => simp [ReductionDsl.anyML]
  | cons x xs ih =>
    simp only [ReductionDsl.anyML, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b <;> simp [ih]

private lemma simulateQ_mapML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} (impl : QueryImpl S₁ (OracleComp S₂))
    {α β : Type} (f : α → OracleComp S₁ β) (xs : List α) :
    simulateQ impl (ReductionDsl.mapML f xs) =
      ReductionDsl.mapML (fun x => simulateQ impl (f x)) xs := by
  induction xs with
  | nil => simp [ReductionDsl.mapML]
  | cons x xs ih =>
    simp only [ReductionDsl.mapML, simulateQ_bind]
    refine bind_congr fun y => ?_
    simp [ih]

private lemma simulateQ_consumeFirstML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} (impl : QueryImpl S₁ (OracleComp S₂))
    {α : Type} (p : α → OracleComp S₁ Bool) (mk : α → α) (xs : List α) :
    simulateQ impl (ReductionDsl.consumeFirstML p mk xs) =
      ReductionDsl.consumeFirstML (fun x => simulateQ impl (p x)) mk xs := by
  induction xs with
  | nil => simp [ReductionDsl.consumeFirstML]
  | cons x xs ih =>
    simp only [ReductionDsl.consumeFirstML, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b <;> simp [ih]

private lemma simulateQ_foldML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} (impl : QueryImpl S₁ (OracleComp S₂))
    {α β : Type} (f : α → β → OracleComp S₁ β) (xs : List α) (b : β) :
    simulateQ impl (ReductionDsl.foldML f b xs) =
      ReductionDsl.foldML (fun x acc => simulateQ impl (f x acc)) b xs := by
  induction xs generalizing b with
  | nil => simp [ReductionDsl.foldML]
  | cons x xs ih =>
    simp only [ReductionDsl.foldML, simulateQ_bind]
    exact bind_congr ih

private lemma liftNoQuerySlotComp_eval_eq_retag
    (dflt : Expr OpsF [] (.opt wireSaltCtT)) (dfltM : Expr OpsF [] (.opt PlainT))
    {Γ : List (Ty SigA)} {t : Ty SigA}
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t)
    (hno : noQuerySlot ℓ Pt C encT c = true) (ρ : Env Γ) :
    (liftNoQuerySlotComp (Dh := Dh) (encPt := encPt) (lam := lam) dflt dfltM c).eval ρ =
      simulateQ (retagSlotToI2 ℓ Pt) (c.eval ρ) := by
  induction c with
  | ret e =>
    simp [liftNoQuerySlotComp, Comp.eval, liftFsExpr_eval']
  | bind c k ihc ihk =>
    simp only [noQuerySlot, Bool.and_eq_true] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, simulateQ_bind, ihc hno.1 ρ]
    exact bind_congr fun x => ihk hno.2 _
  | ite b c d ihc ihd =>
    simp only [noQuerySlot, Bool.and_eq_true] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, liftFsExpr_eval']
    cases b.eval ρ <;> simp [ihc hno.1, ihd hno.2]
  | caseOpt e n s ihn ihs =>
    simp only [noQuerySlot, Bool.and_eq_true] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, liftFsExpr_eval']
    cases e.eval ρ <;> simp [ihn hno.1, ihs hno.2]
  | caseSum e l r ihl ihr =>
    simp only [noQuerySlot, Bool.and_eq_true] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, liftFsExpr_eval']
    cases e.eval ρ <;> simp [ihl hno.1, ihr hno.2]
  | sample s e =>
    simp only [liftNoQuerySlotComp, liftBaseSamp_eval_slot, Comp.eval,
      simulateQ_retagSlotToI2_liftP]
  | query g _ =>
    simp [noQuerySlot] at hno
  | iter n e body ih =>
    simp only [noQuerySlot] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, simulateQ_iterM]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext acc; exact ih hno _
  | findM K l p ih =>
    simp only [noQuerySlot] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, simulateQ_findML]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext x; exact ih hno _
  | anyM K l p ih =>
    simp only [noQuerySlot] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, simulateQ_anyML]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext x; exact ih hno _
  | mapM K l f ih =>
    simp only [noQuerySlot] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, simulateQ_mapML]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext x; exact ih hno _
  | consumeFirstM K l p mk ih =>
    simp only [noQuerySlot] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, simulateQ_consumeFirstML]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1
    · funext x; exact ih hno _
    · funext x; exact liftFsExpr_eval' ℓ Pt C Dh encPt encT lam mk _
  | foldM K l z f ih =>
    simp only [noQuerySlot] at hno
    simp only [liftNoQuerySlotComp, Comp.eval, simulateQ_foldML]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam, liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext x acc; exact ih hno _

private lemma simulateQ_comp {ι₁ ι₂ : Type}
    {S₁ : OracleSpec.{0, 0} ι₁} {S₂ : OracleSpec.{0, 0} ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (f₂ : QueryImpl S₂ m) (f₁ : QueryImpl S₁ (OracleComp S₂))
    {α : Type} (oa : OracleComp S₁ α) :
    simulateQ f₂ (simulateQ f₁ oa) = simulateQ (fun i => simulateQ f₂ (f₁ i)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => rfl
  | query_bind i _ ih =>
    simp [simulateQ_bind, simulateQ_query, ih]

private lemma retagSlotToI2_coinSimEquiv_liftP {α : Type}
    (oa : OracleComp
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α)
    (p : ProbComp α)
    (h : CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU oa
      ((slotOtccaTargetIface ℓ Pt).liftP p)) :
    CoinSimEquiv (IfaceF).fwdU (simulateQ (retagSlotToI2 ℓ Pt) oa) ((IfaceF).liftP p) := by
  refine ⟨fun {σ} impl hv s => ?_⟩
  let implSlot : QueryImpl
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) (StateT σ ProbComp)
    | .inl n => impl (.inl n)
    | .inr (.inl _) => pure none
    | .inr (.inr _) => pure none
  have hvSlot : Computational.Proofs.ReductionDsl.FsAtomicMacros.ValidCoinSim
      (slotOtccaTargetIface ℓ Pt).fwdU implSlot := ⟨hv.coin_eq⟩
  have hcomp : simulateQ impl (simulateQ (retagSlotToI2 ℓ Pt) oa) = simulateQ implSlot oa := by
    rw [simulateQ_comp]
    congr 1; funext q
    rcases q with n | (_ | _) <;> simp [retagSlotToI2, implSlot]
  rw [hcomp, ← simulateQ_retagSlotToI2_liftP ℓ Pt p]
  have hcomp2 : simulateQ impl (simulateQ (retagSlotToI2 ℓ Pt)
      ((slotOtccaTargetIface ℓ Pt).liftP p)) =
      simulateQ implSlot ((slotOtccaTargetIface ℓ Pt).liftP p) := by
    rw [simulateQ_comp]
    congr 1; funext q
    rcases q with n | (_ | _) <;> simp [retagSlotToI2, implSlot]
  rw [hcomp2]
  exact h.run_eq implSlot hvSlot s

private theorem liftFsSlotComp_eval {Γ : List (Ty SigA)} {t : Ty SigA}
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) (ρ : Env Γ) :
    (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c).eval ρ = c.eval ρ := by
  induction c with
  | ret e =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
  | bind c k ihc ihk =>
    simp only [liftFsSlotComp, Comp.eval, ihc]
    exact bind_congr fun x => ihk _
  | ite b c d ihc ihd =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    cases b.eval ρ <;> simp [ihc, ihd]
  | caseOpt e n s ihn ihs =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    cases e.eval ρ <;> simp [ihn, ihs]
  | caseSum e l r ihl ihr =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    cases e.eval ρ <;> simp [ihl, ihr]
  | sample s e =>
    simp only [liftFsSlotComp, Comp.eval]
  | query g e =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
  | iter n e body ih =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext acc; exact ih _
  | findM K l p ih =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext x; exact ih _
  | anyM K l p ih =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext x; exact ih _
  | mapM K l f ih =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext x; exact ih _
  | consumeFirstM K l p mk ih =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1
    · funext x; exact ih _
    · funext x; exact liftFsExpr_eval' ℓ Pt C Dh encPt encT lam mk _
  | foldM K l z f ih =>
    simp only [liftFsSlotComp, Comp.eval]
    rw [liftFsExpr_eval' ℓ Pt C Dh encPt encT lam, liftFsExpr_eval' ℓ Pt C Dh encPt encT lam]
    congr 1; funext x acc; exact ih _

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma slotOtccaTargetIface_liftP_eq_liftM {α : Type} (p : ProbComp α) :
    (slotOtccaTargetIface ℓ Pt).liftP p =
      (liftM p : OracleComp
        (unifSpec + CryptoGames.AEADScheme.otccaSpec
          (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    simp only [ReductionDsl.Iface.liftP, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, monadLift_bind]
    refine bind_congr fun x => ih x

private lemma iface_liftP_map {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α β : Type} (f : α → β) (p : ProbComp α) :
    f <$> I.liftP p = I.liftP (f <$> p) := by
  simp only [ReductionDsl.Iface.liftP, map_eq_bind_pure_comp, Function.comp_def,
    simulateQ_bind, simulateQ_pure]

private lemma iface_liftP_pure {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α : Type} (a : α) :
    I.liftP (pure a) = pure a := rfl

private lemma iface_liftP_bind {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α β : Type} (p : ProbComp α) (k : α → ProbComp β) :
    (I.liftP p >>= fun a => I.liftP (k a)) = I.liftP (p >>= k) := by
  simp only [ReductionDsl.Iface.liftP, simulateQ_bind]

private def hasNoQuery {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .bind c k => hasNoQuery c && hasNoQuery k
  | _, _, .ite _ c d => hasNoQuery c && hasNoQuery d
  | _, _, .caseOpt _ n s => hasNoQuery n && hasNoQuery s
  | _, _, .caseSum _ l r => hasNoQuery l && hasNoQuery r
  | _, _, .sample _ _ => true
  | _, _, .query _ _ => false
  | _, _, .iter _ _ body => hasNoQuery body
  | _, _, .findM _ _ p => hasNoQuery p
  | _, _, .anyM _ _ p => hasNoQuery p
  | _, _, .mapM _ _ f => hasNoQuery f
  | _, _, .consumeFirstM _ _ p _ => hasNoQuery p
  | _, _, .foldM _ _ _ f => hasNoQuery f

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma noQuerySlot_renameM {Γ Δ : List (Ty SigA)} {t : Ty SigA}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u)
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    noQuerySlot ℓ Pt C encT (Comp.renameM ξ c) = noQuerySlot ℓ Pt C encT c := by
  induction c generalizing Δ with
  | ret _ => rfl
  | bind c k ihc ihk => simp [Comp.renameM, noQuerySlot, ihc, ihk]
  | ite _ c d ihc ihd => simp [Comp.renameM, noQuerySlot, ihc, ihd]
  | caseOpt _ n s ihn ihs => simp [Comp.renameM, noQuerySlot, ihn, ihs]
  | caseSum _ l r ihl ihr => simp [Comp.renameM, noQuerySlot, ihl, ihr]
  | sample _ _ => rfl
  | query _ _ => rfl
  | iter _ _ body ih => simp [Comp.renameM, noQuerySlot, ih]
  | findM _ _ p ih => simp [Comp.renameM, noQuerySlot, ih]
  | anyM _ _ p ih => simp [Comp.renameM, noQuerySlot, ih]
  | mapM _ _ f ih => simp [Comp.renameM, noQuerySlot, ih]
  | consumeFirstM _ _ p _ ih => simp [Comp.renameM, noQuerySlot, ih]
  | foldM _ _ _ f ih => simp [Comp.renameM, noQuerySlot, ih]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma noQuerySlot_compilePureComp
    {S₁ : Sig} {O₁ : Ops S₁}
    {I₁ : Iface S₁
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)}
    (M : Computational.Proofs.ReductionDsl.FsAtomicMacros.PureMacroBundle
      O₁ (atomicFsOps ℓ Pt C encT) I₁ (slotOtccaTargetIface ℓ Pt))
    (hsamp : ∀ s, noQuerySlot ℓ Pt C encT (M.sampMacro s) = true)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t)
    (hc : hasNoQuery c = true) :
    noQuerySlot ℓ Pt C encT (compilePureComp M c) = true := by
  induction c with
  | ret _ => rfl
  | bind c k ihc ihk =>
    simp only [hasNoQuery, Bool.and_eq_true] at hc
    simp [compilePureComp, noQuerySlot, ihc hc.1, ihk hc.2]
  | ite _ c d ihc ihd =>
    simp only [hasNoQuery, Bool.and_eq_true] at hc
    simp [compilePureComp, noQuerySlot, ihc hc.1, ihd hc.2]
  | caseOpt _ n s ihn ihs =>
    simp only [hasNoQuery, Bool.and_eq_true] at hc
    simp [compilePureComp, noQuerySlot, ihn hc.1, ihs hc.2]
  | caseSum _ l r ihl ihr =>
    simp only [hasNoQuery, Bool.and_eq_true] at hc
    simp [compilePureComp, noQuerySlot, ihl hc.1, ihr hc.2]
  | sample s _ =>
    simp [compilePureComp, noQuerySlot, noQuerySlot_renameM, hsamp s]
  | query _ _ => simp [hasNoQuery] at hc
  | iter _ _ body ih => simp [compilePureComp, noQuerySlot, ih hc]
  | findM _ _ p ih => simp [compilePureComp, noQuerySlot, ih hc]
  | anyM _ _ p ih => simp [compilePureComp, noQuerySlot, ih hc]
  | mapM _ _ f ih => simp [compilePureComp, noQuerySlot, ih hc]
  | consumeFirstM _ _ p _ ih => simp [compilePureComp, noQuerySlot, ih hc]
  | foldM _ _ _ f ih => simp [compilePureComp, noQuerySlot, ih hc]

omit [Zero Pt] [SampleableType Pt] in
private lemma swOpMacro_eval' (hinj : Function.Injective encT) (o) (x) :
    (Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro (Pt := Pt) C ℓ encT idOf o).eval
      (.cons (toVal swBaseTy swToDen _ x) .nil) =
    toVal swBaseTy swToDen _
      ((CryptoGames.AEAD.Costed.saltWireOps C clampedProtoSignalCodec ℓ encT idOf 1).eval o x) := by
  rcases o with (_ | _ | _ | _ | _ | _ | _) | ((_ | _ | _ | _ | _ | _ | _) | (_ | _ | _ | _))
  · rcases x with ⟨mk, ⟨i, a⟩, m⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.libsignalAeadKeyIndexedAd, id]
    rw [aeadKEncExpr_eval]
    simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV, wireSaltCtV, salt32V]
  · rcases x with ⟨mk, ⟨i, a⟩, e⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.libsignalAeadKeyIndexedAd, id]
    rw [aeadKDecExpr_eval]
    have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
      simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    have hct : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((e.1.1, e.1.2), salt32V e.2) = e := by
      rcases e with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    simp only [hsl, hct]
    cases (CryptoGames.Ratchet.LibsignalInst.lAeadK C clampedProtoSignalCodec ℓ encT idOf).dec mk ((i, a.1), a.2) e <;> rfl
  · rcases x with ⟨i, a⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [saltOfSlotAdExpr_eval]
    simp [Expr.eval, slotAdOfV, fig8PubAdOfV_fig8PubAdV, salt32V]
  · rcases x with ⟨⟨i₁, a₁⟩, ⟨i₂, a₂⟩⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqSlotAdExpr_eval ℓ Pt C encT hinj]
    simp only [Expr.eval, env_get_zero, slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    by_cases h : (i₁, a₁) = (i₂, a₂) <;> simp [h]
  · rcases x with ⟨m₁, m₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqPlainExpr_eval]; simp only [Expr.eval, env_get_zero]
    by_cases h : m₁ = m₂ <;> simp [h]
  · rcases x with ⟨c₁, c₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqWireSaltCtExpr_eval]
    have hc₁ : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((c₁.1.1, c₁.1.2), salt32V c₁.2) = c₁ := by
      rcases c₁ with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    have hc₂ : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((c₂.1.1, c₂.1.2), salt32V c₂.2) = c₂ := by
      rcases c₂ with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    simp only [Expr.eval, env_get_zero, hc₁, hc₂]
    by_cases h : c₁ = c₂ <;> simp [h]
  · rcases x with ⟨s₁, s₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqSaltExpr_eval]; simp [Expr.eval, salt32OfV_salt32V]
  · rcases x with ⟨seed, ⟨i, a⟩, m⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [aeadREncExpr_eval]
    simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV, wireSaltCtV, salt32V]
  · rcases x with ⟨seed, ⟨i, a⟩, e⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [aeadRDecExpr_eval]
    have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
      simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    have hct : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((e.1.1, e.1.2), salt32V e.2) = e := by
      rcases e with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    simp only [hsl, hct]
    cases (lAeadR C clampedProtoSignalCodec ℓ encT idOf).dec seed (i, a) e <;> rfl
  · rcases x with ⟨i, a⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [saltOfSlotAdExpr_eval]
    simp [Expr.eval, slotAdOfV, fig8PubAdOfV_fig8PubAdV, salt32V]
  · rcases x with ⟨⟨i₁, a₁⟩, ⟨i₂, a₂⟩⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqSlotAdExpr_eval ℓ Pt C encT hinj]
    simp only [Expr.eval, env_get_zero, slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    by_cases h : (i₁, a₁) = (i₂, a₂) <;> simp [h]
  · rcases x with ⟨m₁, m₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqPlainExpr_eval]; simp only [Expr.eval, env_get_zero]
    by_cases h : m₁ = m₂ <;> simp [h]
  · rcases x with ⟨c₁, c₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqWireSaltCtExpr_eval]
    have hc₁ : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((c₁.1.1, c₁.1.2), salt32V c₁.2) = c₁ := by
      rcases c₁ with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    have hc₂ : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((c₂.1.1, c₂.1.2), salt32V c₂.2) = c₂ := by
      rcases c₂ with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    simp only [Expr.eval, env_get_zero, hc₁, hc₂]
    by_cases h : c₁ = c₂ <;> simp [h]
  · rcases x with ⟨s₁, s₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqSaltExpr_eval]; simp [Expr.eval, salt32OfV_salt32V]
  · rcases x with ⟨i, ⟨t, T?⟩, pub⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      Ops.sum, Sum.elim, CryptoGames.AEAD.Costed.wireOps, fig8PubAdV, id]
    rw [lIdsExpr_eval]; simp [Expr.eval]
  · rcases x with ⟨i, a⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, CryptoGames.AEAD.Costed.slotAdTy,
      Ops.sum, Sum.elim, CryptoGames.AEAD.Costed.wireOps, id]
    rw [lHeaderExpr_eval]; simp [Expr.eval, slotAdOfV, fig8PubAdOfV_fig8PubAdV]
  · rcases x with ⟨h₁, h₂⟩
    dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, id]
    rw [eqWireSignalHdrExpr_eval]
    simp only [Expr.eval, env_get_zero, wireSignalHdrOfV_wireSignalHdrV]
  · dsimp only [Computational.Proofs.ReductionDsl.FsAtomicBundles.swOpMacro, swBaseTy, swToDen,
      mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, id]
    rw [fitPlainExpr_eval]; rfl

omit [Zero Pt] [SampleableType Pt] in
private lemma slotSwSamp_coinSimEquiv' (s) (x) :
    Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).eval
        (.cons (toVal swBaseTy swToDen
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).smp.sDom s) x) .nil))
      (toVal (swBaseTy (Pt := Pt) (ℓ := ℓ)) swToDen
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).smp.sTy s) <$>
        (CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).liftP
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).smp.samp s x)) := by
  cases s with
  | inl u =>
    cases u; rcases x with ⟨i, a⟩
    refine (sampleIdealComp_coinSimEquiv ℓ Pt C encT (I := slotOtccaTargetIface ℓ Pt)
      (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b _ => by cases b <;> rfl) (i, fig8PubAdV a)).trans
      (Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv.of_eq ?_)
    have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
      simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    rw [hsl]
    dsimp only [slotSwMacroBundle, CryptoGames.AEAD.Costed.slotOtccaIface, ReductionDsl.Iface.withSamp,
      ReductionDsl.Samplers.sum, CryptoGames.OTCCA.Costed.otccaIface,
      CryptoGames.OTCCA.Costed.idealSamplers, slotOtccaTargetIface, ReductionDsl.Iface.liftP,
      CryptoGames.AEAD.Costed.lctTy, CryptoGames.AEAD.Costed.wireTagTy, swBaseTy, mapTy, toVal,
      swToDen, wireSaltCtV, salt32V]
    rfl
  | inr t =>
    rcases t with _ | N | (_ | _)
    · exact Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv.of_eq (by
        simp [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
          CryptoGames.OTCCA.Costed.otccaIface, ReductionDsl.Iface.withSamp,
          ReductionDsl.Samplers.sum, ReductionDsl.Iface.liftP, unifSamplers,
          Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort, swBaseTy, mapTy, toVal])
    · exact Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv.of_eq (by
        simp [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
          CryptoGames.OTCCA.Costed.otccaIface, ReductionDsl.Iface.withSamp,
          ReductionDsl.Samplers.sum, ReductionDsl.Iface.liftP, unifSamplers,
          Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort, swBaseTy, mapTy, toVal])
    · refine (sampleMsgKeyComp_coinSimEquiv ℓ Pt C encT (I := slotOtccaTargetIface ℓ Pt)
        (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
        (fun b _ => by cases b <;> rfl) _).trans
        (Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv.of_eq ?_)
      dsimp only [slotSwMacroBundle, CryptoGames.AEAD.Costed.slotOtccaIface,
        ReductionDsl.Iface.withSamp, ReductionDsl.Samplers.sum,
        CryptoGames.OTCCA.Costed.otccaIface, slotOtccaTargetIface, ReductionDsl.Iface.liftP,
        unifSamplers, CryptoGames.AEAD.Costed.slotKeySort, swBaseTy, mapTy, toVal, swToDen]
      rfl
    · exact Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv.of_eq (by
        dsimp only [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
          CryptoGames.AEAD.Costed.saltWireSig, CryptoGames.AEAD.Costed.SaltWireSort.den,
          CryptoGames.OTCCA.Costed.otccaIface, ReductionDsl.Iface.withSamp,
          ReductionDsl.Samplers.sum, Sum.elim, ReductionDsl.Iface.liftP,
          unifSamplers, CryptoGames.AEAD.Costed.slotKeySort, Comp.eval,
          atomicBaseSamplers, AtomicBaseUnif.sort, AtomicSort.den, swBaseTy, mapTy, toVal, swToDen]
        simp only [id_map]; rfl)

omit [Zero Pt] [SampleableType Pt] in
private lemma slotSwQuery_coinSimEquiv' (g) (x) :
    Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).eval
        (.cons (toVal swBaseTy swToDen
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).dom g) x) .nil))
      (toVal (swBaseTy (Pt := Pt) (ℓ := ℓ)) swToDen
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).cod g) <$>
        ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).dec g x <$>
          liftM ((unifSpec + CryptoGames.AEADScheme.otccaSpec _ _ _).query
            ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).enc g x)))) := by
  cases g
  · apply Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv.of_eq
    dsimp only [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
      CryptoGames.AEAD.Costed.saltWireSig, CryptoGames.AEAD.Costed.SaltWireSort.den,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, ReductionDsl.Iface.withSamp,
      CryptoGames.OTCCA.Costed.otccaIface, Ty.denote, Comp.eval, Expr.eval, swBaseTy, mapTy,
      toVal, swToDen, slotAdOfV, id] at x ⊢
    rcases x with ⟨⟨i, a⟩, m⟩
    simp only [env_get_zero, Functor.map_map]
    rw [fig8PubAdOfV_fig8PubAdV]
    congr 1
  · apply Computational.Proofs.ReductionDsl.FsAtomicMacros.CoinSimEquiv.of_eq
    dsimp only [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
      CryptoGames.AEAD.Costed.saltWireSig, CryptoGames.AEAD.Costed.SaltWireSort.den,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, ReductionDsl.Iface.withSamp,
      CryptoGames.OTCCA.Costed.otccaIface, Ty.denote, Comp.eval, Expr.eval, swBaseTy, mapTy,
      toVal, swToDen, slotAdOfV, wireSaltCtOfV, id] at x ⊢
    rcases x with ⟨⟨i, a⟩, ⟨⟨w, tg⟩, s⟩⟩
    simp only [env_get_zero, Functor.map_map]
    rw [fig8PubAdOfV_fig8PubAdV, salt32OfV_salt32V]
    congr 1; funext r
    cases r <;> rfl

omit [Zero Pt] [SampleableType Pt] in
private lemma noQuerySlot_slotSwSamp (s) :
    noQuerySlot ℓ Pt C encT ((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s) = true := by
  rcases s with ⟨⟩ | (_ | N | (_ | _)) <;> rfl

private abbrev slotSaltImplByNf (nf : Bool) :
    QueryImpl
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
      (StateT (CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) ProbComp) :=
  if nf then
    CryptoGames.Ratchet.LibsignalInst.slotSaltImplNF C clampedProtoSignalCodec ℓ encT idOf false
  else
    CryptoGames.Ratchet.LibsignalInst.slotSaltImpl C clampedProtoSignalCodec ℓ encT idOf false

omit [Zero Pt] [SampleableType Pt] in
private lemma slotSaltImplByNf_enc_eq (nf : Bool)
    (h : ℕ × (Header Pt × LibsignalMsgPublicPart)) (m : Plain ℓ)
    (st : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) :
    (slotSaltImplByNf ℓ Pt C encT idOf nf (.inr (.inl (h, m)))).run st =
      (CryptoGames.Ratchet.LibsignalInst.slotSaltImpl C clampedProtoSignalCodec ℓ encT idOf false
        (.inr (.inl (h, m)))).run st := by
  cases nf <;> rfl

omit [Zero Pt] [SampleableType Pt] in
private lemma slotSaltImplByNf_support_length (nf : Bool)
    (t : (unifSpec + CryptoGames.AEADScheme.otccaSpec
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt).Domain)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) :
    ∀ z ∈ support ((CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf) t).run σ),
      ∀ i, (z.2 i).table.length ≤ (σ i).table.length + (if t.isRight then 1 else 0) := by
  intro z hz i
  rcases t with n | q
  · simp only [CryptoGames.FSAEAD.Thm5.slotLift_inl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, StateT.run_monadLift, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨_, -, rfl⟩ := hz
    simp
  · simp only [CryptoGames.FSAEAD.Thm5.slotLift_inr, Sum.isRight_inr, ↓reduceIte] at hz ⊢
    rcases q with ⟨h, m⟩ | ⟨h, e⟩
    · simp only [CryptoGames.FSAEAD.Thm5.slotLiftOtcca, StateT.run_mk,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s'⟩, hs', rfl⟩ := hz
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        cases nf
        · exact CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltImpl_support_length
            C clampedProtoSignalCodec ℓ encT idOf false (.inl (h, m)) (σ h.1) (r, s') hs'
        · exact CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltImplNF_support_length
            C clampedProtoSignalCodec ℓ encT idOf false (.inl (h, m)) (σ h.1) (r, s') hs'
      · simp [Function.update_of_ne hi]
    · simp only [CryptoGames.FSAEAD.Thm5.slotLiftOtcca, StateT.run_mk,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s'⟩, hs', rfl⟩ := hz
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        cases nf
        · exact CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltImpl_support_length
            C clampedProtoSignalCodec ℓ encT idOf false (.inr (h, e)) (σ h.1) (r, s') hs'
        · exact CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltImplNF_support_length
            C clampedProtoSignalCodec ℓ encT idOf false (.inr (h, e)) (σ h.1) (r, s') hs'
      · simp [Function.update_of_ne hi]

private def qSlotRaw (nf : Bool) (qSim : ℕ) :
    QueryImpl
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
      (StateT ((Ty.tbl (saltSlotStAtomTy ℓ Pt)).denote)
        (OracleComp
          (unifSpec + CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
            (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt))))
  | .inl n => StateT.lift ((IfaceF).fwdU n)
  | .inr (.inl (h, m)) => StateT.mk fun tbl =>
      Prod.map (Option.map (wireSaltCtOfV (ℓ := ℓ) (Pt := Pt))) id <$>
        (slotOtccaImpl ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim .enc).eval
          (.cons ((h.1, fig8PubAdV (ℓ := ℓ) (Pt := Pt) h.2), m) (.cons tbl .nil))
  | .inr (.inr (h, e)) => StateT.mk fun tbl =>
      (slotOtccaImpl ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim .dec).eval
        (.cons ((h.1, fig8PubAdV (ℓ := ℓ) (Pt := Pt) h.2), wireSaltCtV (ℓ := ℓ) (Pt := Pt) e)
          (.cons tbl .nil))

private theorem slotOtccaImpl_coinSimEquiv (hinj : Function.Injective encT)
    (nf : Bool) (qSim : ℕ)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (hσ : ∀ i, (σ i).table.length ≤ qSim)
    (q : (CryptoGames.AEADScheme.otccaSpec
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt).Domain) :
    CoinSimEquiv (IfaceF).fwdU
      ((qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim (.inr q)).run
        (encSlotTbl ℓ Pt σ))
      ((IfaceF).liftP
        (Prod.map id (encSlotTbl ℓ Pt) <$>
          (CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf) (.inr q)).run σ)) := by
  rcases q with ⟨h, m⟩ | ⟨h, e⟩
  · dsimp only [qSlotRaw, slotOtccaImpl, StateT.run_mk, Comp.eval, Expr.eval]
    simp only [env_get_zero, env_get_succ, pure_bind]
    have hren :
        ((liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
          (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
            (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC (Γ := [])
              C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim))).renameM renId2).eval
          (Env.cons (t := saltSlotStAtomTy ℓ Pt) (encSlotTbl ℓ Pt σ h.1)
            (Env.cons (t := (slotOtccaTargetIface ℓ Pt).dom .enc)
              ((h.1, fig8PubAdV (ℓ := ℓ) (Pt := Pt) h.2), m)
              (Env.cons (t := .tbl (saltSlotStAtomTy ℓ Pt)) (encSlotTbl ℓ Pt σ) .nil))) =
        (liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
          (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
            (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC (Γ := [])
              C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim))).eval
          (.cons (encSaltSlotAtom ℓ Pt (σ h.1))
            (.cons ((h.1, fig8PubAdV (ℓ := ℓ) (Pt := Pt) h.2), m) .nil)) := by
      exact ReductionDsl.Comp.renameM_eval _ fun ⦃u⦄ v => by
        rcases v with _ | (_ | v)
        · rfl
        · rfl
        · exact nomatch v
    change (Prod.map (Option.map wireSaltCtOfV) id <$>
        (((liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
          (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
            (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC (Γ := [])
              C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim))).renameM renId2).eval
          (Env.cons (t := saltSlotStAtomTy ℓ Pt) (encSlotTbl ℓ Pt σ h.1)
            (Env.cons (t := (slotOtccaTargetIface ℓ Pt).dom .enc)
              ((h.1, fig8PubAdV (ℓ := ℓ) (Pt := Pt) h.2), m)
              (Env.cons (t := .tbl (saltSlotStAtomTy ℓ Pt)) (encSlotTbl ℓ Pt σ) .nil))) >>= _))
      |> fun lhs => CoinSimEquiv (IfaceF).fwdU lhs _
    rw [hren, liftNoQuerySlotComp_eval_eq_retag ℓ Pt C Dh encPt encT lam .none .none _
      (noQuerySlot_compilePureComp ℓ Pt C encT (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (noQuerySlot_slotSwSamp ℓ Pt C encT idOf) _ rfl)]
    have hcomp :
        CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
          ((compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
            (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC (Γ := [])
              C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim)).eval
            (mapPureEnv swBaseTy swToDen
              (.cons (CryptoGames.Ratchet.LibsignalInst.Costed.encSaltSlotSt ℓ (σ h.1))
                (.cons (h, m) .nil))))
          ((slotOtccaTargetIface ℓ Pt).liftP
            (toVal swBaseTy swToDen
              (.prod (.opt (CryptoGames.AEAD.Costed.lctTy Pt ℓ))
                (CryptoGames.Ratchet.LibsignalInst.Costed.saltSlotStTy (Pt := Pt) ℓ)) <$>
              (Prod.map id (CryptoGames.Ratchet.LibsignalInst.Costed.encSaltSlotSt ℓ) <$>
                (slotSaltImplByNf ℓ Pt C encT idOf nf (.inr (.inl (h, m)))).run (σ h.1)))) := by
      refine (coinSimEquiv_of_fsMacro (compilePureComp_coinSimEquiv
        (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (swOpMacro_eval' ℓ Pt C encT idOf hinj)
        (slotSwSamp_coinSimEquiv' ℓ Pt C encT idOf)
        (slotSwQuery_coinSimEquiv' ℓ Pt C encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC (Γ := [])
          C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim)
        (.cons (CryptoGames.Ratchet.LibsignalInst.Costed.encSaltSlotSt ℓ (σ h.1))
          (.cons (h, m) .nil)))).trans (CoinSimEquiv.of_eq ?_)
      rw [CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC_eval
        C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim (σ h.1) (hσ h.1) h m .nil,
        ← slotSaltImplByNf_enc_eq ℓ Pt C encT idOf nf h m (σ h.1),
        ← slotOtccaTargetIface_liftP_eq_liftM ℓ Pt, iface_liftP_map]
      rfl
    have hretag := retagSlotToI2_coinSimEquiv_liftP ℓ Pt _ _ hcomp
    refine (CoinSimEquiv.map _ (CoinSimEquiv.bind hretag fun _ => CoinSimEquiv.refl _)).trans
      (CoinSimEquiv.of_eq ?_)
    simp only [CryptoGames.FSAEAD.Thm5.slotLift_inr, CryptoGames.FSAEAD.Thm5.slotLiftOtcca,
      StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      ← iface_liftP_pure (IfaceF), iface_liftP_bind]
    congr 1
    erw [bind_map_left, bind_assoc]
    simp only [pure_bind]
    refine bind_congr fun rs => ?_
    rcases rs with ⟨r, s'⟩
    dsimp only [Comp.eval, Expr.eval, Prod.map, id_eq]
    congr 1; apply Prod.ext
    · erw [env_get_zero]
      cases r with
      | none => rfl
      | some c =>
        rcases c with ⟨⟨w, tg⟩, s⟩
        simp [CryptoGames.AEAD.Costed.lctTy, CryptoGames.AEAD.Costed.wireTagTy,
          swBaseTy, mapTy, toVal, swToDen, wireSaltCtOfV, salt32OfV_salt32V]
    · erw [env_get_zero]
      funext j; by_cases hj : j = h.1 <;> simp [hj, encSlotTbl, encSaltSlotAtom, toVal]
  · dsimp only [qSlotRaw, slotOtccaImpl, StateT.run_mk, Comp.eval, Expr.eval]
    simp only [env_get_zero, env_get_succ, pure_bind]
    have hren :
        ((liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
          (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
            (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC (Γ := [])
              C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim))).renameM renId2).eval
          (Env.cons (t := saltSlotStAtomTy ℓ Pt) (encSlotTbl ℓ Pt σ h.1)
            (Env.cons (t := (slotOtccaTargetIface ℓ Pt).dom .dec)
              ((h.1, fig8PubAdV (ℓ := ℓ) (Pt := Pt) h.2), wireSaltCtV (ℓ := ℓ) (Pt := Pt) e)
              (Env.cons (t := .tbl (saltSlotStAtomTy ℓ Pt)) (encSlotTbl ℓ Pt σ) .nil))) =
        (liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
          (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
            (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC (Γ := [])
              C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim))).eval
          (.cons (encSaltSlotAtom ℓ Pt (σ h.1))
            (.cons ((h.1, fig8PubAdV (ℓ := ℓ) (Pt := Pt) h.2), wireSaltCtV (ℓ := ℓ) (Pt := Pt) e)
              .nil)) := by
      exact ReductionDsl.Comp.renameM_eval _ fun ⦃u⦄ v => by
        rcases v with _ | (_ | v)
        · rfl
        · rfl
        · exact nomatch v
    change ((((liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam) .none .none
        (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
          (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC (Γ := [])
            C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim))).renameM renId2).eval
        (Env.cons (t := saltSlotStAtomTy ℓ Pt) (encSlotTbl ℓ Pt σ h.1)
          (Env.cons (t := (slotOtccaTargetIface ℓ Pt).dom .dec)
            ((h.1, fig8PubAdV (ℓ := ℓ) (Pt := Pt) h.2), wireSaltCtV (ℓ := ℓ) (Pt := Pt) e)
            (Env.cons (t := .tbl (saltSlotStAtomTy ℓ Pt)) (encSlotTbl ℓ Pt σ) .nil))) >>= _))
      |> fun lhs => CoinSimEquiv (IfaceF).fwdU lhs _
    rw [hren, liftNoQuerySlotComp_eval_eq_retag ℓ Pt C Dh encPt encT lam .none .none _
      (noQuerySlot_compilePureComp ℓ Pt C encT (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (noQuerySlot_slotSwSamp ℓ Pt C encT idOf) _ rfl)]
    have hcomp :
        CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
          ((compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
            (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC (Γ := [])
              C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim)).eval
            (mapPureEnv swBaseTy swToDen
              (.cons (CryptoGames.Ratchet.LibsignalInst.Costed.encSaltSlotSt ℓ (σ h.1))
                (.cons (h, e) .nil))))
          ((slotOtccaTargetIface ℓ Pt).liftP
            (toVal swBaseTy swToDen
              (Ty.prod (S := CryptoGames.AEAD.Costed.saltWireSig Pt ℓ) (.opt (.base .plain))
                (CryptoGames.Ratchet.LibsignalInst.Costed.saltSlotStTy (Pt := Pt) ℓ)) <$>
              (Prod.map id (CryptoGames.Ratchet.LibsignalInst.Costed.encSaltSlotSt ℓ) <$>
                (slotSaltImplByNf ℓ Pt C encT idOf nf (.inr (.inr (h, e)))).run (σ h.1)))) := by
      refine (coinSimEquiv_of_fsMacro (compilePureComp_coinSimEquiv
        (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (swOpMacro_eval' ℓ Pt C encT idOf hinj)
        (slotSwSamp_coinSimEquiv' ℓ Pt C encT idOf)
        (slotSwQuery_coinSimEquiv' ℓ Pt C encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC (Γ := [])
          C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim)
        (.cons (CryptoGames.Ratchet.LibsignalInst.Costed.encSaltSlotSt ℓ (σ h.1))
          (.cons (h, e) .nil)))).trans (CoinSimEquiv.of_eq ?_)
      cases nf with
      | false =>
        rw [CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC_false_eval
          C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim (σ h.1) (hσ h.1) h e .nil,
          ← slotOtccaTargetIface_liftP_eq_liftM ℓ Pt, iface_liftP_map]
        rfl
      | true =>
        rw [CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC_true_eval
          C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim (σ h.1) (hσ h.1) h e .nil,
          ← slotOtccaTargetIface_liftP_eq_liftM ℓ Pt, iface_liftP_map]
        rfl
    have hretag := retagSlotToI2_coinSimEquiv_liftP ℓ Pt _ _ hcomp
    refine (CoinSimEquiv.bind hretag fun _ => CoinSimEquiv.refl _).trans
      (CoinSimEquiv.of_eq ?_)
    simp only [CryptoGames.FSAEAD.Thm5.slotLift_inr, CryptoGames.FSAEAD.Thm5.slotLiftOtcca,
      StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      ← iface_liftP_pure (IfaceF), iface_liftP_bind]
    congr 1
    erw [bind_map_left, bind_assoc]
    simp only [pure_bind]
    refine bind_congr fun rs => ?_
    rcases rs with ⟨r, s'⟩
    dsimp only [Comp.eval, Expr.eval, Prod.map, id_eq]
    congr 1; apply Prod.ext
    · erw [env_get_zero]
      cases r <;> rfl
    · erw [env_get_zero]
      funext j; by_cases hj : j = h.1 <;> simp [hj, encSlotTbl, encSaltSlotAtom, toVal]

private lemma exprWk1_eval_slot {S : Sig} {O : Ops S} {a t : Ty S} {Γ : List (Ty S)}
    (e : Expr O Γ t) (x : a.denote) (ρ : Env Γ) :
    (exprWk1 e).eval (.cons x ρ) = e.eval ρ :=
  ReductionDsl.Expr.renameM_eval e fun ⦃_⦄ _ => rfl

private lemma substExpr_eval_slot {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) {t : Ty S} (e : Expr O Γ t)
    {ρ₁ : Env Γ} {ρ₂ : Env Δ}
    (hρ : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).eval ρ₂ = ρ₁.get v) :
    (substExpr envMap e).eval ρ₂ = e.eval ρ₁ := by
  induction e generalizing Δ with
  | var v => exact hρ v
  | unit => rfl
  | bool _ => rfl
  | nat _ => rfl
  | add a b iha ihb => simp [substExpr, Expr.eval, iha _ hρ, ihb _ hρ]
  | sub a b iha ihb => simp [substExpr, Expr.eval, iha _ hρ, ihb _ hρ]
  | mulK k a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | divK k a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | modK k a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | lt a b iha ihb => simp [substExpr, Expr.eval, iha _ hρ, ihb _ hρ]
  | eqN a b iha ihb => simp [substExpr, Expr.eval, iha _ hρ, ihb _ hρ]
  | not a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | and a b iha ihb => simp [substExpr, Expr.eval, iha _ hρ, ihb _ hρ]
  | ite c a b ihc iha ihb => simp [substExpr, Expr.eval, ihc _ hρ, iha _ hρ, ihb _ hρ]
  | pair a b iha ihb => simp [substExpr, Expr.eval, iha _ hρ, ihb _ hρ]
  | fst a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | snd a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | inl a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | inr a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | none => rfl
  | some a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | caseOpt e n s ihe ihn ihs =>
    simp only [substExpr, Expr.eval, ihe _ hρ]
    cases e.eval ρ₁ with
    | none => exact ihn _ hρ
    | some v =>
      exact ihs _ fun ⦃_⦄ w => by
        cases w with
        | zero => rfl
        | succ w => simp [liftEnv1, exprWk1_eval_slot, hρ w]
  | caseSum e l r ihe ihl ihr =>
    simp only [substExpr, Expr.eval, ihe _ hρ]
    cases e.eval ρ₁ with
    | inl v =>
      exact ihl _ fun ⦃_⦄ w => by
        cases w with
        | zero => rfl
        | succ w => simp [liftEnv1, exprWk1_eval_slot, hρ w]
    | inr v =>
      exact ihr _ fun ⦃_⦄ w => by
        cases w with
        | zero => rfl
        | succ w => simp [liftEnv1, exprWk1_eval_slot, hρ w]
  | letE e b ihe ihb =>
    simp only [substExpr, Expr.eval, ihe _ hρ]
    exact ihb _ fun ⦃_⦄ w => by
      cases w with
      | zero => rfl
      | succ w => simp [liftEnv1, exprWk1_eval_slot, hρ w]
  | op o a iha => simp [substExpr, Expr.eval, iha _ hρ]
  | nil => rfl
  | cons x l ihx ihl => simp [substExpr, Expr.eval, ihx _ hρ, ihl _ hρ]
  | len l ihl => simp [substExpr, Expr.eval, ihl _ hρ]
  | take n l ihn ihl => simp [substExpr, Expr.eval, ihn _ hρ, ihl _ hρ]
  | appendL K a b iha ihb => simp [substExpr, Expr.eval, iha _ hρ, ihb _ hρ]
  | findB K l p ihl ihp =>
    simp only [substExpr, Expr.eval, ihl _ hρ]; congr 1; funext x
    exact ihp _ fun ⦃_⦄ w => by
      cases w with
      | zero => rfl
      | succ w => simp [liftEnv1, exprWk1_eval_slot, hρ w]
  | anyB K l p ihl ihp =>
    simp only [substExpr, Expr.eval, ihl _ hρ]; congr 1; funext x
    exact ihp _ fun ⦃_⦄ w => by
      cases w with
      | zero => rfl
      | succ w => simp [liftEnv1, exprWk1_eval_slot, hρ w]
  | mapB K l f ihl ihf =>
    simp only [substExpr, Expr.eval, ihl _ hρ]; congr 1; funext x
    exact ihf _ fun ⦃_⦄ w => by
      cases w with
      | zero => rfl
      | succ w => simp [liftEnv1, exprWk1_eval_slot, hρ w]
  | foldrB K l z f ihl ihz ihf =>
    simp only [substExpr, Expr.eval, ihl _ hρ, ihz _ hρ]; congr 1; funext x acc
    exact ihf _ fun ⦃_⦄ w => by
      rcases w with _ | (_ | w)
      · rfl
      · rfl
      · simp [liftEnv2, exprWk1_eval_slot, hρ w]
  | tconst a iha =>
    simp only [substExpr, Expr.eval]; funext i; exact iha _ hρ
  | tget m i ihm ihi => simp [substExpr, Expr.eval, ihm _ hρ, ihi _ hρ]
  | tset m i a ihm ihi iha => simp [substExpr, Expr.eval, ihm _ hρ, ihi _ hρ, iha _ hρ]

private lemma probComp_bind_congr_support {ι : Type} {S : OracleSpec.{0, 0} ι}
    {α β : Type} (oa : OracleComp S α) {f g : α → OracleComp S β}
    (h : ∀ a ∈ support oa, f a = g a) :
    oa >>= f = oa >>= g := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact h a (by simp)
  | query_bind t mx ih =>
    simp only [bind_assoc]
    refine bind_congr fun u => ih u fun x hx => h x ?_
    simp only [support_bind, Set.mem_iUnion]
    exact ⟨u, by simp, hx⟩

private lemma iterM_state_eq {ι : Type} {S : OracleSpec.{0, 0} ι} {α R : Type}
    (f : α → StateT R (OracleComp S) α) (n : ℕ) (a : α) (r : R) :
    ReductionDsl.iterM (fun (ar : α × R) => (f ar.1).run ar.2) n (a, r) =
      (ReductionDsl.iterM f n a).run r := by
  induction n generalizing a r with
  | zero => simp [ReductionDsl.iterM]
  | succ n ih =>
    simp only [ReductionDsl.iterM, StateT.run_bind]
    exact bind_congr fun ar => ih ar.1 ar.2

private lemma foldML_state_eq {ι : Type} {S : OracleSpec.{0, 0} ι} {α β R : Type}
    (f : α → β → StateT R (OracleComp S) β) (xs : List α) (b : β) (r : R) :
    ReductionDsl.foldML (fun x (br : β × R) => (f x br.1).run br.2) (b, r) xs =
      (ReductionDsl.foldML f b xs).run r := by
  induction xs generalizing b r with
  | nil => simp [ReductionDsl.foldML]
  | cons x xs ih =>
    simp only [ReductionDsl.foldML, StateT.run_bind]
    exact bind_congr fun br => ih br.1 br.2

private lemma foldML_some_eq {ι : Type} {S : OracleSpec.{0, 0} ι} {α R : Type}
    (p : α → StateT R (OracleComp S) Bool) (xs : List α) (v : α) (r : R) :
    ReductionDsl.foldML
      (fun x (mr : Option α × R) =>
        match mr.1 with
        | none => (p x).run mr.2 >>= fun br => pure (if br.1 then some x else none, br.2)
        | some w => pure (some w, mr.2))
      (some v, r) xs = pure (some v, r) := by
  induction xs with
  | nil => simp only [ReductionDsl.foldML]
  | cons x xs ih => simp only [ReductionDsl.foldML, pure_bind, ih]

private lemma findML_state_eq {ι : Type} {S : OracleSpec.{0, 0} ι} {α R : Type}
    (p : α → StateT R (OracleComp S) Bool) (xs : List α) (r : R) :
    ReductionDsl.foldML
      (fun x (mr : Option α × R) =>
        match mr.1 with
        | none => (p x).run mr.2 >>= fun br => pure (if br.1 then some x else none, br.2)
        | some w => pure (some w, mr.2))
      (none, r) xs = (ReductionDsl.findML p xs).run r := by
  induction xs generalizing r with
  | nil => simp only [ReductionDsl.foldML, ReductionDsl.findML, StateT.run_pure]
  | cons x xs ih =>
    simp only [ReductionDsl.foldML, ReductionDsl.findML, StateT.run_bind, bind_assoc,
      pure_bind]
    refine bind_congr fun br => ?_
    cases br.1
    · simp only [Bool.false_eq_true, ↓reduceIte, ih br.2]
    · simp only [↓reduceIte, StateT.run_pure, foldML_some_eq]

private lemma foldML_true_eq {ι : Type} {S : OracleSpec.{0, 0} ι} {α R : Type}
    (p : α → StateT R (OracleComp S) Bool) (xs : List α) (r : R) :
    ReductionDsl.foldML
      (fun x (br : Bool × R) => if br.1 then pure br else (p x).run br.2)
      (true, r) xs = pure (true, r) := by
  induction xs with
  | nil => simp [ReductionDsl.foldML]
  | cons x xs ih => simp [ReductionDsl.foldML, ih]

private lemma anyML_state_eq {ι : Type} {S : OracleSpec.{0, 0} ι} {α R : Type}
    (p : α → StateT R (OracleComp S) Bool) (xs : List α) (r : R) :
    ReductionDsl.foldML
      (fun x (br : Bool × R) => if br.1 then pure br else (p x).run br.2)
      (false, r) xs = (ReductionDsl.anyML p xs).run r := by
  induction xs generalizing r with
  | nil => simp [ReductionDsl.foldML, ReductionDsl.anyML]
  | cons x xs ih =>
    simp only [ReductionDsl.foldML, ReductionDsl.anyML, Bool.false_eq_true,
      ↓reduceIte, StateT.run_bind]
    refine bind_congr fun br => ?_
    rcases br with ⟨b, r'⟩
    cases b
    · exact ih r'
    · simp [foldML_true_eq]

private lemma foldML_pure_rev {ι : Type} {S : OracleSpec.{0, 0} ι} {β : Type}
    (ys acc : List β) :
    ReductionDsl.foldML (fun y l => (pure (y :: l) : OracleComp S (List β))) acc ys =
      pure (ys.reverse ++ acc) := by
  induction ys generalizing acc with
  | nil => simp [ReductionDsl.foldML]
  | cons y ys ih => simp [ReductionDsl.foldML, ih, List.reverse_cons, List.append_assoc]

private lemma foldML_map_rev {ι : Type} {S : OracleSpec.{0, 0} ι} {α β R : Type}
    (f : α → StateT R (OracleComp S) β) (xs : List α) (acc : List β) (r : R) :
    ReductionDsl.foldML
      (fun x (ysr : List β × R) => (f x).run ysr.2 >>= fun yr => pure (yr.1 :: ysr.1, yr.2))
      (acc, r) xs =
      (fun ysr => (ysr.1.reverse ++ acc, ysr.2)) <$> (ReductionDsl.mapML f xs).run r := by
  induction xs generalizing acc r with
  | nil => simp [ReductionDsl.foldML, ReductionDsl.mapML]
  | cons x xs ih =>
    simp only [ReductionDsl.foldML, ReductionDsl.mapML, StateT.run_bind,
      bind_assoc, pure_bind, map_bind]
    refine bind_congr fun yr => ?_
    rw [ih (yr.1 :: acc) yr.2]
    simp [List.reverse_cons, List.append_assoc]

private lemma mapML_support_length {ι : Type} {S : OracleSpec.{0, 0} ι} {α β R : Type}
    (f : α → StateT R (OracleComp S) β) (xs : List α) (r : R) :
    ∀ ysr ∈ support ((ReductionDsl.mapML f xs).run r), ysr.1.length = xs.length := by
  induction xs generalizing r with
  | nil =>
    intro ysr h
    simp only [ReductionDsl.mapML, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
    subst h; rfl
  | cons x xs ih =>
    intro ysr h
    simp only [ReductionDsl.mapML, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at h
    obtain ⟨yr, _, ysr', hysr', rfl⟩ := h
    simp [ih yr.2 ysr' hysr']

private lemma foldML_consume_done {ι : Type} {S : OracleSpec.{0, 0} ι} {α R : Type}
    (stepF : α → ((Bool × List α) × R) → OracleComp S ((Bool × List α) × R))
    (hdone : ∀ x acc r, stepF x ((true, acc), r) = pure ((true, x :: acc), r))
    (xs acc : List α) (r : R) :
    ReductionDsl.foldML stepF ((true, acc), r) xs =
      pure ((true, xs.reverse ++ acc), r) := by
  induction xs generalizing acc with
  | nil => simp [ReductionDsl.foldML]
  | cons x xs ih =>
    simp [ReductionDsl.foldML, hdone, ih, List.reverse_cons, List.append_assoc]

private lemma foldML_consume_rev {ι : Type} {S : OracleSpec.{0, 0} ι} {α R : Type}
    (p : α → StateT R (OracleComp S) Bool) (mk : α → α) (xs acc : List α) (r : R) :
    ReductionDsl.foldML
      (fun x (st : (Bool × List α) × R) =>
        if st.1.1 then
          pure ((true, x :: st.1.2), st.2)
        else
          (p x).run st.2 >>= fun br =>
            if br.1 then pure ((true, mk x :: st.1.2), br.2)
            else pure ((false, x :: st.1.2), br.2))
      ((false, acc), r) xs =
      (fun (res : (Bool × List α) × R) => ((res.1.1, res.1.2.reverse ++ acc), res.2)) <$>
        (ReductionDsl.consumeFirstML p mk xs).run r := by
  induction xs generalizing acc r with
  | nil => simp [ReductionDsl.foldML, ReductionDsl.consumeFirstML]
  | cons x xs ih =>
    simp only [ReductionDsl.foldML, ReductionDsl.consumeFirstML, Bool.false_eq_true,
      ↓reduceIte, StateT.run_bind, bind_assoc, map_bind]
    refine bind_congr fun br => ?_
    rcases br with ⟨b, r'⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      rw [ih (x :: acc) r']
      simp [Functor.map_map, List.reverse_cons, List.append_assoc]
    · simp only [↓reduceIte, pure_bind, StateT.run_pure, map_pure]
      rw [foldML_consume_done
        (fun x (st : (Bool × List α) × R) =>
          if st.1.1 then pure ((true, x :: st.1.2), st.2)
          else (p x).run st.2 >>= fun br =>
            if br.1 then pure ((true, mk x :: st.1.2), br.2)
            else pure ((false, x :: st.1.2), br.2))
        (fun _ _ _ => rfl) xs (mk x :: acc) r']
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma consumeFirstML_support_length {ι : Type} {S : OracleSpec.{0, 0} ι} {α R : Type}
    (p : α → StateT R (OracleComp S) Bool) (mk : α → α) (xs : List α) (r : R) :
    ∀ res ∈ support ((ReductionDsl.consumeFirstML p mk xs).run r),
      res.1.2.length = xs.length := by
  induction xs generalizing r with
  | nil =>
    intro res h
    simp only [ReductionDsl.consumeFirstML, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at h
    subst h; rfl
  | cons x xs ih =>
    intro res h
    simp only [ReductionDsl.consumeFirstML, StateT.run_bind, mem_support_bind_iff] at h
    obtain ⟨⟨b, r'⟩, _, h⟩ := h
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
      obtain ⟨res', hres', rfl⟩ := h
      simp [ih r' res' hres']
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
      subst h; simp

private lemma simulateQ_qSlotRaw_liftP (nf : Bool) (qSim : ℕ) {α : Type}
    (p : ProbComp α) (tbl : (Ty.tbl (saltSlotStAtomTy ℓ Pt)).denote) :
    (simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
      ((slotOtccaTargetIface ℓ Pt).liftP p)).run tbl =
      (fun a => (a, tbl)) <$> (IfaceF).liftP p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    have hq :
        (simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
          ((slotOtccaTargetIface ℓ Pt).fwdU n)).run tbl =
        (fun a => (a, tbl)) <$> (IfaceF).fwdU n := by
      dsimp only [slotOtccaTargetIface, fsaeadHeaderIface]
      simp [qSlotRaw, StateT.run_lift, map_eq_bind_pure_comp]
    simp only [ReductionDsl.Iface.liftP, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind]
    change (do
        let p ← (simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
          ((slotOtccaTargetIface ℓ Pt).fwdU n)).run tbl
        (simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
          ((slotOtccaTargetIface ℓ Pt).liftP (k p.1))).run p.2) =
      (fun a => (a, tbl)) <$> ((IfaceF).fwdU n >>= fun u => (IfaceF).liftP (k u))
    rw [hq, bind_map_left, map_bind]
    exact bind_congr fun u => ih u

private lemma simulateQ_state_bind {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} {R α β : Type}
    (impl : QueryImpl S₁ (StateT R (OracleComp S₂)))
    (oa : OracleComp S₁ α) (k : α → OracleComp S₁ β) (r : R) :
    (simulateQ impl (oa >>= k)).run r =
      ((simulateQ impl oa).run r >>= fun zr => (simulateQ impl (k zr.1)).run zr.2) := by
  simp [simulateQ_bind, StateT.run_bind]

private lemma simulateQ_state_iterM {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} {R α : Type}
    (impl : QueryImpl S₁ (StateT R (OracleComp S₂)))
    (f : α → OracleComp S₁ α) (n : ℕ) (a : α) (r : R) :
    (simulateQ impl (ReductionDsl.iterM f n a)).run r =
      (ReductionDsl.iterM (fun x => simulateQ impl (f x)) n a).run r := by
  induction n generalizing a r with
  | zero => simp [ReductionDsl.iterM]
  | succ n ih =>
    simp only [ReductionDsl.iterM, simulateQ_bind, StateT.run_bind]
    exact bind_congr fun ar => ih ar.1 ar.2

private lemma simulateQ_state_foldML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} {R α β : Type}
    (impl : QueryImpl S₁ (StateT R (OracleComp S₂)))
    (f : α → β → OracleComp S₁ β) (xs : List α) (b : β) (r : R) :
    (simulateQ impl (ReductionDsl.foldML f b xs)).run r =
      (ReductionDsl.foldML (fun x acc => simulateQ impl (f x acc)) b xs).run r := by
  induction xs generalizing b r with
  | nil => simp [ReductionDsl.foldML]
  | cons x xs ih =>
    simp only [ReductionDsl.foldML, simulateQ_bind, StateT.run_bind]
    exact bind_congr fun br => ih br.1 br.2

private lemma simulateQ_state_findML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} {R α : Type}
    (impl : QueryImpl S₁ (StateT R (OracleComp S₂)))
    (p : α → OracleComp S₁ Bool) (xs : List α) (r : R) :
    (simulateQ impl (ReductionDsl.findML p xs)).run r =
      (ReductionDsl.findML (fun x => simulateQ impl (p x)) xs).run r := by
  induction xs generalizing r with
  | nil => simp [ReductionDsl.findML]
  | cons x xs ih =>
    simp only [ReductionDsl.findML, simulateQ_bind, StateT.run_bind]
    refine bind_congr fun br => ?_
    cases br.1 <;> simp [ih br.2]

private lemma simulateQ_state_anyML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} {R α : Type}
    (impl : QueryImpl S₁ (StateT R (OracleComp S₂)))
    (p : α → OracleComp S₁ Bool) (xs : List α) (r : R) :
    (simulateQ impl (ReductionDsl.anyML p xs)).run r =
      (ReductionDsl.anyML (fun x => simulateQ impl (p x)) xs).run r := by
  induction xs generalizing r with
  | nil => simp [ReductionDsl.anyML]
  | cons x xs ih =>
    simp only [ReductionDsl.anyML, simulateQ_bind, StateT.run_bind]
    refine bind_congr fun br => ?_
    cases br.1 <;> simp [ih br.2]

private lemma simulateQ_state_mapML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} {R α β : Type}
    (impl : QueryImpl S₁ (StateT R (OracleComp S₂)))
    (f : α → OracleComp S₁ β) (xs : List α) (r : R) :
    (simulateQ impl (ReductionDsl.mapML f xs)).run r =
      (ReductionDsl.mapML (fun x => simulateQ impl (f x)) xs).run r := by
  induction xs generalizing r with
  | nil => simp [ReductionDsl.mapML]
  | cons x xs ih =>
    simp only [ReductionDsl.mapML, simulateQ_bind, StateT.run_bind]
    refine bind_congr fun yr => ?_
    simp [ih yr.2]

private lemma simulateQ_state_consumeFirstML {ι₁ ι₂ : Type} {S₁ : OracleSpec.{0, 0} ι₁}
    {S₂ : OracleSpec.{0, 0} ι₂} {R α : Type}
    (impl : QueryImpl S₁ (StateT R (OracleComp S₂)))
    (p : α → OracleComp S₁ Bool) (mk : α → α) (xs : List α) (r : R) :
    (simulateQ impl (ReductionDsl.consumeFirstML p mk xs)).run r =
      (ReductionDsl.consumeFirstML (fun x => simulateQ impl (p x)) mk xs).run r := by
  induction xs generalizing r with
  | nil => simp [ReductionDsl.consumeFirstML]
  | cons x xs ih =>
    simp only [ReductionDsl.consumeFirstML, simulateQ_bind, StateT.run_bind]
    refine bind_congr fun br => ?_
    cases br.1 <;> simp [ih br.2]

private lemma env_eq_evalEnvMap_slot {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (ρ₁ : Env Γ) (ρ₂ : Env Δ)
    (hρ : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).eval ρ₂ = ρ₁.get v) :
    ρ₁ = evalEnvMap envMap ρ₂ := by
  induction ρ₁ with
  | nil => rfl
  | cons x xs ih =>
    simp only [evalEnvMap]
    congr 1
    · exact (hρ .zero).symm
    · exact ih (fun _ v => envMap v.succ) (fun _ v => hρ v.succ)

private lemma substQueryComp_slot_eval (nf : Bool) (qSim : ℕ)
    {Γ Δ : List (Ty SigA)} {t : Ty SigA}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr OpsF Δ u)
    (rExpr : Expr OpsF Δ (.tbl (saltSlotStAtomTy ℓ Pt)))
    (c : Comp OpsF (slotOtccaTargetIface ℓ Pt) Γ t)
    {ρ₁ : Env Γ} {ρ₂ : Env Δ}
    (hρ : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).eval ρ₂ = ρ₁.get v) :
    (substQueryComp (I₁ := slotOtccaTargetIface ℓ Pt) (I₂ := IfaceF)
      (fun s {_} e => liftBaseSamp s e)
      (slotOtccaImpl ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
      envMap rExpr c).eval ρ₂ =
    (simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
      (c.eval ρ₁)).run (rExpr.eval ρ₂) := by
  rw [env_eq_evalEnvMap_slot envMap ρ₁ ρ₂ hρ]
  exact substQueryComp_eval (I₁ := slotOtccaTargetIface ℓ Pt) (I₂ := IfaceF)
    (fun s {_} e => liftBaseSamp s e)
    (slotOtccaImpl ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
    (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
    (fun s {_} e ρ r => by
      rw [liftBaseSamp_eval_slot, simulateQ_qSlotRaw_liftP]
      simp only [slotOtccaTargetIface, map_eq_bind_pure_comp, Function.comp_def])
    (fun g x r => by
      cases g with
      | enc =>
        rcases x with ⟨⟨i, aV⟩, m⟩
        dsimp only [slotOtccaTargetIface, qSlotRaw, slotAdOfV]
        rw [fig8PubAdV_fig8PubAdOfV, StateT.run_map, StateT.run_mk, Functor.map_map]
        symm
        calc _ = id <$> _ := by
              congr 1
              funext ⟨res, tbl'⟩
              cases res <;> simp [Prod.map, wireSaltCtV_wireSaltCtOfV]
          _ = _ := id_map _
      | dec =>
        rcases x with ⟨⟨i, aV⟩, eV⟩
        dsimp only [slotOtccaTargetIface, qSlotRaw, slotAdOfV]
        rw [fig8PubAdV_fig8PubAdOfV, wireSaltCtV_wireSaltCtOfV, StateT.run_map, StateT.run_mk]
        symm
        calc _ = id <$> _ := by congr 1
          _ = _ := id_map _)
    envMap rExpr c ρ₂

private lemma evalDistEq_probComp_bind_of_support {α β : Type} (p : ProbComp α)
    {g₁ g₂ : α → ProbComp β} (hg : ∀ a ∈ support p, g₁ a =ᵈ g₂ a) :
    (p >>= g₁) =ᵈ (p >>= g₂) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact hg a (by simp)
  | query_bind n k ih =>
    simp only [bind_assoc]
    exact EvalDistEq.rfl.bind fun u => ih u fun a ha =>
      hg a (by simp only [mem_support_bind_iff]; exact ⟨u, by simp, ha⟩)

private lemma coinSimEquiv_liftP_bind_of_support_slot {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α β : Type} (p : ProbComp α) {k₁ k₂ : α → OracleComp T β}
    (hk : ∀ a ∈ support p, CoinSimEquiv I.fwdU (k₁ a) (k₂ a)) :
    CoinSimEquiv I.fwdU (I.liftP p >>= k₁) (I.liftP p >>= k₂) := by
  refine ⟨fun {σ₀} impl hv s₀ => ?_⟩
  simp only [simulateQ_bind, StateT.run_bind]
  have hl := Computational.Proofs.ReductionDsl.FsAtomicMacros.evalDistEq_simulateQ_liftP I impl hv p s₀
  refine ((hl.bind fun _ => EvalDistEq.rfl).trans ?_).trans
    ((hl.bind fun _ => EvalDistEq.rfl).symm)
  simp only [bind_assoc, pure_bind]
  exact evalDistEq_probComp_bind_of_support p fun a ha => (hk a ha).run_eq impl hv s₀

private lemma qSlotRaw_coinSimEquiv_trans (nf : Bool) (qSim : ℕ) {α : Type}
    {oa₁ oa₂ : OracleComp
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α}
    (h : CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU oa₁ oa₂)
    (tbl : (Ty.tbl (saltSlotStAtomTy ℓ Pt)).denote) :
    CoinSimEquiv (IfaceF).fwdU
      ((simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim) oa₁).run tbl)
      ((simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim) oa₂).run tbl) := by
  refine ⟨fun {σ₀} impl hv s₀ => ?_⟩
  let implComb : QueryImpl
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
      (StateT ((Ty.tbl (saltSlotStAtomTy ℓ Pt)).denote × σ₀) ProbComp) := fun q =>
    StateT.mk fun ts => do
      let ((r, t'), s') ←
        (simulateQ impl
          ((qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim q).run ts.1)).run ts.2
      pure (r, (t', s'))
  have hvComb : Computational.Proofs.ReductionDsl.FsAtomicMacros.ValidCoinSim
      (slotOtccaTargetIface ℓ Pt).fwdU implComb := ⟨by
    intro n ⟨t, s⟩
    have hcoin := hv.coin_eq n s
    have hlhs :
        (simulateQ implComb ((slotOtccaTargetIface ℓ Pt).fwdU n)).run (t, s) =
        ((simulateQ impl ((IfaceF).fwdU n)).run s >>=
          fun z => pure (z.1, (t, z.2))) := by
      simp [slotOtccaTargetIface, implComb, fsaeadHeaderIface, qSlotRaw]
    rw [hlhs]
    have h1 :
        ((simulateQ impl ((IfaceF).fwdU n)).run s >>=
          fun z => (pure (z.1, (t, z.2)) : ProbComp _)) =ᵈ
        (((query (m := ProbComp) (spec := unifSpec) n >>= fun u => pure (u, s)) : ProbComp _) >>=
          fun z => pure (z.1, (t, z.2))) :=
      hcoin.bind fun z => EvalDistEq.rfl
    exact h1.trans (by simp only [bind_assoc, pure_bind]; exact EvalDistEq.rfl)⟩
  have hnest : ∀ {β : Type}
      (oa : OracleComp
        (unifSpec + CryptoGames.AEADScheme.otccaSpec
          (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) β)
      (t : (Ty.tbl (saltSlotStAtomTy ℓ Pt)).denote) (s : σ₀),
      (simulateQ impl
        ((simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim) oa).run t)).run s =
      (fun (z : β × (_ × σ₀)) => ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ implComb oa).run (t, s) := by
    intro β oa
    induction oa using OracleComp.inductionOn with
    | pure b => intro t s; simp
    | query_bind q k ih =>
      intro t s
      dsimp only [implComb]
      simp only [simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, StateT.run_mk, simulateQ_bind,
        map_bind, bind_assoc, pure_bind]
      exact bind_congr fun z => ih z.1.1 z.1.2 z.2
  rw [hnest oa₁ tbl s₀, hnest oa₂ tbl s₀]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  exact (h.run_eq implComb hvComb (tbl, s₀)).bind fun _ => EvalDistEq.rfl

private theorem simulateQ_qSlotRaw_of_bound (hinj : Function.Injective encT)
    (nf : Bool) (qSim : ℕ) {α : Type}
    (oa : OracleComp
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α) :
    ∀ (m : ℕ), oa.IsQueryBoundP (fun t => t.isRight = true) m →
      ∀ (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) (n : ℕ),
        (∀ i, (σ i).table.length ≤ n) → n + m ≤ qSim →
        CoinSimEquiv (IfaceF).fwdU
          ((simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim) oa).run
            (encSlotTbl ℓ Pt σ))
          ((IfaceF).liftP
            (Prod.map id (encSlotTbl ℓ Pt) <$>
              (simulateQ (CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf))
                oa).run σ)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro m _ σ n _ _
    exact CoinSimEquiv.of_eq rfl
  | query_bind t k ih =>
    intro m hb σ n hσ hnm
    rw [isQueryBoundP_query_bind_iff] at hb
    simp only [simulateQ_query_bind, monadLift_self, OracleQuery.input_query,
      OracleQuery.cont_query, StateT.run_bind, map_bind]
    rcases t with u | q
    · have hstep :
          (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim (.inl u)).run
            (encSlotTbl ℓ Pt σ) =
          (IfaceF).liftP
            (Prod.map id (encSlotTbl ℓ Pt) <$>
              (CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf)
                (.inl u)).run σ) := by
        dsimp only [qSlotRaw, fsaeadHeaderIface]
        simp only [CryptoGames.FSAEAD.Thm5.slotLift_inl, QueryImpl.liftTarget_apply,
          QueryImpl.ofLift_apply, StateT.run_lift, StateT.run_monadLift,
          ReductionDsl.Iface.liftP, map_eq_bind_pure_comp, Function.comp_def,
          monadLift_self, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, simulateQ_pure, Prod.map, id_eq, bind_assoc, pure_bind]
        rfl
      rw [hstep, ← iface_liftP_map]
      simp only [bind_map_left]
      change CoinSimEquiv (IfaceF).fwdU
        ((IfaceF).liftP
          ((CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf) (.inl u)).run σ) >>=
          fun z => (simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
            (k z.1)).run (encSlotTbl ℓ Pt z.2))
        ((IfaceF).liftP _)
      rw [← iface_liftP_bind]
      refine coinSimEquiv_liftP_bind_of_support_slot (IfaceF) _ fun z hz => ?_
      have hpres := slotSaltImplByNf_support_length ℓ Pt C encT idOf nf (.inl u) σ z hz
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hpres
      have hbu := hb.2 z.1
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte] at hbu
      exact ih z.1 m hbu z.2 n (fun i => (hpres i).trans (hσ i)) hnm
    · have hm : 0 < m := hb.1.resolve_left (by simp)
      have hstep := slotOtccaImpl_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj nf qSim σ
        (fun i => (hσ i).trans (by omega)) q
      refine (CoinSimEquiv.bind hstep fun _ => CoinSimEquiv.refl _).trans ?_
      rw [← iface_liftP_map]
      simp only [bind_map_left]
      change CoinSimEquiv (IfaceF).fwdU
        ((IfaceF).liftP
          ((CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf) (.inr q)).run σ) >>=
          fun z => (simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
            (k z.1)).run (encSlotTbl ℓ Pt z.2))
        ((IfaceF).liftP _)
      rw [← iface_liftP_bind]
      refine coinSimEquiv_liftP_bind_of_support_slot (IfaceF) _ fun z hz => ?_
      have hpres := slotSaltImplByNf_support_length ℓ Pt C encT idOf nf (.inr q) σ z hz
      simp only [Sum.isRight_inr, ↓reduceIte] at hpres
      have hbu := hb.2 z.1
      simp only [Sum.isRight_inr, ↓reduceIte] at hbu
      exact ih z.1 (m - 1) hbu z.2 (n + 1)
        (fun i => Nat.add_le_add_right (hσ i) 1 |> (hpres i).trans) (by omega)

private theorem liftSlotHybStep_coinSimEquiv (hinj : Function.Injective encT)
    {qTy rTy : Ty SigA} {R : Type}
    (nf : Bool) (qSim : ℕ)
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt)
      [qTy, hybSessStTy ℓ Pt] (.prod rTy (hybSessStTy ℓ Pt)))
    (qV : qTy.denote)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (encRes : R → rTy.denote)
    (oa : OracleComp
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
      (R × CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt))
    (hc : CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (c.eval (.cons qV (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((fun z => (encRes z.1, encHybSessSt ℓ Pt z.2)) <$> oa))
    {m n : ℕ}
    (hbound : oa.IsQueryBoundP (fun t => t.isRight = true) m)
    (hσ : ∀ i, (σ i).table.length ≤ n)
    (hnm : n + m ≤ qSim) :
    CoinSimEquiv (IfaceF).fwdU
      ((liftSlotHybStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim c).eval
        (.cons qV (.cons (encSlotSessSt ℓ Pt (s, σ)) .nil)))
      ((IfaceF).liftP
        ((fun z => (encRes z.1.1, encSlotSessSt ℓ Pt (z.1.2, z.2))) <$>
          (simulateQ (CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf))
            oa).run σ)) := by
  dsimp only [liftSlotHybStep, Comp.eval]
  have hsubst := substQueryComp_slot_eval ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim
    envSwapFst2 (.snd (.var (.succ .zero))) (liftFsSlotComp c)
    (ρ₁ := .cons qV (.cons (encHybSessSt ℓ Pt s) .nil))
    (ρ₂ := .cons qV (.cons (encSlotSessSt ℓ Pt (s, σ)) .nil))
    (fun ⦃_⦄ v => by
      rcases v with _ | (_ | v)
      · rfl
      · rfl
      · exact nomatch v)
  rw [hsubst, liftFsSlotComp_eval]
  dsimp only [Expr.eval, encSlotSessSt]
  simp only [env_get_zero, env_get_succ]
  refine (CoinSimEquiv.bind
    (qSlotRaw_coinSimEquiv_trans ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim hc _)
    fun _ => CoinSimEquiv.refl _).trans ?_
  have hmap_run :
      (simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
        ((fun z => (encRes z.1, encHybSessSt ℓ Pt z.2)) <$> oa)).run (encSlotTbl ℓ Pt σ) =
      Prod.map (fun z => (encRes z.1, encHybSessSt ℓ Pt z.2)) id <$>
        (simulateQ (qSlotRaw ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim) oa).run
          (encSlotTbl ℓ Pt σ) := by
    simp only [map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, Prod.map, id_eq]
  rw [hmap_run, bind_map_left]
  have hsim := simulateQ_qSlotRaw_of_bound ℓ Pt C Dh encPt encT idOf lam hinj nf qSim oa
    m hbound σ n hσ hnm
  refine (CoinSimEquiv.bind hsim fun _ => CoinSimEquiv.refl _).trans (CoinSimEquiv.of_eq ?_)
  rw [← iface_liftP_map]
  simp only [bind_map_left]
  change ((IfaceF).liftP _ >>= fun z => pure _) = (IfaceF).liftP _
  have hpure : ∀ z : (R × _) × _,
      (pure ((encRes z.1.1, (encHybSessSt ℓ Pt z.1.2, encSlotTbl ℓ Pt z.2))) :
        OracleComp _ _) =
      (IfaceF).liftP (pure (encRes z.1.1, encSlotSessSt ℓ Pt (z.1.2, z.2))) := fun _ => rfl
  simp only [Prod.map, id_eq]
  conv_lhs => arg 2; ext z; rw [hpure z]
  rw [iface_liftP_bind]
  simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- Per-session optional state invariant on a slot (`fsSlotImpl`) router entry after `n` queries. -/
private def SlotOptInv (n : ℕ)
    (os : Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ×
      (ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt))) : Prop :=
  match os with
  | none => True
  | some (s, tbl) =>
    CryptoGames.FSAEAD.Thm5.HInv maxForwardJumps n s.1 ∧ ∀ i, (tbl i).table.length ≤ n

private lemma fst_mem_support_simulateQ_run
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) :
    ∀ st, ∀ z ∈ support ((simulateQ impl oa).run st), z.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; simp
  | query_bind t k ih =>
    intro st z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, -, hz'⟩ := hz
    exact (mem_support_bind_iff _ _ _).2 ⟨r.1, mem_support_query t r.1, ih r.1 r.2 z hz'⟩

omit [Zero Pt] [SampleableType Pt] in
private lemma simulateQ_slotLift_support_length
    (nf : Bool) {α : Type}
    (oa : OracleComp
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α)
    (m : ℕ) (hb : oa.IsQueryBoundP (fun t => t.isRight = true) m)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (n : ℕ) (hσ : ∀ i, (σ i).table.length ≤ n) :
    ∀ z ∈ support
      ((simulateQ (CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf))
        oa).run σ),
      ∀ i, (z.2 i).table.length ≤ n + m := by
  induction oa using OracleComp.inductionOn generalizing m σ n with
  | pure a =>
    intro z hz i
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact (hσ i).trans (Nat.le_add_right n m)
  | query_bind t k ih =>
    intro z hz i
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz'⟩ := hz
    have hpres := slotSaltImplByNf_support_length ℓ Pt C encT idOf nf t σ r hr
    cases t with
    | inl u =>
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hpres hb
      exact ih r.1 m (hb.2 r.1) r.2 n (fun j => (hpres j).trans (hσ j)) z hz' i
    | inr q =>
      have hm : 0 < m := hb.1.resolve_left (by simp)
      simp only [Sum.isRight_inr, ↓reduceIte] at hpres hb
      have hstep := ih r.1 (m - 1) (hb.2 r.1) r.2 (n + 1)
        (fun j => (hpres j).trans (Nat.add_le_add_right (hσ j) 1)) z hz' i
      omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma fsSlotInit_inv (n : ℕ) :
    ∀ s ∈ support
      (CryptoVerification.E2E.Signed.SessionFS.fsSlotInit
        (pure fun _ => ({} : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)) :
        ProbComp (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
          (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ×
          (ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt))),
      CryptoGames.FSAEAD.Thm5.HInv maxForwardJumps n s.1.1 ∧
        ∀ i, (s.2 i).table.length ≤ n := by
  intro s hs
  simp only [CryptoVerification.E2E.Signed.SessionFS.fsSlotInit, pure_bind,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hs
  obtain ⟨b, -, rfl⟩ := hs
  exact ⟨(CryptoGames.FSAEAD.Thm5.HInv.init b).mono (Nat.zero_le n), fun _ => Nat.zero_le n⟩

private theorem renSwap2_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {a b : Ty S} {Γ : List (Ty S)} {t : Ty S}
    (c : Comp O I [a, b] t) (y : b.denote) (x : a.denote) (ρ : Env Γ) :
    (c.renameM renSwap2).eval (.cons y (.cons x ρ)) = c.eval (.cons x (.cons y .nil)) :=
  c.renameM_eval (fun _ v => match v with | .zero => rfl | .succ .zero => rfl)

private abbrev slotSaltProtoByNf (nf : Bool) :
    QueryImpl (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT (CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) ProbComp) :=
  if nf then
    CryptoGames.Ratchet.LibsignalInst.slotSaltImplNF C protoSignalCodec ℓ encT idOf false
  else
    CryptoGames.Ratchet.LibsignalInst.slotSaltImpl C protoSignalCodec ℓ encT idOf false

omit [Zero Pt] [SampleableType Pt] in
private lemma slotSaltImplByNf_proto_inl_eq (nf : Bool) (u : unifSpec.Domain) :
    slotSaltImplByNf ℓ Pt C encT idOf nf (.inl u) =
      slotSaltProtoByNf ℓ Pt C encT idOf nf (.inl u) := by
  cases nf <;>
    simp [slotSaltImplByNf, slotSaltProtoByNf,
      CryptoGames.Ratchet.LibsignalInst.slotSaltImpl,
      CryptoGames.Ratchet.LibsignalInst.slotSaltImplNF]

omit [Zero Pt] [SampleableType Pt] in
private lemma slotSaltImplByNf_proto_dec_eq (nf : Bool)
    (ia : ℕ × (Header Pt × LibsignalMsgPublicPart)) (e : LCt) :
    slotSaltImplByNf ℓ Pt C encT idOf nf (.inr (.inr (ia, e))) =
      slotSaltProtoByNf ℓ Pt C encT idOf nf (.inr (.inr (ia, e))) := by
  cases nf <;>
    simp [slotSaltImplByNf, slotSaltProtoByNf,
      CryptoGames.Ratchet.LibsignalInst.slotSaltImpl,
      CryptoGames.Ratchet.LibsignalInst.slotSaltImplNF,
      Computational.Proofs.ReductionDsl.FsAtomicOps.lAeadK_clamped_dec_eq]

omit [Zero Pt] [SampleableType Pt] in
private lemma slotSaltImplByNf_proto_enc_eq (nf : Bool)
    (i : ℕ) (a : Header Pt × LibsignalMsgPublicPart) (m : Plain ℓ)
    (hshort : atomicShortB a.2 = true) :
    slotSaltImplByNf ℓ Pt C encT idOf nf (.inr (.inl ((i, a), m))) =
      slotSaltProtoByNf ℓ Pt C encT idOf nf (.inr (.inl ((i, a), m))) := by
  have henc : ∀ mk,
      (CryptoGames.Ratchet.LibsignalInst.lAeadK C clampedProtoSignalCodec ℓ encT idOf).enc mk
          ((i, a.1), a.2) m =
        (CryptoGames.Ratchet.LibsignalInst.lAeadK C protoSignalCodec ℓ encT idOf).enc mk
          ((i, a.1), a.2) m :=
    fun mk =>
      Computational.Proofs.ReductionDsl.FsAtomicOps.lAeadK_clamped_enc_eq C ℓ encT idOf mk
        ((i, a.1), a.2) m hshort
  cases nf <;>
    simp only [slotSaltImplByNf, slotSaltProtoByNf, ↓reduceIte, Bool.false_eq_true,
      CryptoGames.Ratchet.LibsignalInst.slotSaltImpl,
      CryptoGames.Ratchet.LibsignalInst.slotSaltImplNF, henc]

omit [Zero Pt] [SampleableType Pt] in
private lemma slotSaltImplByNf_proto_eq_of_not_otEncBad (nf : Bool)
    (t : (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt).Domain)
    (ht : ¬ CryptoGames.AEADScheme.otEncBad
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) t = true) :
    slotSaltImplByNf ℓ Pt C encT idOf nf t =
      slotSaltProtoByNf ℓ Pt C encT idOf nf t := by
  rcases t with u | (⟨⟨i, a⟩, m⟩ | ⟨ia, e⟩)
  · exact slotSaltImplByNf_proto_inl_eq ℓ Pt C encT idOf nf u
  · have ha : atomicShortB a.2 = true := by simpa [CryptoGames.AEADScheme.otEncBad] using ht
    exact slotSaltImplByNf_proto_enc_eq ℓ Pt C encT idOf nf i a m ha
  · exact slotSaltImplByNf_proto_dec_eq ℓ Pt C encT idOf nf ia e

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma run_simulateQ_eq_of_dis_slot {κ : Type} {spec : OracleSpec.{0, 0} κ}
    {α σ : Type}
    {impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp)}
    {dis : κ → Prop} [DecidablePred dis]
    (oa : OracleComp spec α) (hoa : oa.IsQueryBoundP dis 0) (s : σ)
    (hstep : ∀ t s, ¬dis t → (impl₁ t).run s = (impl₂ t).run s) :
    (simulateQ impl₁ oa).run s = (simulateQ impl₂ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hoa
    obtain ⟨hdis, hk⟩ := hoa
    have hndis : ¬dis t := by simpa using hdis
    simp only [hndis, ↓reduceIte] at hk
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [hstep t s hndis]
    exact bind_congr fun z => ih z.1 (hk z.1) z.2

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma slot_multiEncIdxWith_clamped_eq
    (N i : ℕ) (a : Header Pt × LibsignalMsgPublicPart) (msg : Plain ℓ)
    (ha : atomicShortB a.2 = true) :
    CryptoGames.FSAEAD.Thm5.multiEncIdxWith
      (m := OracleComp (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt))
      (CK := BitVec 256)
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      0 N (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C clampedProtoSignalCodec ℓ encT)))
      i a msg =
    CryptoGames.FSAEAD.Thm5.multiEncIdxWith
      (m := OracleComp (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt))
      (CK := BitVec 256)
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      0 N (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
      i a msg := by
  unfold CryptoGames.FSAEAD.Thm5.multiEncIdxWith
  refine congrArg (Bind.bind CryptoGames.FSAEAD.Thm5.getH) (funext fun st => ?_)
  have hk :
      CryptoGames.FSAEAD.Thm5.multiKind 0 N
        (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C clampedProtoSignalCodec ℓ encT))) st i =
      CryptoGames.FSAEAD.Thm5.multiKind 0 N
        (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT))) st i := rfl
  rw [hk]
  generalize CryptoGames.FSAEAD.Thm5.multiKind 0 N
    (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT))) st i = κ
  have hid := Computational.Proofs.ReductionDsl.FsAtomicOps.lIdeal_clamped_eq C ℓ encT (i, a) ha
  have hkeys : ∀ K,
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf).enc K (i, a) msg =
        (lAeadR C protoSignalCodec ℓ encT idOf).enc K (i, a) msg :=
    fun K =>
      Computational.Proofs.ReductionDsl.FsAtomicOps.lAeadR_clamped_enc_eq C ℓ encT idOf K (i, a)
        msg ha
  cases κ with
  | ideal => simp only [hid]
  | special => simp only [CryptoGames.FSAEAD.Thm5.otOpsWith, hid]
  | real => simp only [hid, hkeys]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma slot_multiDecIdx_clamped_eq
    (N : ℕ) (hint : Option (Plain ℓ)) (i : ℕ)
    (a : Header Pt × LibsignalMsgPublicPart) (e : LCt) :
    CryptoGames.FSAEAD.Thm5.multiDecIdx
      (m := OracleComp (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt))
      (CK := BitVec 256)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
      0 N (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C clampedProtoSignalCodec ℓ encT)))
      hint i a e =
    CryptoGames.FSAEAD.Thm5.multiDecIdx
      (m := OracleComp (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt))
      (CK := BitVec 256)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      0 N (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
      hint i a e := by
  unfold CryptoGames.FSAEAD.Thm5.multiDecIdx
  cases hint with
  | some msg => rfl
  | none =>
    dsimp only
    refine congrArg (Bind.bind CryptoGames.FSAEAD.Thm5.getH) (funext fun st => ?_)
    have hk :
        CryptoGames.FSAEAD.Thm5.multiKind 0 N
          (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C clampedProtoSignalCodec ℓ encT))) st i =
        CryptoGames.FSAEAD.Thm5.multiKind 0 N
          (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT))) st i := rfl
    rw [hk, Computational.Proofs.ReductionDsl.FsAtomicOps.lAeadR_clamped_dec_eq]
    generalize CryptoGames.FSAEAD.Thm5.multiKind 0 N
      (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT))) st i = κ
    cases κ <;> rfl

omit [Zero Pt] [SampleableType Pt] in
private lemma slot_multiOraclesWith_qb_one
    (ideal : ℕ × (Header Pt × LibsignalMsgPublicPart) → ProbComp LCt)
    (ae : CryptoGames.AEADScheme (BitVec 256)
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
    (N : ℕ) (la : Bool)
    (t : (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt).Domain)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt) :
    ((CryptoGames.FSAEAD.Thm5.multiOraclesWith ideal ae (lChainPRG C.F) maxForwardJumps
      (hp N 0 la) N (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
      (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal)) t).run s).IsQueryBoundP
      (fun q => q.isRight = true) 1 := by
  refine (CryptoVerification.E2E.Signed.SessionQueries.qb_multiOraclesWith_step
    ideal ae (lChainPRG C.F) maxForwardJumps (Q := fun q => q.isRight = true)
    (fun _ => by simp) N la 1 1 (fun _ _ _ _ _ _ => Nat.zero_lt_one)
    (fun _ _ _ _ _ _ => Nat.zero_lt_one) t s).mono ?_
  split_ifs <;> omega

omit [Zero Pt] [SampleableType Pt] in
private theorem compilePureComp_multi_coinSimEquiv (hinj : Function.Injective encT)
    {Γ : List (Ty (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))}
    {t : Ty (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)}
    (c : Comp
      (Ops.sum
        (CryptoGames.PRG.Costed.prgOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
          (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
        (CryptoGames.OTCCA.Costed.otccaOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ())))
      (Iface.withSamp
        (CryptoGames.OTCCA.Costed.otccaIface
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.prod .nat (.base .ad)) (.base .msg) (.base .ct)
          (lIdeal C clampedProtoSignalCodec ℓ encT) 1)
        (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)))
      Γ t)
    (ρ : Env Γ) :
    CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      ((compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) c).eval
        (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
          (hybBaseTy (Pt := Pt) (ℓ := ℓ))
          (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ))
      (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
        (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) t <$>
        c.eval ρ) :=
  Computational.Proofs.ReductionDsl.FsAtomicMacros.compilePureComp_coinSimEquiv
    (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
    (hybOpMacro_eval_local ℓ Pt C encT idOf hinj)
    (fun s x => by
      cases s with
      | inl u =>
        cases u; rcases x with ⟨i, a⟩
        refine (Computational.Proofs.ReductionDsl.FsAtomicOps.sampleIdealComp_coinSimEquiv
          ℓ Pt C encT (I := slotOtccaTargetIface ℓ Pt)
          (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
          (fun b _ => by cases b <;> rfl) (i, ReductionDsl.fig8PubAdV a)).trans
          (CoinSimEquiv.of_eq ?_)
        have hsl : ReductionDsl.slotAdOfV (ℓ := ℓ) (Pt := Pt)
            (i, ReductionDsl.fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
          simp [ReductionDsl.slotAdOfV,
            Computational.Proofs.ReductionDsl.FsAtomicMacros.fig8PubAdOfV_fig8PubAdV]
        rw [hsl]
        dsimp only [multiMacroBundle, Iface.withSamp, ReductionDsl.Samplers.sum,
          CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
          slotOtccaTargetIface, Iface.liftP, toVal,
          Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen, hybBaseTy, mapTy,
          CryptoGames.FSAEAD.Costed.bt]
        rfl
      | inr t =>
        rcases t with _ | N | (_ | _)
        · exact CoinSimEquiv.of_eq rfl
        · exact CoinSimEquiv.of_eq (by
            dsimp only [multiMacroBundle, slotOtccaTargetIface, Iface.withSamp,
              ReductionDsl.Samplers.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaIface,
              Iface.liftP, ReductionDsl.unifSamplers,
              CryptoGames.FSAEAD.Costed.fsStateSampleSort, CryptoGames.FSAEAD.Costed.fsSig,
              Comp.eval, ReductionDsl.atomicBaseSamplers, ReductionDsl.AtomicBaseUnif.sort,
              ReductionDsl.AtomicSort.den, toVal,
              Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen, hybBaseTy, mapTy]
            exact (id_map _).symm)
        · exact CoinSimEquiv.of_eq rfl
        · exact CoinSimEquiv.of_eq rfl)
    (fun g x => by
      cases g
      · apply CoinSimEquiv.of_eq
        dsimp only [multiMacroBundle, slotOtccaTargetIface, Iface.withSamp,
          CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, Ty.denote, Comp.eval, Expr.eval, hybBaseTy, mapTy,
          toVal, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen,
          ReductionDsl.slotAdOfV, id] at x ⊢
        rcases x with ⟨⟨i, a⟩, m⟩
        simp only [Computational.Proofs.ReductionDsl.FsAtomicOps.env_get_zero, Functor.map_map]
        rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.fig8PubAdOfV_fig8PubAdV]
      · apply CoinSimEquiv.of_eq
        dsimp only [multiMacroBundle, slotOtccaTargetIface, Iface.withSamp,
          CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, Ty.denote, Comp.eval, Expr.eval, hybBaseTy, mapTy,
          toVal, Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen,
          ReductionDsl.slotAdOfV, id] at x ⊢
        rcases x with ⟨⟨i, a⟩, e⟩
        simp only [Computational.Proofs.ReductionDsl.FsAtomicOps.env_get_zero, Functor.map_map]
        rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.fig8PubAdOfV_fig8PubAdV,
          Computational.Proofs.ReductionDsl.FsAtomicMacros.wireSaltCtOfV_wireSaltCtV]
        congr 1; funext r; cases r <;> rfl)
    c ρ

private theorem initSlotSessComp_coinSimEquiv (hinj : Function.Injective encT) :
    CoinSimEquiv (IfaceF).fwdU
      ((initSlotSessComp ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam)).eval .nil)
      ((IfaceF).liftP (encSlotSessSt ℓ Pt <$>
        CryptoVerification.E2E.Signed.SessionFS.fsSlotInit
          (pure fun _ => ({} : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)))) := by
  refine CoinSimEquiv.of_eq ?_
  have hbind : ∀ {α β : Type} (p : ProbComp α) (k : α → ProbComp β),
      (IfaceF).liftP (p >>= k) = (IfaceF).liftP p >>= fun x => (IfaceF).liftP (k x) := by
    intro α β p k
    simp [Iface.liftP]
  dsimp only [initSlotSessComp, Comp.eval, CryptoVerification.E2E.Signed.SessionFS.fsSlotInit]
  have hmap :
      (encSlotSessSt ℓ Pt <$>
        (do
          let σ ← (pure fun _ => ({} : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt))
          let b ← ($ᵗ Bool : ProbComp Bool)
          pure (CryptoGames.FSAEAD.Thm5.hInit b .unknown, σ))) =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        pure (encSlotSessSt ℓ Pt
          (CryptoGames.FSAEAD.Thm5.hInit b .unknown,
           fun _ => ({} : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)))) := by
    simp
  rw [hmap, hbind]
  refine bind_congr fun b => ?_
  dsimp only [Expr.eval]
  rw [initHybSessStExpr_eval ℓ Pt C Dh encPt encT idOf lam hinj b]
  rfl

omit [Zero Pt] [SampleableType Pt] in
private lemma slot_multiTransmit_otEncBad_zero
    (N : ℕ) (la : Bool) (a : Header Pt × LibsignalMsgPublicPart) (m : Plain ℓ)
    (ha : atomicShortB a.2 = true)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt) :
    ((CryptoGames.FSAEAD.Thm5.multiTransmitHWith
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) (hp N 0 la) N
      (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
      (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
      (a, m)).run s).IsQueryBoundP
      (fun q => CryptoGames.AEADScheme.otEncBad
        (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) q = true) 0 := by
  have hQu : ∀ u, ¬ CryptoGames.AEADScheme.otEncBad (M := Plain ℓ) (C := LCt)
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) (.inl u) = true := by
    intro u; simp [CryptoGames.AEADScheme.otEncBad]
  unfold CryptoGames.FSAEAD.Thm5.multiTransmitHWith
  refine (CryptoGames.FSAEAD.Thm5.qb_bind0 CryptoGames.FSAEAD.Thm5.qb_getH fun st => ?_) s
  split_ifs
  · exact CryptoGames.FSAEAD.Thm5.qb_pure _ _
  · refine CryptoGames.FSAEAD.Thm5.qb_bind0
      (CryptoGames.FSAEAD.Thm5.qb_genUpTo hQu (lChainPRG C.F) (hp N 0 la)
        (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) _) fun _ => ?_
    refine CryptoGames.FSAEAD.Thm5.qb_bind_r
      (CryptoGames.FSAEAD.Thm5.qb_multiEncIdx_at
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) hQu N _ a m
        (fun _ _ => by simp [CryptoGames.AEADScheme.otEncBad, ha])) fun _ => ?_
    exact CryptoGames.FSAEAD.Thm5.qb_bind0 (CryptoGames.FSAEAD.Thm5.qb_modifyH _) fun _ =>
      CryptoGames.FSAEAD.Thm5.qb_pure _ _

omit [Zero Pt] [SampleableType Pt] in
private lemma slot_multiChallenge_otEncBad_zero
    (N : ℕ) (la : Bool) (a : Header Pt × LibsignalMsgPublicPart) (m0 m1 : Plain ℓ)
    (ha : atomicShortB a.2 = true)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt) :
    ((CryptoGames.FSAEAD.Thm5.multiChallengeHWith
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) (hp N 0 la) N
      (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
      (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
      (a, m0, m1)).run s).IsQueryBoundP
      (fun q => CryptoGames.AEADScheme.otEncBad
        (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) q = true) 0 := by
  have hQu : ∀ u, ¬ CryptoGames.AEADScheme.otEncBad (M := Plain ℓ) (C := LCt)
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) (.inl u) = true := by
    intro u; simp [CryptoGames.AEADScheme.otEncBad]
  unfold CryptoGames.FSAEAD.Thm5.multiChallengeHWith
  refine (CryptoGames.FSAEAD.Thm5.qb_bind0 CryptoGames.FSAEAD.Thm5.qb_getH fun st => ?_) s
  split_ifs
  · exact CryptoGames.FSAEAD.Thm5.qb_pure _ _
  all_goals
    refine CryptoGames.FSAEAD.Thm5.qb_bind0
      (CryptoGames.FSAEAD.Thm5.qb_genUpTo hQu (lChainPRG C.F) (hp N 0 la)
        (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F)) _) fun _ => ?_
    refine CryptoGames.FSAEAD.Thm5.qb_bind_r
      (CryptoGames.FSAEAD.Thm5.qb_multiEncIdx_at
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) hQu N _ a _
        (fun _ _ => by simp [CryptoGames.AEADScheme.otEncBad, ha])) fun _ => ?_
    exact CryptoGames.FSAEAD.Thm5.qb_bind0 (CryptoGames.FSAEAD.Thm5.qb_modifyH _) fun _ =>
      CryptoGames.FSAEAD.Thm5.qb_pure _ _

omit [Zero Pt] [SampleableType Pt] in
private lemma slot_multiNonEnc_otEncBad_zero
    (N : ℕ) (la : Bool)
    (t : (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt).Domain)
    (hnoEnc : CryptoVerification.E2E.Signed.SessionQueries.fsEncQ t = false)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt) :
    ((CryptoGames.FSAEAD.Thm5.multiOraclesWith
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp N 0 la) N
      (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
      (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
      t).run s).IsQueryBoundP
      (fun q => CryptoGames.AEADScheme.otEncBad
        (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) q = true) 0 := by
  refine (CryptoVerification.E2E.Signed.SessionQueries.qb_multiOraclesWith_step
    (lIdeal C protoSignalCodec ℓ encT)
    (lAeadR C protoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) maxForwardJumps
    (Q := fun q => CryptoGames.AEADScheme.otEncBad
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) q = true)
    (fun _ => by simp [CryptoGames.AEADScheme.otEncBad])
    N la 1 0
    (fun _ _ _ _ _ _ => Nat.zero_lt_one)
    (fun _ _ _ _ _ h => by simp [CryptoGames.AEADScheme.otEncBad] at h)
    t s).mono ?_
  simp [hnoEnc]

omit [Zero Pt] [SampleableType Pt] in
private lemma slot_fsSlotImpl_cs_eq
    (nf la : Bool) (N : ℕ)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt) :
    (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps N la
      (slotSaltProtoByNf ℓ Pt C encT idOf nf)
      (.inl (.inl (.inl (.inr ()))))).run (s, σ) =
    (fun r => (r.1, (r.2, σ))) <$>
      (CryptoVerification.E2E.Signed.SessionFS.fsImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
        (.inl (.inl (.inl (.inr ()))))).run s := by
  change (do
      let r ← (simulateQ
        (CryptoGames.FSAEAD.Thm5.slotLift (slotSaltProtoByNf ℓ Pt C encT idOf nf))
        ((CryptoGames.FSAEAD.Thm5.corruptSenderH
          (m := OracleComp (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
            (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt))
          (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
          (lChainPRG C.F) (hp N 0 la) ()).run s)).run σ
      return (r.1.1, (r.1.2, r.2))) =
    (fun r => (r.1, (r.2, σ))) <$>
      (CryptoGames.FSAEAD.Thm5.corruptSenderH (m := ProbComp)
        (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
        (lChainPRG C.F) (hp 0 0 la) ()).run s
  rcases s with ⟨st, sl⟩
  unfold CryptoGames.FSAEAD.Thm5.corruptSenderH CryptoGames.FSAEAD.Thm5.senderKey
    CryptoGames.FSAEAD.Thm5.reveal
  have hla1 : (hp N 0 la).la = la := rfl
  have hla2 : (hp 0 0 la).la = la := rfl
  simp only [hla1, hla2]
  dsimp only [CryptoGames.FSAEAD.Thm5.getH, CryptoGames.FSAEAD.Thm5.modifyH,
    CryptoGames.FSAEAD.Thm5.onH]
  simp only [StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure, pure_bind]
  cases hend : st.ended
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases la
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_mk, pure_bind]
      rcases st.senderCorruptedAt with _ | c <;>
        rcases st.corrKey with _ | w0 <;>
        rcases sl with ⟨w⟩ | _ | _ <;>
        simp [StateT.run_bind, StateT.run_pure, StateT.run_mk, StateT.run_modify,
          simulateQ_bind, simulateQ_pure,
          CryptoVerification.E2E.Signed.SessionFS.slotLift_liftM_run,
          map_eq_bind_pure_comp]
    · simp [StateT.run_pure, StateT.run_mk, StateT.run_modify, simulateQ_pure]
  · simp [StateT.run_pure, simulateQ_pure]

omit [Zero Pt] [SampleableType Pt] in
private lemma slotLift_slotSaltImplByNf_proto_eq_of_not_otEncBad (nf : Bool)
    (t : (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt).Domain)
    (st : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (ht : ¬ CryptoGames.AEADScheme.otEncBad
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) t = true) :
    (CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf) t).run st =
      (CryptoGames.FSAEAD.Thm5.slotLift (slotSaltProtoByNf ℓ Pt C encT idOf nf) t).run st := by
  rcases t with u | (⟨h, m⟩ | ⟨h, e⟩)
  · simp only [CryptoGames.FSAEAD.Thm5.slotLift_inl]
  · simp only [CryptoGames.FSAEAD.Thm5.slotLift_inr, CryptoGames.FSAEAD.Thm5.slotLiftOtcca]
    rw [slotSaltImplByNf_proto_eq_of_not_otEncBad ℓ Pt C encT idOf nf (.inr (.inl (h, m))) ht]
  · simp only [CryptoGames.FSAEAD.Thm5.slotLift_inr, CryptoGames.FSAEAD.Thm5.slotLiftOtcca]
    rw [slotSaltImplByNf_proto_eq_of_not_otEncBad ℓ Pt C encT idOf nf (.inr (.inr (h, e))) ht]

private theorem slotTrStep_coinSimEquiv (hinj : Function.Injective encT)
    (nf la : Bool) (qSim N n : ℕ)
    (hdr : Header Pt) (pv : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m : Plain ℓ)
    (hshort : atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv) = true)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (hks : s.1.lastSentIdx ≤ s.1.keys.length)
    (hσ : ∀ i, (σ i).table.length ≤ n)
    (hn1 : n + 1 ≤ qSim) :
    CoinSimEquiv (IfaceF).fwdU
      ((slotTrStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim N).eval
        (.cons ((hdr, pv), m) (.cons (encSlotSessSt ℓ Pt (s, σ)) .nil)))
      ((IfaceF).liftP
        (Prod.map (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) (encSlotSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps N la
            (slotSaltProtoByNf ℓ Pt C encT idOf nf)
            (.inl (.inl (.inl (.inl (.inl (
              (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv), m))))))).run (s, σ))) := by
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := CryptoGames.OTCCA.Costed.otccaIface
    (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1
  let I_m := I₀.withSamp
    (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))
  let O_src := Ops.sum
    (CryptoGames.PRG.Costed.prgOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
      (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
    (CryptoGames.OTCCA.Costed.otccaOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))
  let sIdeal : ∀ {Δ}, Expr O_src Δ (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad)) →
      Comp O_src I_m Δ (CryptoGames.FSAEAD.Costed.bt .ct) := fun ia =>
    Comp.sample (I := I_m) (Sum.inl ()) ia
  let sEnc : ∀ {Δ},
      Expr O_src Δ (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .msg)) →
      Comp O_src I_m Δ (CryptoGames.FSAEAD.Costed.bt .ct) := fun iam =>
    .bind (Comp.query (I := I_m) CryptoGames.OTCCA.Costed.OtccaTag.enc iam)
      (.caseOpt (.var .zero) (sIdeal (.fst (exprWk1 iam))) (.ret (.var .zero)))
  have hliftP : ∀ {α : Type} (p : ProbComp α),
      I₀.liftP p = (liftM p : OracleComp (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α) :=
    fun p => CryptoGames.FSAEAD.Thm5.Costed.otccaIface_liftP _ _ _ ideal 1 p
  have hIdeal : CryptoGames.FSAEAD.Thm5.Costed.SampleIdealRel (I := I_m) ae G 1 1 sIdeal ideal := by
    intro Δ ρ' ia
    dsimp only [sIdeal, Comp.eval, CryptoGames.FSAEAD.Thm5.Costed.liftP_withSamp,
      CryptoGames.FSAEAD.Thm5.Costed.samp_withSamp_inl,
      CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers]
    exact hliftP _
  have hEnc : CryptoGames.FSAEAD.Thm5.Costed.SpecialEncRel (I := I_m) ae G 1 1
      (some sEnc) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal)) := by
    intro Δ ρ' iam
    dsimp only [sEnc, CryptoGames.FSAEAD.Thm5.otOpsWith, Comp.eval]
    change ((id <$> (query (spec := unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
        (Sum.inr (Sum.inl (iam.eval ρ'))))) >>= _) = _
    rw [id_map]
    refine bind_congr fun r => ?_
    cases r with
    | none =>
      change (sIdeal (.fst (exprWk1 iam))).eval
        (Env.cons (t := .opt (CryptoGames.FSAEAD.Costed.bt .ct)) none ρ') =
        liftM (ideal (iam.eval ρ').1)
      rw [hIdeal]
      dsimp only [Expr.eval]
      erw [exprWk1_eval_slot]
    | some c =>
      rfl
  let a : Header Pt × LibsignalMsgPublicPart :=
    (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv)
  let ρ_src : Env [.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg),
      CryptoGames.FSAEAD.Thm5.Costed.stTy] :=
    .cons (a, m) (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) .nil)
  have hρ : Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
      (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src =
      .cons ((hdr, pv), m) (.cons (encHybSessSt ℓ Pt s) .nil) := by
    change Env.cons (t := .prod fig8PubAdT PlainT)
        ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt)
          (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv)), m)
        (Env.cons (t := hybSessStTy ℓ Pt) (encHybSessSt ℓ Pt s) Env.nil) = _
    rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubV_lpubOfV]
  let oa_p := (CryptoGames.FSAEAD.Thm5.multiTransmitHWith
    (lIdeal C protoSignalCodec ℓ encT)
    (lAeadR C protoSignalCodec ℓ encT idOf)
    G (hp N 0 la) N (CryptoGames.FSAEAD.Thm5.DG G)
    (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
    (a, m)).run s
  have hoa_eq :
      (CryptoGames.FSAEAD.Thm5.multiTransmitHWith ideal ae G (hp N 0 la) N
        (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
        (a, m)).run s = oa_p := by
    have henc := fun i => slot_multiEncIdxWith_clamped_eq ℓ Pt C encT idOf N i a m hshort
    dsimp only [oa_p, ideal, ae, G]
    unfold CryptoGames.FSAEAD.Thm5.multiTransmitHWith
    dsimp only [hp, Option.getD]
    simp only [henc]
  let src : Comp O_src I_m
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.transmitBody (I₀ := I₀) ae G 1 1
        maxForwardJumps N N sIdeal (some sEnc))
  let c_hyb : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt)
      [.prod fig8PubAdT PlainT, hybSessStTy ℓ Pt]
      (.prod (.opt lctT) (hybSessStTy ℓ Pt)) :=
    compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src
  have hc : CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (c_hyb.eval (.cons ((hdr, pv), m) (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((fun z => (z.1.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt)), encHybSessSt ℓ Pt z.2)) <$> oa_p) := by
    have heval : c_hyb.eval (.cons ((hdr, pv), m) (.cons (encHybSessSt ℓ Pt s) .nil)) =
        (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src).eval
          (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
            (hybBaseTy (Pt := Pt) (ℓ := ℓ))
            (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src) :=
      congrArg c_hyb.eval hρ.symm
    rw [heval]
    refine (compilePureComp_multi_coinSimEquiv ℓ Pt C encT idOf hinj src ρ_src).trans
      (CoinSimEquiv.of_eq ?_)
    have hsrc :
        src.eval ρ_src =
        (CryptoGames.FSAEAD.Thm5.Costed.transmitBody (I₀ := I₀) ae G 1 1
          maxForwardJumps N N sIdeal (some sEnc)).eval
          (.cons ((a, m), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) := by
      dsimp only [src, Comp.eval]; rw [pure_bind]; rfl
    have hbody := CryptoGames.FSAEAD.Thm5.Costed.transmitBody_eval ae G 1 1 hliftP ρ_src
      maxForwardJumps N (hp N 0 la) rfl ideal sIdeal hIdeal (some sEnc)
      (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal)) hEnc a m s hks
    change (CryptoGames.FSAEAD.Thm5.Costed.transmitBody (I₀ := I₀) ae G 1 1
        maxForwardJumps N N sIdeal (some sEnc)).eval
        (.cons ((a, m), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) =
      Prod.map id CryptoGames.FSAEAD.Thm5.Costed.encSt <$>
        (CryptoGames.FSAEAD.Thm5.multiTransmitHWith ideal ae G (hp N 0 la) N
          (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
          (a, m)).run s at hbody
    erw [hsrc, hbody, hoa_eq, Functor.map_map]
    refine congrFun (congrArg Functor.map ?_) _
    funext ⟨r1, s'⟩
    rcases r1 with _ | ⟨i, c⟩ <;> rfl
  have hqb1 : oa_p.IsQueryBoundP (fun q => q.isRight = true) 1 :=
    slot_multiOraclesWith_qb_one ℓ Pt C (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) N la (.inl (.inl (.inl (.inl (.inl (a, m)))))) s
  dsimp only [slotTrStep]
  refine (liftSlotHybStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj nf qSim c_hyb
    ((hdr, pv), m) s σ (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) oa_p hc hqb1 hσ hn1).trans
    (CoinSimEquiv.of_eq ?_)
  refine congrArg (IfaceF).liftP ?_
  have hdis := run_simulateQ_eq_of_dis_slot
    (impl₁ := CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf))
    (impl₂ := CryptoGames.FSAEAD.Thm5.slotLift (slotSaltProtoByNf ℓ Pt C encT idOf nf))
    oa_p
    (slot_multiTransmit_otEncBad_zero ℓ Pt C encT idOf N la a m hshort s) σ
    (slotLift_slotSaltImplByNf_proto_eq_of_not_otEncBad ℓ Pt C encT idOf nf)
  rw [hdis]
  dsimp only [CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl,
    CryptoGames.FSAEAD.Thm5.multiOraclesWith, StateT.run_mk, oa_p, G, a]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
  rfl

private theorem slotChStep_coinSimEquiv (hinj : Function.Injective encT)
    (nf la : Bool) (qSim N n : ℕ)
    (hdr : Header Pt) (pv0 : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) (m0 m1 : Plain ℓ)
    (hshort : atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0) = true)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (hks : s.1.lastSentIdx ≤ s.1.keys.length)
    (hσ : ∀ i, (σ i).table.length ≤ n)
    (hn1 : n + 1 ≤ qSim) :
    CoinSimEquiv (IfaceF).fwdU
      ((slotChStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim N).eval
        (.cons ((hdr, pv0), (m0, m1)) (.cons (encSlotSessSt ℓ Pt (s, σ)) .nil)))
      ((IfaceF).liftP
        (Prod.map (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) (encSlotSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps N la
            (slotSaltProtoByNf ℓ Pt C encT idOf nf)
            (.inl (.inl (.inl (.inl (.inr (
              (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0), m0, m1))))))).run (s, σ))) := by
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := CryptoGames.OTCCA.Costed.otccaIface
    (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1
  let I_m := I₀.withSamp
    (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))
  let O_src := Ops.sum
    (CryptoGames.PRG.Costed.prgOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
      (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
    (CryptoGames.OTCCA.Costed.otccaOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))
  let sIdeal : ∀ {Δ}, Expr O_src Δ (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad)) →
      Comp O_src I_m Δ (CryptoGames.FSAEAD.Costed.bt .ct) := fun ia =>
    Comp.sample (I := I_m) (Sum.inl ()) ia
  let sEnc : ∀ {Δ},
      Expr O_src Δ (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .msg)) →
      Comp O_src I_m Δ (CryptoGames.FSAEAD.Costed.bt .ct) := fun iam =>
    .bind (Comp.query (I := I_m) CryptoGames.OTCCA.Costed.OtccaTag.enc iam)
      (.caseOpt (.var .zero) (sIdeal (.fst (exprWk1 iam))) (.ret (.var .zero)))
  have hliftP : ∀ {α : Type} (p : ProbComp α),
      I₀.liftP p = (liftM p : OracleComp (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α) :=
    fun p => CryptoGames.FSAEAD.Thm5.Costed.otccaIface_liftP _ _ _ ideal 1 p
  have hIdeal : CryptoGames.FSAEAD.Thm5.Costed.SampleIdealRel (I := I_m) ae G 1 1 sIdeal ideal := by
    intro Δ ρ' ia
    dsimp only [sIdeal, Comp.eval, CryptoGames.FSAEAD.Thm5.Costed.liftP_withSamp,
      CryptoGames.FSAEAD.Thm5.Costed.samp_withSamp_inl,
      CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers]
    exact hliftP _
  have hEnc : CryptoGames.FSAEAD.Thm5.Costed.SpecialEncRel (I := I_m) ae G 1 1
      (some sEnc) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal)) := by
    intro Δ ρ' iam
    dsimp only [sEnc, CryptoGames.FSAEAD.Thm5.otOpsWith, Comp.eval]
    change ((id <$> (query (spec := unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
        (Sum.inr (Sum.inl (iam.eval ρ'))))) >>= _) = _
    rw [id_map]
    refine bind_congr fun r => ?_
    cases r with
    | none =>
      change (sIdeal (.fst (exprWk1 iam))).eval
        (Env.cons (t := .opt (CryptoGames.FSAEAD.Costed.bt .ct)) none ρ') =
        liftM (ideal (iam.eval ρ').1)
      rw [hIdeal]
      dsimp only [Expr.eval]
      erw [exprWk1_eval_slot]
    | some c =>
      rfl
  let a : Header Pt × LibsignalMsgPublicPart :=
    (hdr, ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0)
  let ρ_src : Env [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod (CryptoGames.FSAEAD.Costed.bt .msg) (CryptoGames.FSAEAD.Costed.bt .msg)),
      CryptoGames.FSAEAD.Thm5.Costed.stTy] :=
    .cons (a, (m0, m1)) (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) .nil)
  have hρ : Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
      (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src =
      .cons ((hdr, pv0), (m0, m1)) (.cons (encHybSessSt ℓ Pt s) .nil) := by
    change Env.cons (t := .prod fig8PubAdT (.prod PlainT PlainT))
        ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt)
          (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0)), (m0, m1))
        (Env.cons (t := hybSessStTy ℓ Pt) (encHybSessSt ℓ Pt s) Env.nil) = _
    rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubV_lpubOfV]
  let oa_p := (CryptoGames.FSAEAD.Thm5.multiChallengeHWith
    (lIdeal C protoSignalCodec ℓ encT)
    (lAeadR C protoSignalCodec ℓ encT idOf)
    G (hp N 0 la) N (CryptoGames.FSAEAD.Thm5.DG G)
    (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
    (a, m0, m1)).run s
  have hoa_eq :
      (CryptoGames.FSAEAD.Thm5.multiChallengeHWith ideal ae G (hp N 0 la) N
        (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
        (a, m0, m1)).run s = oa_p := by
    have henc := fun i msg => slot_multiEncIdxWith_clamped_eq ℓ Pt C encT idOf N i a msg hshort
    dsimp only [oa_p, ideal, ae, G]
    unfold CryptoGames.FSAEAD.Thm5.multiChallengeHWith
    dsimp only [hp, Option.getD]
    simp only [henc]
  let src : Comp O_src I_m
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod (CryptoGames.FSAEAD.Costed.bt .msg) (CryptoGames.FSAEAD.Costed.bt .msg)),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.challengeBody (I₀ := I₀) ae G 1 1
        maxForwardJumps N N sIdeal (some sEnc))
  let c_hyb : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt)
      [.prod fig8PubAdT (.prod PlainT PlainT), hybSessStTy ℓ Pt]
      (.prod (.opt lctT) (hybSessStTy ℓ Pt)) :=
    compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src
  have hc : CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (c_hyb.eval (.cons ((hdr, pv0), (m0, m1)) (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((fun z => (z.1.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt)), encHybSessSt ℓ Pt z.2)) <$> oa_p) := by
    have heval : c_hyb.eval (.cons ((hdr, pv0), (m0, m1)) (.cons (encHybSessSt ℓ Pt s) .nil)) =
        (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src).eval
          (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
            (hybBaseTy (Pt := Pt) (ℓ := ℓ))
            (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src) :=
      congrArg c_hyb.eval hρ.symm
    rw [heval]
    refine (compilePureComp_multi_coinSimEquiv ℓ Pt C encT idOf hinj src ρ_src).trans
      (CoinSimEquiv.of_eq ?_)
    have hsrc :
        src.eval ρ_src =
        (CryptoGames.FSAEAD.Thm5.Costed.challengeBody (I₀ := I₀) ae G 1 1
          maxForwardJumps N N sIdeal (some sEnc)).eval
          (.cons ((a, (m0, m1)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) := by
      dsimp only [src, Comp.eval]; rw [pure_bind]; rfl
    have hbody := CryptoGames.FSAEAD.Thm5.Costed.challengeBody_eval ae G 1 1 hliftP ρ_src
      maxForwardJumps N (hp N 0 la) rfl ideal sIdeal hIdeal (some sEnc)
      (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal)) hEnc a m0 m1 s hks
    change (CryptoGames.FSAEAD.Thm5.Costed.challengeBody (I₀ := I₀) ae G 1 1
        maxForwardJumps N N sIdeal (some sEnc)).eval
        (.cons ((a, (m0, m1)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) =
      Prod.map id CryptoGames.FSAEAD.Thm5.Costed.encSt <$>
        (CryptoGames.FSAEAD.Thm5.multiChallengeHWith ideal ae G (hp N 0 la) N
          (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
          (a, m0, m1)).run s at hbody
    erw [hsrc, hbody, hoa_eq, Functor.map_map]
    refine congrFun (congrArg Functor.map ?_) _
    funext ⟨r1, s'⟩
    rcases r1 with _ | ⟨i, c⟩ <;> rfl
  have hqb1 : oa_p.IsQueryBoundP (fun q => q.isRight = true) 1 :=
    slot_multiOraclesWith_qb_one ℓ Pt C (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) N la (.inl (.inl (.inl (.inl (.inr (a, m0, m1)))))) s
  dsimp only [slotChStep]
  refine (liftSlotHybStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj nf qSim c_hyb
    ((hdr, pv0), (m0, m1)) s σ (Option.map (ReductionDsl.lctV (ℓ := ℓ) (Pt := Pt))) oa_p hc hqb1 hσ hn1).trans
    (CoinSimEquiv.of_eq ?_)
  refine congrArg (IfaceF).liftP ?_
  have hdis := run_simulateQ_eq_of_dis_slot
    (impl₁ := CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf))
    (impl₂ := CryptoGames.FSAEAD.Thm5.slotLift (slotSaltProtoByNf ℓ Pt C encT idOf nf))
    oa_p
    (slot_multiChallenge_otEncBad_zero ℓ Pt C encT idOf N la a m0 m1 hshort s) σ
    (slotLift_slotSaltImplByNf_proto_eq_of_not_otEncBad ℓ Pt C encT idOf nf)
  rw [hdis]
  dsimp only [CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl,
    CryptoGames.FSAEAD.Thm5.multiOraclesWith, StateT.run_mk, oa_p, G, a]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
  rfl

private theorem slotCsStep_coinSimEquiv (hinj : Function.Injective encT)
    (nf la : Bool) (qSim N : ℕ)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (hsent : s.1.lastSentIdx ≤ qSim) :
    CoinSimEquiv (IfaceF).fwdU
      ((slotCsStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) qSim la).eval
        (.cons () (.cons (encSlotSessSt ℓ Pt (s, σ)) .nil)))
      ((IfaceF).liftP
        (Prod.map (Option.map (ReductionDsl.fsSendStV (ℓ := ℓ) (Pt := Pt))) (encSlotSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps N la
            (slotSaltProtoByNf ℓ Pt C encT idOf nf)
            (.inl (.inl (.inl (.inr ()))))).run (s, σ))) := by
  dsimp only [slotCsStep, Comp.eval, Expr.eval, encSlotSessSt]
  simp only [env_get_zero, env_get_succ, pure_bind]
  rw [renSwap2_eval, slot_fsSlotImpl_cs_eq ℓ Pt C encT idOf nf la N s σ, Functor.map_map,
    map_eq_bind_pure_comp]
  refine coinSimEquiv_liftP_map_bind_of_support IfaceF
    (Prod.map (Option.map (ReductionDsl.fsSendStV (ℓ := ℓ) (Pt := Pt))) (encHybSessSt ℓ Pt))
    (realCsStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj qSim 0 la s hsent)
    fun ⟨r1, s'⟩ _ => ?_
  dsimp only [Prod.map, Function.comp_def, Expr.eval, encSlotSessSt]
  exact coinSimEquiv_liftP_pure IfaceF _

private theorem slotDlStep_coinSimEquiv (hinj : Function.Injective encT)
    (nf la : Bool) (qSim N n : ℕ)
    (hdr : Header Pt) (cv : (lctT (ℓ := ℓ) (Pt := Pt)).denote)
    (p : LibsignalMsgPublicPart)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (hrecv : s.1.receiverIdx ≤ s.1.keys.length)
    (htr : s.1.inTransit.length ≤ qSim)
    (hch : s.1.challengesInTransit.length ≤ qSim)
    (hσ : ∀ i, (σ i).table.length ≤ n)
    (hn1 : n + 1 ≤ qSim) :
    CoinSimEquiv (IfaceF).fwdU
      ((slotDlStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim N la).eval
        (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
          (.cons (encSlotSessSt ℓ Pt (s, σ)) .nil)))
      ((IfaceF).liftP
        (Prod.map
          (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
          (encSlotSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps N la
            (slotSaltProtoByNf ℓ Pt C encT idOf nf)
            (.inl (.inr ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv)))).run (s, σ))) := by
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := CryptoGames.OTCCA.Costed.otccaIface
    (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1
  let I_m := I₀.withSamp
    (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))
  let O_src := Ops.sum
    (CryptoGames.PRG.Costed.prgOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
      (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
    (CryptoGames.OTCCA.Costed.otccaOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))
  let sDec : ∀ {Δ},
      Expr O_src Δ (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .ct)) →
      Comp O_src I_m Δ (.opt (CryptoGames.FSAEAD.Costed.bt .msg)) := fun iae =>
    Comp.query (I := I_m) CryptoGames.OTCCA.Costed.OtccaTag.dec iae
  have hliftP : ∀ {α : Type} (p : ProbComp α),
      I₀.liftP p = (liftM p : OracleComp (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α) :=
    fun p => CryptoGames.FSAEAD.Thm5.Costed.otccaIface_liftP _ _ _ ideal 1 p
  have hDec : CryptoGames.FSAEAD.Thm5.Costed.SpecialDecRel (I := I_m) ae G 1 1
      (some sDec) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal)) := by
    intro Δ ρ' iae
    change id <$> (query (spec := unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
        (Sum.inr (Sum.inr (iae.eval ρ')))) =
      (query (spec := unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
        (Sum.inr (Sum.inr (iae.eval ρ'))))
    exact id_map _
  let stT := CryptoGames.FSAEAD.Thm5.Costed.stTy
    (CK := BitVec 256) (MK := BitVec 256)
    (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
  let c0 := ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv
  let ρ_src : Env [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)), stT] :=
    .cons ((hdr, p), (c0.1, c0.2)) (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) .nil)
  have hρ : Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
      (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src =
      .cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
        (.cons (encHybSessSt ℓ Pt s) .nil) := by
    rcases cv with ⟨i, wv⟩
    change Env.cons (t := .prod fig8PubAdT lctT)
        ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p),
         (i, ReductionDsl.wireSaltCtV (ℓ := ℓ) (Pt := Pt)
           (ReductionDsl.wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) wv)))
        (Env.cons (t := hybSessStTy ℓ Pt) (encHybSessSt ℓ Pt s) Env.nil) = _
    rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.wireSaltCtV_wireSaltCtOfV]
  let oa_p := (CryptoGames.FSAEAD.Thm5.multiDeliverH
    (lAeadR C protoSignalCodec ℓ encT idOf) G maxForwardJumps (hp N 0 la) N
    (CryptoGames.FSAEAD.Thm5.DG G)
    (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
    ((hdr, p), c0)).run s
  have hoa_eq :
      (CryptoGames.FSAEAD.Thm5.multiDeliverH ae G maxForwardJumps (hp N 0 la) N
        (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
        ((hdr, p), (c0.1, c0.2))).run s = oa_p := by
    have hrec : ∀ hint a c,
        CryptoGames.FSAEAD.Thm5.multiReceiveH ae G maxForwardJumps (hp N 0 la) N
          (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
          hint a c =
        CryptoGames.FSAEAD.Thm5.multiReceiveH (lAeadR C protoSignalCodec ℓ encT idOf) G
          maxForwardJumps (hp N 0 la) N (CryptoGames.FSAEAD.Thm5.DG G)
          (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
          hint a c := by
      intro hint a c
      dsimp only [ae, ideal, G]
      unfold CryptoGames.FSAEAD.Thm5.multiReceiveH
      dsimp only [hp, Option.getD]
      simp only [slot_multiDecIdx_clamped_eq ℓ Pt C encT idOf N]
      rfl
    have hc0 : (c0.1, c0.2) = c0 := Prod.eta c0
    rw [hc0]
    dsimp only [oa_p]
    unfold CryptoGames.FSAEAD.Thm5.multiDeliverH
    simp only [hrec]
  let src : Comp O_src I_m
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)), stT]
      (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg))) stT) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim N N la (some sDec))
  let c_hyb : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt)
      [.prod fig8PubAdT lctT, hybSessStTy ℓ Pt]
      (.prod (.opt (fsRrT PlainT)) (hybSessStTy ℓ Pt)) :=
    compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src
  have hc : CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (c_hyb.eval
        (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
          (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((fun z =>
        (z.1.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id),
         encHybSessSt ℓ Pt z.2)) <$> oa_p) := by
    have heval : c_hyb.eval
        (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
          (.cons (encHybSessSt ℓ Pt s) .nil)) =
        (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src).eval
          (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
            (hybBaseTy (Pt := Pt) (ℓ := ℓ))
            (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src) :=
      congrArg c_hyb.eval hρ.symm
    rw [heval]
    refine (compilePureComp_multi_coinSimEquiv ℓ Pt C encT idOf hinj src ρ_src).trans
      (CoinSimEquiv.of_eq ?_)
    have hsrc :
        src.eval ρ_src =
        (CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀) ae G 1 1
          maxForwardJumps qSim N N la (some sDec)).eval
          (.cons (((hdr, p), (c0.1, c0.2)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) := by
      dsimp only [src, Comp.eval]; rw [pure_bind]; rfl
    have hbody := CryptoGames.FSAEAD.Thm5.Costed.deliverBody_eval ae G 1 1 hliftP ρ_src
      maxForwardJumps qSim N (hp N 0 la) rfl (some sDec)
      (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal)) hDec (hdr, p) c0.1 c0.2 s hrecv htr hch
    change Prod.map (Option.map CryptoGames.FSAEAD.Costed.rrDecM) id <$>
        (CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀) ae G 1 1
          maxForwardJumps qSim N N la (some sDec)).eval
          (.cons (((hdr, p), (c0.1, c0.2)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) =
      Prod.map id CryptoGames.FSAEAD.Thm5.Costed.encSt <$>
        (CryptoGames.FSAEAD.Thm5.multiDeliverH ae G maxForwardJumps (hp N 0 la) N
          (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
          ((hdr, p), (c0.1, c0.2))).run s at hbody
    have hmap {F : Type → Type} [Functor F] [LawfulFunctor F] (p0 : F _) :
        toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
          (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
          (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg))) stT) <$> p0 =
        Prod.map
          (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
          (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
            (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) stT) <$>
          (Prod.map (Option.map CryptoGames.FSAEAD.Costed.rrDecM) id <$> p0) := by
      rw [Functor.map_map]
      refine congrFun (congrArg Functor.map ?_) p0
      funext ⟨r1, s'⟩
      rcases r1 with _ | (⟨⟩ | ⟨st, _ | m⟩) <;> rfl
    erw [hsrc, hmap, hbody, hoa_eq, Functor.map_map]
    refine congrFun (congrArg Functor.map ?_) _
    funext ⟨r1, s'⟩
    rfl
  have hqb1 : oa_p.IsQueryBoundP (fun q => q.isRight = true) 1 :=
    slot_multiOraclesWith_qb_one ℓ Pt C (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) N la (.inl (.inr ((hdr, p), c0))) s
  dsimp only [slotDlStep]
  refine (liftSlotHybStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj nf qSim c_hyb
    ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv) s σ
    (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
    oa_p hc hqb1 hσ hn1).trans
    (CoinSimEquiv.of_eq ?_)
  refine congrArg (IfaceF).liftP ?_
  have hdis := run_simulateQ_eq_of_dis_slot
    (impl₁ := CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf))
    (impl₂ := CryptoGames.FSAEAD.Thm5.slotLift (slotSaltProtoByNf ℓ Pt C encT idOf nf))
    oa_p
    (slot_multiNonEnc_otEncBad_zero ℓ Pt C encT idOf N la (.inl (.inr ((hdr, p), c0))) rfl s) σ
    (slotLift_slotSaltImplByNf_proto_eq_of_not_otEncBad ℓ Pt C encT idOf nf)
  rw [hdis]
  dsimp only [CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl,
    CryptoGames.FSAEAD.Thm5.multiOraclesWith, StateT.run_mk, oa_p, G, c0]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
  rfl

private theorem slotIjStep_coinSimEquiv (hinj : Function.Injective encT)
    (nf la : Bool) (qSim N n : ℕ)
    (hdr : Header Pt) (cv : (lctT (ℓ := ℓ) (Pt := Pt)).denote)
    (p : LibsignalMsgPublicPart)
    (s : CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (hrecv : s.1.receiverIdx ≤ s.1.keys.length)
    (htr : s.1.inTransit.length ≤ qSim)
    (hch : s.1.challengesInTransit.length ≤ qSim)
    (hσ : ∀ i, (σ i).table.length ≤ n)
    (hn1 : n + 1 ≤ qSim) :
    CoinSimEquiv (IfaceF).fwdU
      ((slotIjStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim N la).eval
        (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
          (.cons (encSlotSessSt ℓ Pt (s, σ)) .nil)))
      ((IfaceF).liftP
        (Prod.map
          (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
          (encSlotSessSt ℓ Pt) <$>
          (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps N la
            (slotSaltProtoByNf ℓ Pt C encT idOf nf)
            (.inr ((hdr, p), ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv))).run (s, σ))) := by
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := CryptoGames.OTCCA.Costed.otccaIface
    (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1
  let I_m := I₀.withSamp
    (ReductionDsl.unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1))
  let O_src := Ops.sum
    (CryptoGames.PRG.Costed.prgOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
      (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
    (CryptoGames.OTCCA.Costed.otccaOps
      (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
      (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))
  let sDec : ∀ {Δ},
      Expr O_src Δ (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .ct)) →
      Comp O_src I_m Δ (.opt (CryptoGames.FSAEAD.Costed.bt .msg)) := fun iae =>
    Comp.query (I := I_m) CryptoGames.OTCCA.Costed.OtccaTag.dec iae
  have hliftP : ∀ {α : Type} (p : ProbComp α),
      I₀.liftP p = (liftM p : OracleComp (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α) :=
    fun p => CryptoGames.FSAEAD.Thm5.Costed.otccaIface_liftP _ _ _ ideal 1 p
  have hDec : CryptoGames.FSAEAD.Thm5.Costed.SpecialDecRel (I := I_m) ae G 1 1
      (some sDec) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal)) := by
    intro Δ ρ' iae
    change id <$> (query (spec := unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
        (Sum.inr (Sum.inr (iae.eval ρ')))) =
      (query (spec := unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
        (Sum.inr (Sum.inr (iae.eval ρ'))))
    exact id_map _
  let stT := CryptoGames.FSAEAD.Thm5.Costed.stTy
    (CK := BitVec 256) (MK := BitVec 256)
    (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)
  let c0 := ReductionDsl.lctOfV (ℓ := ℓ) (Pt := Pt) cv
  let ρ_src : Env [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)), stT] :=
    .cons ((hdr, p), (c0.1, c0.2)) (.cons (CryptoGames.FSAEAD.Thm5.Costed.encSt s) .nil)
  have hρ : Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
      (hybBaseTy (Pt := Pt) (ℓ := ℓ))
      (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src =
      .cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
        (.cons (encHybSessSt ℓ Pt s) .nil) := by
    rcases cv with ⟨i, wv⟩
    change Env.cons (t := .prod fig8PubAdT lctT)
        ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p),
         (i, ReductionDsl.wireSaltCtV (ℓ := ℓ) (Pt := Pt)
           (ReductionDsl.wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) wv)))
        (Env.cons (t := hybSessStTy ℓ Pt) (encHybSessSt ℓ Pt s) Env.nil) = _
    rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.wireSaltCtV_wireSaltCtOfV]
  let oa_p := (CryptoGames.FSAEAD.Thm5.multiInjectH
    (lAeadR C protoSignalCodec ℓ encT idOf) G maxForwardJumps (hp N 0 la) N
    (CryptoGames.FSAEAD.Thm5.DG G)
    (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
    ((hdr, p), c0)).run s
  have hoa_eq :
      (CryptoGames.FSAEAD.Thm5.multiInjectH ae G maxForwardJumps (hp N 0 la) N
        (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
        ((hdr, p), (c0.1, c0.2))).run s = oa_p := by
    have hrec : ∀ hint a c,
        CryptoGames.FSAEAD.Thm5.multiReceiveH ae G maxForwardJumps (hp N 0 la) N
          (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
          hint a c =
        CryptoGames.FSAEAD.Thm5.multiReceiveH (lAeadR C protoSignalCodec ℓ encT idOf) G
          maxForwardJumps (hp N 0 la) N (CryptoGames.FSAEAD.Thm5.DG G)
          (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
          hint a c := by
      intro hint a c
      dsimp only [ae, ideal, G]
      unfold CryptoGames.FSAEAD.Thm5.multiReceiveH
      dsimp only [hp, Option.getD]
      simp only [slot_multiDecIdx_clamped_eq ℓ Pt C encT idOf N]
      rfl
    have hc0 : (c0.1, c0.2) = c0 := Prod.eta c0
    rw [hc0]
    dsimp only [oa_p]
    unfold CryptoGames.FSAEAD.Thm5.multiInjectH
    simp only [hrec]
  let src : Comp O_src I_m
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)), stT]
      (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg))) stT) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim N N la (some sDec))
  let c_hyb : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt)
      [.prod fig8PubAdT lctT, hybSessStTy ℓ Pt]
      (.prod (.opt (fsRrT PlainT)) (hybSessStTy ℓ Pt)) :=
    compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src
  have hc : CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (c_hyb.eval
        (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
          (.cons (encHybSessSt ℓ Pt s) .nil)))
      ((fun z =>
        (z.1.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id),
         encHybSessSt ℓ Pt z.2)) <$> oa_p) := by
    have heval : c_hyb.eval
        (.cons ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv)
          (.cons (encHybSessSt ℓ Pt s) .nil)) =
        (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src).eval
          (Computational.Proofs.ReductionDsl.FsAtomicMacros.mapPureEnv
            (hybBaseTy (Pt := Pt) (ℓ := ℓ))
            (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) ρ_src) :=
      congrArg c_hyb.eval hρ.symm
    rw [heval]
    refine (compilePureComp_multi_coinSimEquiv ℓ Pt C encT idOf hinj src ρ_src).trans
      (CoinSimEquiv.of_eq ?_)
    have hsrc :
        src.eval ρ_src =
        (CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀) ae G 1 1
          maxForwardJumps qSim N N la (some sDec)).eval
          (.cons (((hdr, p), (c0.1, c0.2)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) := by
      dsimp only [src, Comp.eval]; rw [pure_bind]; rfl
    have hbody := CryptoGames.FSAEAD.Thm5.Costed.injectBody_eval ae G 1 1 hliftP ρ_src
      maxForwardJumps qSim N (hp N 0 la) rfl (some sDec)
      (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal)) hDec (hdr, p) c0.1 c0.2 s hrecv htr hch
    change Prod.map (Option.map CryptoGames.FSAEAD.Costed.rrDecM) id <$>
        (CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀) ae G 1 1
          maxForwardJumps qSim N N la (some sDec)).eval
          (.cons (((hdr, p), (c0.1, c0.2)), CryptoGames.FSAEAD.Thm5.Costed.encSt s) ρ_src) =
      Prod.map id CryptoGames.FSAEAD.Thm5.Costed.encSt <$>
        (CryptoGames.FSAEAD.Thm5.multiInjectH ae G maxForwardJumps (hp N 0 la) N
          (CryptoGames.FSAEAD.Thm5.DG G) (some (CryptoGames.FSAEAD.Thm5.otOpsWith ideal))
          ((hdr, p), (c0.1, c0.2))).run s at hbody
    have hmap {F : Type → Type} [Functor F] [LawfulFunctor F] (p0 : F _) :
        toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
          (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ))
          (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg))) stT) <$> p0 =
        Prod.map
          (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
          (toVal (hybBaseTy (Pt := Pt) (ℓ := ℓ))
            (Computational.Proofs.ReductionDsl.FsAtomicBundles.hybToDen (Pt := Pt) (ℓ := ℓ)) stT) <$>
          (Prod.map (Option.map CryptoGames.FSAEAD.Costed.rrDecM) id <$> p0) := by
      rw [Functor.map_map]
      refine congrFun (congrArg Functor.map ?_) p0
      funext ⟨r1, s'⟩
      rcases r1 with _ | (⟨⟩ | ⟨st, _ | m⟩) <;> rfl
    erw [hsrc, hmap, hbody, hoa_eq, Functor.map_map]
    refine congrFun (congrArg Functor.map ?_) _
    funext ⟨r1, s'⟩
    rfl
  have hqb1 : oa_p.IsQueryBoundP (fun q => q.isRight = true) 1 :=
    slot_multiOraclesWith_qb_one ℓ Pt C (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) N la (.inr ((hdr, p), c0)) s
  dsimp only [slotIjStep]
  refine (liftSlotHybStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj nf qSim c_hyb
    ((hdr, ReductionDsl.lpubV (ℓ := ℓ) (Pt := Pt) p), cv) s σ
    (Option.map (ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT) id))
    oa_p hc hqb1 hσ hn1).trans
    (CoinSimEquiv.of_eq ?_)
  refine congrArg (IfaceF).liftP ?_
  have hdis := run_simulateQ_eq_of_dis_slot
    (impl₁ := CryptoGames.FSAEAD.Thm5.slotLift (slotSaltImplByNf ℓ Pt C encT idOf nf))
    (impl₂ := CryptoGames.FSAEAD.Thm5.slotLift (slotSaltProtoByNf ℓ Pt C encT idOf nf))
    oa_p
    (slot_multiNonEnc_otEncBad_zero ℓ Pt C encT idOf N la (.inr ((hdr, p), c0)) rfl s) σ
    (slotLift_slotSaltImplByNf_proto_eq_of_not_otEncBad ℓ Pt C encT idOf nf)
  rw [hdis]
  dsimp only [CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl,
    CryptoGames.FSAEAD.Thm5.multiOraclesWith, StateT.run_mk, oa_p, G, c0]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
  rfl

private theorem slotStep_coinSimEquiv (hinj : Function.Injective encT)
    (stage la : Bool) (qR : ℕ)
    (g : FSAEADTag) (payload : ((IfaceF).dom g).denote)
    (endedPub : Bool)
    (os : Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ×
      (ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)))
    (n : ℕ) (hn : n < 2 * qR + 4)
    (hInv : SlotOptInv ℓ Pt n os)
    (hNoCr : g ≠ .cr)
    (hShort : ¬ CryptoGames.FSAEAD.encBadMsg
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (C := ℕ × LCt)
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
      ((IfaceF).enc g payload) = true) :
    let N := authHopCutoff maxForwardJumps qR la
    let qSim := 2 * qR + 4
    CoinSimEquiv (IfaceF).fwdU
      ((runLazyPubSess ℓ Pt C Dh encPt encT lam
        (initSlotSessComp ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam))
        (slotTrStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
        (slotChStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
        (slotCsStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) qSim la)
        (slotCrStep ℓ Pt C Dh encPt encT lam)
        (slotDlStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
        (slotIjStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
        g).eval
        (.cons payload (.cons (endedPub, os.map (encSlotSessSt ℓ Pt)) .nil)))
      ((IfaceF).liftP
        ((fun z => ((IfaceF).dec g payload z.1.1, (z.1.2, z.2.map (encSlotSessSt ℓ Pt)))) <$>
          (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
            (CryptoVerification.E2E.Signed.SessionRouter.lazyInit
              (CryptoVerification.E2E.Signed.SessionFS.fsSlotInit
                (pure fun _ => ({} : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)))
              (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
                (lIdeal C protoSignalCodec ℓ encT)
                (lAeadR C protoSignalCodec ℓ encT idOf)
                (lChainPRG C.F) maxForwardJumps N la
                (slotSaltProtoByNf ℓ Pt C encT idOf stage))))
            ((CryptoGames.FSAEAD.pubRedImpl
              (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
              (AD := Header Pt) (M := Plain ℓ)
              (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
              ((IfaceF).enc g payload)).run endedPub)).run os)) := by
  intro N qSim
  refine runLazyPubSess_coinSimEquiv ℓ Pt C Dh encPt encT lam
    (encSlotSessSt ℓ Pt)
    (fun st => CryptoGames.FSAEAD.Thm5.HInv maxForwardJumps n st.1.1 ∧
      ∀ i, (st.2 i).table.length ≤ n)
    (CryptoVerification.E2E.Signed.SessionFS.fsSlotInit
      (pure fun _ => ({} : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)))
    (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps N la
      (slotSaltProtoByNf ℓ Pt C encT idOf stage))
    (initSlotSessComp ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam))
    (slotTrStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
    (slotChStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
    (slotCsStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) qSim la)
    (slotCrStep ℓ Pt C Dh encPt encT lam)
    (slotDlStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
    (slotIjStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
    g payload endedPub os
    (initSlotSessComp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj)
    (fun s hs => fsSlotInit_inv ℓ Pt n s hs)
    (fun ⟨s, σ⟩ hos => by subst hos; exact hInv)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro hdr pv m hg hpay ⟨s, σ⟩ ⟨hs, hσ⟩
    subst hg; cases hpay
    have hsh : atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv) = true := by
      dsimp only [fsaeadHeaderIface, CryptoGames.FSAEAD.encBadMsg] at hShort
      simpa using hShort
    exact slotTrStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj stage la qSim N n
      hdr pv m hsh s σ hs.keys_sent hσ hn
  · intro hdr pv0 m0 pv1 m1 hg hpay ⟨s, σ⟩ ⟨hs, hσ⟩
    subst hg; cases hpay
    have hsh : atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0) = true := by
      dsimp only [fsaeadHeaderIface, CryptoGames.FSAEAD.encBadMsg] at hShort
      rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hShort) with ⟨h0, -⟩
      revert h0
      cases atomicShortB (ReductionDsl.lpubOfV (ℓ := ℓ) (Pt := Pt) pv0) <;> decide
    exact slotChStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj stage la qSim N n
      hdr pv0 m0 m1 hsh s σ hs.keys_sent hσ hn
  · intro _ ⟨s, σ⟩ ⟨hs, _⟩
    exact slotCsStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj stage la qSim N s σ
      (hs.sent_le.trans (Nat.le_of_lt hn))
  · intro hg
    exact (hNoCr hg).elim
  · intro hdr cv p _ _ _ ⟨s, σ⟩ ⟨hs, hσ⟩
    exact slotDlStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj stage la qSim N n
      hdr cv p s σ
      hs.keys_recv (hs.transit_len.trans (Nat.le_of_lt hn))
      (hs.chal_len.trans (Nat.le_of_lt hn)) hσ hn
  · intro hdr cv p _ _ _ ⟨s, σ⟩ ⟨hs, hσ⟩
    exact slotIjStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj stage la qSim N n
      hdr cv p s σ
      hs.keys_recv (hs.transit_len.trans (Nat.le_of_lt hn))
      (hs.chal_len.trans (Nat.le_of_lt hn)) hσ hn

omit [Zero Pt] [SampleableType Pt] in
private lemma slotSaltProtoByNf_support_length
    (nf : Bool)
    (t : (unifSpec + CryptoGames.AEADScheme.otccaSpec
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt).Domain)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (z : (unifSpec + CryptoGames.AEADScheme.otccaSpec
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt).Range t ×
      (ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt))
    (hz : z ∈ support
      ((CryptoGames.FSAEAD.Thm5.slotLift (slotSaltProtoByNf ℓ Pt C encT idOf nf) t).run σ)) :
    ∀ i, (z.2 i).table.length ≤ (σ i).table.length + if t.isRight then 1 else 0 := by
  intro i
  rcases t with n | q
  · simp only [CryptoGames.FSAEAD.Thm5.slotLift_inl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, StateT.run_monadLift, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨_, -, rfl⟩ := hz
    simp
  · simp only [CryptoGames.FSAEAD.Thm5.slotLift_inr, Sum.isRight_inr, ↓reduceIte] at hz ⊢
    rcases q with ⟨h, m⟩ | ⟨h, e⟩
    · simp only [CryptoGames.FSAEAD.Thm5.slotLiftOtcca, StateT.run_mk,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s'⟩, hs', rfl⟩ := hz
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        cases nf
        · exact CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltImpl_support_length
            C protoSignalCodec ℓ encT idOf false (.inl (h, m)) (σ h.1) (r, s') hs'
        · exact CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltImplNF_support_length
            C protoSignalCodec ℓ encT idOf false (.inl (h, m)) (σ h.1) (r, s') hs'
      · simp [Function.update_of_ne hi]
    · simp only [CryptoGames.FSAEAD.Thm5.slotLiftOtcca, StateT.run_mk,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s'⟩, hs', rfl⟩ := hz
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        cases nf
        · exact CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltImpl_support_length
            C protoSignalCodec ℓ encT idOf false (.inr (h, e)) (σ h.1) (r, s') hs'
        · exact CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltImplNF_support_length
            C protoSignalCodec ℓ encT idOf false (.inr (h, e)) (σ h.1) (r, s') hs'
      · simp [Function.update_of_ne hi]

omit [Zero Pt] [SampleableType Pt] in
private lemma simulateQ_slotLift_proto_support_length
    (nf : Bool) {α : Type}
    (oa : OracleComp
      (unifSpec + CryptoGames.AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) α)
    (m : ℕ) (hb : oa.IsQueryBoundP (fun t => t.isRight = true) m)
    (σ : ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)
    (n : ℕ) (hσ : ∀ i, (σ i).table.length ≤ n) :
    ∀ z ∈ support
      ((simulateQ (CryptoGames.FSAEAD.Thm5.slotLift (slotSaltProtoByNf ℓ Pt C encT idOf nf))
        oa).run σ),
      ∀ i, (z.2 i).table.length ≤ n + m := by
  induction oa using OracleComp.inductionOn generalizing m σ n with
  | pure a =>
    intro z hz i
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact (hσ i).trans (Nat.le_add_right n m)
  | query_bind t k ih =>
    intro z hz i
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz'⟩ := hz
    have hpres := slotSaltProtoByNf_support_length ℓ Pt C encT idOf nf t σ r hr
    cases t with
    | inl u =>
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hpres hb
      exact ih r.1 m (hb.2 r.1) r.2 n (fun j => (hpres j).trans (hσ j)) z hz' i
    | inr q =>
      have hm : 0 < m := hb.1.resolve_left (by simp)
      simp only [Sum.isRight_inr, ↓reduceIte] at hpres hb
      have hstep := ih r.1 (m - 1) (hb.2 r.1) r.2 (n + 1)
        (fun j => (hpres j).trans (Nat.add_le_add_right (hσ j) 1)) z hz' i
      omega

omit [Zero Pt] in
/-- Pure `ProbComp` invariant step advancing `SlotOptInv n os` to `SlotOptInv (n + 1) z.2` across
one slot-session router step. -/
private theorem slotStep_support_step
    (stage la : Bool) (qR : ℕ)
    (g : FSAEADTag) (payload : ((IfaceF).dom g).denote)
    (endedPub : Bool)
    (os : Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ×
      (ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)))
    (n : ℕ) (hInv : SlotOptInv ℓ Pt n os) :
    let N := authHopCutoff maxForwardJumps qR la
    ∀ z ∈ support
      ((simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
        (CryptoVerification.E2E.Signed.SessionRouter.lazyInit
          (CryptoVerification.E2E.Signed.SessionFS.fsSlotInit
            (pure fun _ => ({} : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)))
          (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
            (lIdeal C protoSignalCodec ℓ encT)
            (lAeadR C protoSignalCodec ℓ encT idOf)
            (lChainPRG C.F) maxForwardJumps N la
            (slotSaltProtoByNf ℓ Pt C encT idOf stage))))
        ((CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
          ((IfaceF).enc g payload)).run endedPub)).run os),
      SlotOptInv ℓ Pt (n + 1) z.2 := by
  intro N
  refine lazyPubSess_support_step ℓ Pt
    (P_pre := SlotOptInv ℓ Pt n)
    (P_post := SlotOptInv ℓ Pt (n + 1))
    (Q := fun st => CryptoGames.FSAEAD.Thm5.HInv maxForwardJumps n st.1.1 ∧
      ∀ i, (st.2 i).table.length ≤ n)
    (CryptoVerification.E2E.Signed.SessionFS.fsSlotInit
      (pure fun _ => ({} : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)))
    (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps N la
      (slotSaltProtoByNf ℓ Pt C encT idOf stage))
    g payload endedPub os hInv
    (fun hpre => by
      cases os with
      | none => trivial
      | some st =>
        exact ⟨hpre.1.mono (Nat.le_succ n), fun i => (hpre.2 i).trans (Nat.le_succ n)⟩)
    (fun _ s0 hs0 => fsSlotInit_inv ℓ Pt n s0 hs0)
    (fun s _ hpre => hpre)
    (fun q0 ⟨s, σ⟩ ⟨hs, hσ⟩ r hr => ?_)
  dsimp only [CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl, StateT.run_mk] at hr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  have hz1 : z.1 ∈ support
      (((CryptoGames.FSAEAD.Thm5.multiImplWith
        (m := OracleComp (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
          (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt))
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp N 0 la) N
        (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
        (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT))))
        (.inr q0)).run s) :=
    fst_mem_support_simulateQ_run _ _ σ z hz
  refine ⟨CryptoGames.FSAEAD.Thm5.multiImplWith_inv
    (T := CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
    (lIdeal C protoSignalCodec ℓ encT)
    (lAeadR C protoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) (hp N 0 la) N
    (CryptoGames.FSAEAD.Thm5.DG (lChainPRG C.F))
    (some (CryptoGames.FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT)))
    (.inr q0) s hs z.1 hz1, ?_⟩
  exact simulateQ_slotLift_proto_support_length ℓ Pt C encT idOf stage _ 1
    (slot_multiOraclesWith_qb_one ℓ Pt C (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) N la q0 s)
    σ n hσ z hz

end SlotSideEval



private def fsEncQuery :
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

private theorem fsaeadHeaderIface_enc_eq (g : FSAEADTag) (x : ((IfaceF).dom g).denote) :
    (IfaceF).enc g x = .inr (fsEncQuery ℓ Pt g x) := by
  cases g <;> rfl

private theorem fsaeadMultiAtomicIface_enc_eq (qep qR B0 : ℕ) (g : FSHdrTag)
    (sx : ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).dom g).denote) :
    (fsaeadMultiAtomicIface ℓ Pt qep qR B0).enc g sx =
      .inr ⟨sx.1, fsEncQuery ℓ Pt (toFsTag g) sx.2⟩ := by
  cases g <;> rfl

private theorem comp_query_var_zero_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec.{0, 0} ι}
    {I : Iface S T} {Γ : List (Ty S)} (g : I.Tag) (x : (I.dom g).denote) (ρ : Env Γ) :
    (Comp.query (O := O) (I := I) g (.var .zero)).eval (.cons x ρ) =
      I.dec g x <$> liftM (OracleSpec.query (I.enc g x)) := rfl

private theorem fsMultiPureAuxBundle_query_eval (qep qR B0 : ℕ) (sampBV : ProbComp (BitVec 256))
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
            (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ => CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256))
              (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)))
            ((fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
              (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              sampBV sampBV sampBV ($ᵗ Pt) sampBV).enc g z)) :
            OracleComp (unifSpec + OracleSpec.sigma (fun _ : ℕ => CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256))
              (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt))) _)) := by
  cases g with
  | tr =>
    rcases z with ⟨sIdx, ⟨ep, _ | T⟩, pub, m⟩ <;>
      (dsimp only [fsMultiPureAuxBundle]
       erw [comp_query_var_zero_eval]
       dsimp only [Option.map, fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface,
         fsaeadMultiHeaderAdIface, fsaeadHeaderAdIface, toVal, toDenCKA]
       rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubOfV_lpubV]
       erw [Functor.map_map])
  | ch =>
    rcases z with ⟨sIdx, ⟨ep, _ | T⟩, ⟨pub0, m0⟩, ⟨pub1, m1⟩⟩ <;>
      (dsimp only [fsMultiPureAuxBundle]
       erw [comp_query_var_zero_eval]
       dsimp only [Option.map, fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface,
         fsaeadMultiHeaderAdIface, fsaeadHeaderAdIface, toVal, toDenCKA]
       rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubOfV_lpubV pub0,
         Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubOfV_lpubV pub1]
       erw [Functor.map_map])
  | cs | cr =>
    rcases z with ⟨sIdx, ⟨⟩⟩
    dsimp only [fsMultiPureAuxBundle]
    erw [comp_query_var_zero_eval]
    dsimp only [fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, fsaeadMultiHeaderAdIface,
      fsaeadHeaderAdIface, toVal, toDenCKA]
    erw [Functor.map_map]
  | dl | ij =>
    rcases z with ⟨sIdx, ⟨ep, _ | T⟩, c⟩ <;>
      (dsimp only [fsMultiPureAuxBundle]
       erw [comp_query_var_zero_eval]
       dsimp only [Option.map, fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface,
         fsaeadMultiHeaderAdIface, fsaeadHeaderAdIface, toVal, toDenCKA]
       rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lctOfV_lctV, Functor.map_map]
       congr 1; funext r; rcases r with _ | (_ | ⟨idx, _ | ⟨pub, m⟩⟩) <;> rfl)

private theorem liftP_congr_multi {ι : Type} {T : OracleSpec.{0, 0} ι} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' T) (I₁ : Iface S₁' T) (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    {α : Type} (p : ProbComp α) : I₂.liftP p = I₁.liftP p := by
  unfold Iface.liftP
  rw [funext hFwdU]

private theorem fsMultiPureAuxBundle_samp_coinSimEquiv (qep qR B0 : ℕ) (s : CKASamp)
    (z : ((fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    Computational.Proofs.ReductionDsl.PureAuxMacroLift.CoinSimEquiv
      (fsaeadMultiAtomicIface ℓ Pt qep qR B0).fwdU
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
  cases s with
  | bit | i =>
    apply Computational.Proofs.ReductionDsl.PureAuxMacroLift.CoinSimEquiv.of_eq
    exact (liftP_congr_multi (fsaeadMultiAtomicIface ℓ Pt qep qR B0) _ (fun _ => rfl) _).trans
      (id_map _).symm
  | kr | kc | ccoins | k =>
    change Computational.Proofs.ReductionDsl.PureAuxMacroLift.CoinSimEquiv
      (fsaeadMultiAtomicIface ℓ Pt qep qR B0).fwdU
      ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).liftP sampBV256Atomic) (id <$> _)
    rw [id_map, ← liftP_congr_multi (fsaeadMultiAtomicIface ℓ Pt qep qR B0) _ (fun _ => rfl)]
    exact coinSimEquiv_liftP (fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      sampBV256Atomic_evalDistEq

private theorem compilePureAuxRed_fsMulti_coinSimEquiv (qep qR B0 : ℕ)
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
    CoinSimEquiv (fsaeadMultiAtomicIface ℓ Pt qep qR B0).fwdU
      ((compilePureAuxRed
        (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
        (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  have h := compilePureAuxRed_coinSimEquiv
    (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
    (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (fsMultiPureAuxBundle_samp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam qep qR B0)
    (fun g z => .of_eq (fsMultiPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam qep qR B0 _ g z))
    (fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rw [id_map] at h
  exact ⟨fun impl himpl s => h.run_eq impl ⟨himpl.coin_eq⟩ s⟩

private theorem compilePureAuxRed_fsMultiDF_coinSimEquiv (qep qR B0 : ℕ)
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
    CoinSimEquiv (fsaeadMultiAtomicIface ℓ Pt qep qR B0).fwdU
      ((compilePureAuxRed
        (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
        (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  have h := compilePureAuxRed_coinSimEquiv
    (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
    (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (fsMultiPureAuxBundle_samp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam qep qR B0)
    (fun g z => .of_eq (fsMultiPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam qep qR B0 _ g z))
    (fig8AdaptQDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptRDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rw [id_map] at h
  exact ⟨fun impl himpl s => h.run_eq impl ⟨himpl.coin_eq⟩ s⟩

private theorem fsRrEnc_fsRrDec_lpub
    (r : (fsRrT (ℓ := ℓ) (Pt := Pt) (.prod lpubT PlainT)).denote) :
    fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := .prod lpubT PlainT)
      (fun pm : LibsignalMsgPublicPart × Plain ℓ => (lpubV (ℓ := ℓ) (Pt := Pt) pm.1, pm.2))
      (fsRrDec (ℓ := ℓ) (Pt := Pt) (msgT := .prod lpubT PlainT)
        (fun pm : (lpubT (ℓ := ℓ) (Pt := Pt)).denote × Plain ℓ =>
          (lpubOfV (ℓ := ℓ) (Pt := Pt) pm.1, pm.2)) r) = r := by
  rcases r with ⟨⟩ | ⟨st, _ | ⟨pv, m⟩⟩
  · rfl
  · rfl
  · dsimp only [fsRrDec, fsRrEnc, Option.map]
    rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubV_lpubOfV]

@[expose] def dslRouterImpl (stage la : Bool) (j qR : ℕ) :
    QueryImpl
      (unifSpec + OracleSpec.sigma (fun _ : ℕ => CryptoGames.FSAEAD.spec
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)))
      (StateT (routerStTy ℓ Pt).denote
        (OracleComp (unifSpec + CryptoGames.FSAEAD.spec
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))))
  | .inl n => StateT.lift ((IfaceF).fwdU n)
  | .inr ⟨sIdx, q⟩ =>
    match q with
    | .inl (.inl (.inl (.inl (.inl (hdr, (pub, m)))))) =>
      StateT.mk fun r =>
        Prod.map (Option.map (lctOfV (ℓ := ℓ) (Pt := Pt))) id <$>
          (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR .tr).eval
            (.cons (sIdx, (hdr, (lpubV (ℓ := ℓ) (Pt := Pt) pub, m))) (.cons r .nil))
    | .inl (.inl (.inl (.inl (.inr (hdr, ((pub0, m0), (pub1, m1))))))) =>
      StateT.mk fun r =>
        Prod.map (Option.map (lctOfV (ℓ := ℓ) (Pt := Pt))) id <$>
          (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR .ch).eval
            (.cons (sIdx, (hdr, ((lpubV (ℓ := ℓ) (Pt := Pt) pub0, m0),
              (lpubV (ℓ := ℓ) (Pt := Pt) pub1, m1)))) (.cons r .nil))
    | .inl (.inl (.inl (.inr ()))) =>
      StateT.mk fun r =>
        Prod.map (Option.map (fsSendStOfV (ℓ := ℓ) (Pt := Pt))) id <$>
          (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR .cs).eval
            (.cons (sIdx, ()) (.cons r .nil))
    | .inl (.inl (.inr ())) =>
      StateT.mk fun r =>
        Prod.map (Option.map (Prod.map (fsSendStOfV (ℓ := ℓ) (Pt := Pt))
          (fsRecvStOfV (ℓ := ℓ) (Pt := Pt)))) id <$>
          (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR .cr).eval
            (.cons (sIdx, ()) (.cons r .nil))
    | .inl (.inr (hdr, c)) =>
      StateT.mk fun r =>
        Prod.map (Option.map (fsRrDec (ℓ := ℓ) (Pt := Pt) (msgT := .prod lpubT PlainT)
          (fun pm => (lpubOfV (ℓ := ℓ) (Pt := Pt) pm.1, pm.2)))) id <$>
          (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR .dl).eval
            (.cons (sIdx, (hdr, lctV (ℓ := ℓ) (Pt := Pt) c)) (.cons r .nil))
    | .inr (hdr, c) =>
      StateT.mk fun r =>
        Prod.map (Option.map (fsRrDec (ℓ := ℓ) (Pt := Pt) (msgT := .prod lpubT PlainT)
          (fun pm => (lpubOfV (ℓ := ℓ) (Pt := Pt) pm.1, pm.2)))) id <$>
          (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR .ij).eval
            (.cons (sIdx, (hdr, lctV (ℓ := ℓ) (Pt := Pt) c)) (.cons r .nil))

private theorem simulateQ_dslRouterImpl_liftP (stage la : Bool) (j qep qR B0 : ℕ)
    {α : Type} (p : ProbComp α) (r : (routerStTy ℓ Pt).denote) :
    (simulateQ (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR)
      ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).liftP p)).run r =
      ((IfaceF).liftP p >>= fun x => pure (x, r)) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp only [ReductionDsl.Iface.liftP, simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind n k ih =>
    dsimp only [ReductionDsl.Iface.liftP]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    have hstep : (simulateQ (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR)
        ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).fwdU n)).run r =
        ((IfaceF).fwdU n >>= fun u => pure (u, r)) := by
      dsimp only [fsaeadMultiAtomicIface]
      erw [simulateQ_query]
      exact stateT_run_lift ((IfaceF).fwdU n) r
    rw [hstep]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun u => ih u

private theorem dslRouterImpl_hQuery (stage la : Bool) (j qep qR B0 : ℕ)
    (g : FSHdrTag) (sx : ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).dom g).denote)
    (r : (routerStTy ℓ Pt).denote) :
    (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
      (.cons sx (.cons r .nil)) =
      ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).dec g sx <$>
        dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR
          ((fsaeadMultiAtomicIface ℓ Pt qep qR B0).enc g sx)).run r := by
  rcases sx with ⟨sIdx, x⟩
  cases g with
  | tr =>
    rcases x with ⟨hdr, pv, m⟩
    conv_lhs => rw [← id_map ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam)
      stage la j qR .tr).eval _)]
    dsimp only [fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, dslRouterImpl]
    simp only [StateT.run_map, StateT.run_mk, Functor.map_map,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubV_lpubOfV]
    congr 1; funext ⟨optC, r'⟩
    cases optC <;> simp [Prod.map, Computational.Proofs.ReductionDsl.FsAtomicMacros.lctV_lctOfV]
  | ch =>
    rcases x with ⟨hdr, ⟨pv0, m0⟩, ⟨pv1, m1⟩⟩
    conv_lhs => rw [← id_map ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam)
      stage la j qR .ch).eval _)]
    dsimp only [fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, dslRouterImpl]
    simp only [StateT.run_map, StateT.run_mk, Functor.map_map,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubV_lpubOfV]
    congr 1; funext ⟨optC, r'⟩
    cases optC <;> simp [Prod.map, Computational.Proofs.ReductionDsl.FsAtomicMacros.lctV_lctOfV]
  | cs =>
    rcases x with ⟨⟩
    conv_lhs => rw [← id_map ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam)
      stage la j qR .cs).eval _)]
    dsimp only [fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, dslRouterImpl]
    simp only [StateT.run_map, StateT.run_mk, Functor.map_map]
    congr 1; funext ⟨optS, r'⟩
    cases optS <;> simp [Prod.map, Computational.Proofs.ReductionDsl.FsAtomicMacros.fsSendStV_fsSendStOfV]
  | cr =>
    rcases x with ⟨⟩
    conv_lhs => rw [← id_map ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam)
      stage la j qR .cr).eval _)]
    dsimp only [fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, dslRouterImpl]
    simp only [StateT.run_map, StateT.run_mk, Functor.map_map]
    congr 1; funext ⟨optSR, r'⟩
    rcases optSR with _ | ⟨ss, rs⟩ <;>
      simp [Prod.map, Computational.Proofs.ReductionDsl.FsAtomicMacros.fsSendStV_fsSendStOfV,
        Computational.Proofs.ReductionDsl.FsAtomicMacros.fsRecvStV_fsRecvStOfV]
  | dl =>
    rcases x with ⟨hdr, cv⟩
    conv_lhs => rw [← id_map ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam)
      stage la j qR .dl).eval _)]
    dsimp only [fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, dslRouterImpl]
    simp only [StateT.run_map, StateT.run_mk, Functor.map_map,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.lctV_lctOfV]
    congr 1; funext ⟨optR, r'⟩
    cases optR <;> simp [Prod.map, fsRrEnc_fsRrDec_lpub]
  | ij =>
    rcases x with ⟨hdr, cv⟩
    conv_lhs => rw [← id_map ((routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam)
      stage la j qR .ij).eval _)]
    dsimp only [fsaeadMultiAtomicIface, toFsTag, fsaeadHeaderIface, dslRouterImpl]
    simp only [StateT.run_map, StateT.run_mk, Functor.map_map,
      Computational.Proofs.ReductionDsl.FsAtomicMacros.lctV_lctOfV]
    congr 1; funext ⟨optR, r'⟩
    cases optR <;> simp [Prod.map, fsRrEnc_fsRrDec_lpub]

private theorem coinSimEquiv_simulateQ_run {κ ι σ₁ α : Type}
    {G : OracleSpec.{0, 0} κ} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    (h : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T)))
    (hInl : ∀ (n : ℕ) (s₁ : σ₁), (h (.inl n)).run s₁ = (fwdU n >>= fun u => pure (u, s₁)))
    {oa₁ oa₂ : OracleComp (unifSpec + G) α}
    (hoa : CoinSimEquiv (fun n => query (spec := unifSpec + G) (.inl n)) oa₁ oa₂)
    (s₁ : σ₁) :
    CoinSimEquiv fwdU ((simulateQ h oa₁).run s₁) ((simulateQ h oa₂).run s₁) := ⟨by
  intro σ₂ impl himpl s₂
  have hv : Computational.Proofs.ReductionDsl.FsAtomicMacros.ValidCoinSim
      (fun n => query (spec := unifSpec + G) (.inl n))
      (Computational.Proofs.ReductionDsl.FsAtomicMacros.compCoinImpl h impl) := ⟨by
    intro n ⟨s₁', s₂'⟩
    rw [simulateQ_HasQuery_query]
    change (do
      let z ← (simulateQ impl ((h (.inl n)).run s₁')).run s₂'
      pure (z.1.1, (z.1.2, z.2))) =ᵈ
      ((query (m := ProbComp) (spec := unifSpec) n) >>= fun u => pure (u, (s₁', s₂')))
    rw [hInl n s₁', simulateQ_bind, StateT.run_bind]
    refine (((himpl.coin_eq n s₂').bind fun w => by
      simp only [simulateQ_pure, StateT.run_pure]
      exact EvalDistEq.rfl).bind fun _ => EvalDistEq.rfl).trans ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl⟩
  rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.simulateQ_compCoinImpl_run h impl oa₁ s₁ s₂,
    Computational.Proofs.ReductionDsl.FsAtomicMacros.simulateQ_compCoinImpl_run h impl oa₂ s₁ s₂]
  exact (hoa.run_eq _ hv (s₁, s₂)).map _⟩

theorem coinSimEquiv_pubToAD {M₁ M₂ : FsAdv Pt ℓ}
    (h : CoinSimEquiv (IfaceF).fwdU M₁ M₂) :
    CoinSimEquiv
      (fun n => query (spec := unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      (pubToAD protoSignalCodec M₁) (pubToAD protoSignalCodec M₂) := by
  unfold pubToAD CryptoGames.FSAEAD.pubRed StateT.run'
  exact (coinSimEquiv_simulateQ_run
    (fun n => query (spec := unifSpec + fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
    (CryptoGames.FSAEAD.pubRedImpl
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (M := Plain ℓ)
      (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2))
    (fun _ _ => rfl) h false).map Prod.fst

theorem compileFsMultiAtomic_eval_coinSimEquiv
    (hℓ : ℓ < 10 ^ 6) (stage la : Bool) (j qep qR B0 : ℕ)
    (hj : j ≤ (qep + 2) * B0 + B0 * B0) (hqR : qR ≤ B0)
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
    CoinSimEquiv
      (fun n => query (spec := unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      (pubToAD protoSignalCodec
        ((compileFsMultiAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
          (fun _ => A) ()))
      (pubToAD protoSignalCodec
        (Functor.map (f := OracleComp (unifSpec + CryptoGames.FSAEAD.spec
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)))
          Prod.fst
          (StateT.run
            (simulateQ (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR)
              (R.eval (fun _ => A) ()))
            ((fun _ => (false, none), fun _ => (false, none)) : (routerStTy ℓ Pt).denote)))) := by
  apply coinSimEquiv_pubToAD
  unfold compileFsMultiAtomic
  simp only [hℓ, hj, hqR, and_self, ↓reduceIte]
  rw [substQueryRed_eval (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
      (initRouterStExpr ℓ Pt C Dh encPt encT lam)
      (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
      (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR)
      (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR)
      (fun n r => by
        dsimp only [fsaeadMultiAtomicIface, dslRouterImpl]
        rw [simulateQ_HasQuery_query]
        exact stateT_run_lift _ _)
      (fun s _ e ρ r =>
        (simulateQ_dslRouterImpl_liftP ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0
          ((atomicSamplers ℓ Pt).samp s (e.eval ρ)) r).symm)
      (dslRouterImpl_hQuery ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0)]
  exact (coinSimEquiv_simulateQ_run (IfaceF).fwdU
    (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR)
    (fun n r => stateT_run_lift _ _)
    (compilePureAuxRed_fsMulti_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam qep qR B0 R A)
    _).map Prod.fst

theorem compileFsMultiDFAtomic_eval_coinSimEquiv
    (hℓ : ℓ < 10 ^ 6) (stage la : Bool) (j qep qR B0 : ℕ)
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
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    CoinSimEquiv
      (fun n => query (spec := unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n))
      (pubToAD protoSignalCodec
        ((compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0 R).eval
          (fun _ => A) ()))
      (pubToAD protoSignalCodec
        (Functor.map (f := OracleComp (unifSpec + CryptoGames.FSAEAD.spec
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)))
          Prod.fst
          (StateT.run
            (simulateQ (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR)
              (R.eval (fun _ => A) ()))
            ((fun _ => (false, none), fun _ => (false, none)) : (routerStTy ℓ Pt).denote)))) := by
  apply coinSimEquiv_pubToAD
  unfold compileFsMultiDFAtomic
  simp only [hℓ, hj, hqR, and_self, ↓reduceIte]
  rw [substQueryRed_eval (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0) (I₂ := IfaceF)
      (initRouterStExpr ℓ Pt C Dh encPt encT lam)
      (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
      (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR)
      (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR)
      (fun n r => by
        dsimp only [fsaeadMultiAtomicIface, dslRouterImpl]
        rw [simulateQ_HasQuery_query]
        exact stateT_run_lift _ _)
      (fun s _ e ρ r =>
        (simulateQ_dslRouterImpl_liftP ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0
          ((atomicSamplers ℓ Pt).samp s (e.eval ρ)) r).symm)
      (dslRouterImpl_hQuery ℓ Pt C Dh encPt encT idOf lam stage la j qep qR B0)]
  exact (coinSimEquiv_simulateQ_run (IfaceF).fwdU
    (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR)
    (fun n r => stateT_run_lift _ _)
    (compilePureAuxRed_fsMultiDF_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam qep qR B0 R A)
    _).map Prod.fst

abbrev FsPubSpec :=
  CryptoGames.FSAEAD.spec
    (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
    (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)

private def fsDomTag : (FsPubSpec ℓ Pt).Domain → FSHdrTag
  | .inl (.inl (.inl (.inl (.inl _)))) => .tr
  | .inl (.inl (.inl (.inl (.inr _)))) => .ch
  | .inl (.inl (.inl (.inr _))) => .cs
  | .inl (.inl (.inr _)) => .cr
  | .inl (.inr _) => .dl
  | .inr _ => .ij

private def fsDomPayload :
    (q : (FsPubSpec ℓ Pt).Domain) → ((IfaceF).dom (toFsTag (fsDomTag ℓ Pt q))).denote
  | .inl (.inl (.inl (.inl (.inl (hdr, (pub, m)))))) =>
    (hdr, (lpubV (ℓ := ℓ) (Pt := Pt) pub, m))
  | .inl (.inl (.inl (.inl (.inr (hdr, ((pub0, m0), (pub1, m1))))))) =>
    (hdr, ((lpubV (ℓ := ℓ) (Pt := Pt) pub0, m0), (lpubV (ℓ := ℓ) (Pt := Pt) pub1, m1)))
  | .inl (.inl (.inl (.inr ()))) => ()
  | .inl (.inl (.inr ())) => ()
  | .inl (.inr (hdr, c)) => (hdr, lctV (ℓ := ℓ) (Pt := Pt) c)
  | .inr (hdr, c) => (hdr, lctV (ℓ := ℓ) (Pt := Pt) c)

private def fsDomRetDec :
    (q : (FsPubSpec ℓ Pt).Domain) →
      ((IfaceF).cod (toFsTag (fsDomTag ℓ Pt q))).denote → (FsPubSpec ℓ Pt).Range q
  | .inl (.inl (.inl (.inl (.inl _)))) => Option.map (lctOfV (ℓ := ℓ) (Pt := Pt))
  | .inl (.inl (.inl (.inl (.inr _)))) => Option.map (lctOfV (ℓ := ℓ) (Pt := Pt))
  | .inl (.inl (.inl (.inr ()))) => Option.map (fsSendStOfV (ℓ := ℓ) (Pt := Pt))
  | .inl (.inl (.inr ())) =>
    Option.map (Prod.map (fsSendStOfV (ℓ := ℓ) (Pt := Pt)) (fsRecvStOfV (ℓ := ℓ) (Pt := Pt)))
  | .inl (.inr _) =>
    Option.map (fsRrDec (ℓ := ℓ) (Pt := Pt) (msgT := .prod lpubT PlainT)
      (fun pm => (lpubOfV (ℓ := ℓ) (Pt := Pt) pm.1, pm.2)))
  | .inr _ =>
    Option.map (fsRrDec (ℓ := ℓ) (Pt := Pt) (msgT := .prod lpubT PlainT)
      (fun pm => (lpubOfV (ℓ := ℓ) (Pt := Pt) pm.1, pm.2)))

private theorem fsRrDec_fsRrEnc_lpub
    (r : CryptoGames.FSAEAD.ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) :
    fsRrDec (ℓ := ℓ) (Pt := Pt) (msgT := .prod lpubT PlainT)
      (fun pm : (lpubT (ℓ := ℓ) (Pt := Pt)).denote × Plain ℓ =>
        (lpubOfV (ℓ := ℓ) (Pt := Pt) pm.1, pm.2))
      (fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := .prod lpubT PlainT)
        (fun pm : LibsignalMsgPublicPart × Plain ℓ => (lpubV (ℓ := ℓ) (Pt := Pt) pm.1, pm.2))
        r) = r :=
  Computational.Proofs.ReductionDsl.FsAtomicMacros.fsRrDec_fsRrEnc _ _ (fun ⟨_, _⟩ => by simp) r

private theorem dslRouterImpl_inr_eq (stage la : Bool) (j qR sIdx : ℕ)
    (q : (FsPubSpec ℓ Pt).Domain) (r : (routerStTy ℓ Pt).denote) :
    (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR (.inr ⟨sIdx, q⟩)).run r =
      Prod.map (fsDomRetDec ℓ Pt q) id <$>
        (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR
          (fsDomTag ℓ Pt q)).eval
          (.cons (sIdx, fsDomPayload ℓ Pt q) (.cons r .nil)) := by
  rcases q with (((((⟨_, _, _⟩ | ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩) | ⟨⟩) | ⟨⟩) | ⟨_, _⟩) | ⟨_, _⟩) <;> rfl

private theorem ifaceF_enc_fsDomPayload (q : (FsPubSpec ℓ Pt).Domain) :
    (IfaceF).enc (toFsTag (fsDomTag ℓ Pt q)) (fsDomPayload ℓ Pt q) = .inr q := by
  rcases q with (((((⟨_, _, _⟩ | ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩) | ⟨⟩) | ⟨⟩) | ⟨_, _⟩) | ⟨_, _⟩) <;>
    simp [fsDomTag, fsDomPayload, toFsTag]

private theorem routerQueryMacro_eval_same (stage la : Bool) (j qR : ℕ) (g : FSHdrTag)
    (payload : ((IfaceF).dom (toFsTag g)).denote) (r : (routerStTy ℓ Pt).denote) :
    (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
      (.cons (j, payload) (.cons r .nil)) =
      (((IfaceF).dec (toFsTag g) payload <$> query ((IfaceF).enc (toFsTag g) payload)) >>=
        fun v => pure (v, r)) := by
  dsimp only [routerQueryMacro]
  change (if decide (j = j) = true then _ else _) = _
  have hjj : decide (j = j) = true := decide_eq_true rfl
  rw [hjj]
  simp only [↓reduceIte]
  rfl

private theorem dslRouterImpl_inr_same (stage la : Bool) (j qR : ℕ)
    (q : (FsPubSpec ℓ Pt).Domain) (r : (routerStTy ℓ Pt).denote) :
    (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR (.inr ⟨j, q⟩)).run r =
      (query (spec := unifSpec + FsPubSpec ℓ Pt) (.inr q) >>= fun res => pure (res, r)) := by
  rw [dslRouterImpl_inr_eq, routerQueryMacro_eval_same]
  rcases q with (((((⟨hdr, pub, m⟩ | ⟨hdr, ⟨pub0, m0⟩, ⟨pub1, m1⟩⟩) | ⟨⟩) | ⟨⟩) | ⟨hdr, c⟩) | ⟨hdr, c⟩)
  all_goals
    dsimp only [fsDomTag, fsDomPayload, fsDomRetDec, toFsTag, fsaeadHeaderIface]
    repeat rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubOfV_lpubV]
    repeat rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lctOfV_lctV]
    simp only [map_bind, bind_map_left, map_pure]
    refine bind_congr fun res => ?_
    cases res with
    | none => rfl
    | some val =>
      simp only [Prod.map, Option.map, id_eq]
      try rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lctOfV_lctV]
      try rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.fsSendStOfV_fsSendStV]
      try rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.fsRecvStOfV_fsRecvStV]
      try rw [fsRrDec_fsRrEnc_lpub]
      try exact congrArg (fun x => pure (some x, r)) (Prod.eta.symm)

private theorem ite_eq_update {α : Type} (f : ℕ → α) (i : ℕ) (v : α) :
    (fun k => if k = i then v else f k) = Function.update f i v := by
  funext k
  by_cases hk : k = i <;> simp [Function.update, hk]

private theorem routerQueryMacro_eval_real (stage la : Bool) (j qR sIdx : ℕ) (g : FSHdrTag)
    (payload : ((IfaceF).dom (toFsTag g)).denote) (r : (routerStTy ℓ Pt).denote)
    (hBranch : (stage = false ∧ j < sIdx) ∨ (stage = true ∧ sIdx < j)) :
    let N := authHopCutoff maxForwardJumps qR la
    let qSim := 2 * qR + 4
    let mSlotR := if stage then N else 0
    (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
      (.cons (sIdx, payload) (.cons r .nil)) =
      (fun z => (z.1, (Function.update r.1 sIdx z.2, r.2))) <$>
        (runLazyPubSess ℓ Pt C Dh encPt encT lam
          (initRealSessComp ℓ Pt C Dh encPt encT idOf lam)
          (realTrStep ℓ Pt C Dh encPt encT idOf lam mSlotR mSlotR)
          (realChStep ℓ Pt C Dh encPt encT idOf lam mSlotR mSlotR)
          (realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la)
          (realCrStep ℓ Pt C Dh encPt encT lam)
          (realDlStep ℓ Pt C Dh encPt encT idOf lam qSim mSlotR mSlotR la)
          (realIjStep ℓ Pt C Dh encPt encT idOf lam qSim mSlotR mSlotR la)
          (toFsTag g)).eval (.cons payload (.cons (r.1 sIdx) .nil)) := by
  intro N qSim mSlotR
  rcases hBranch with ⟨rfl, hgt⟩ | ⟨rfl, hlt⟩
  · have hne : decide (sIdx = j) = false := decide_eq_false (Nat.ne_of_lt hgt).symm
    have hnotlt : decide (sIdx < j) = false := decide_eq_false (Nat.not_lt.mpr (Nat.le_of_lt hgt))
    dsimp only [routerQueryMacro]
    change (if decide (sIdx = j) = true then _ else _) = _
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (if decide (sIdx < j) = true then _ else _) = _
    rw [hnotlt]
    simp only [Bool.false_eq_true, ↓reduceIte, Comp.eval, Expr.eval, Env.get, pure_bind,
      renId2_eval, ite_eq_update,
      map_eq_bind_pure_comp, Function.comp_def]
    rfl
  · have hne : decide (sIdx = j) = false := decide_eq_false (Nat.ne_of_lt hlt)
    have hlt' : decide (sIdx < j) = true := decide_eq_true hlt
    dsimp only [routerQueryMacro]
    change (if decide (sIdx = j) = true then _ else _) = _
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (if decide (sIdx < j) = true then _ else _) = _
    rw [hlt']
    simp only [↓reduceIte, Comp.eval, Expr.eval, Env.get, pure_bind, renId2_eval,
      ite_eq_update,
      map_eq_bind_pure_comp, Function.comp_def]
    rfl

private theorem routerQueryMacro_eval_slot (stage la : Bool) (j qR sIdx : ℕ) (g : FSHdrTag)
    (payload : ((IfaceF).dom (toFsTag g)).denote) (r : (routerStTy ℓ Pt).denote)
    (hBranch : (stage = false ∧ sIdx < j) ∨ (stage = true ∧ j < sIdx)) :
    let N := authHopCutoff maxForwardJumps qR la
    let qSim := 2 * qR + 4
    (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR g).eval
      (.cons (sIdx, payload) (.cons r .nil)) =
      (fun z => (z.1, (r.1, Function.update r.2 sIdx z.2))) <$>
        (runLazyPubSess ℓ Pt C Dh encPt encT lam
          (initSlotSessComp ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam))
          (slotTrStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
          (slotChStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
          (slotCsStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) qSim la)
          (slotCrStep ℓ Pt C Dh encPt encT lam)
          (slotDlStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
          (slotIjStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
          (toFsTag g)).eval (.cons payload (.cons (r.2 sIdx) .nil)) := by
  intro N qSim
  rcases hBranch with ⟨rfl, hlt⟩ | ⟨rfl, hgt⟩
  · have hne : decide (sIdx = j) = false := decide_eq_false (Nat.ne_of_lt hlt)
    have hlt' : decide (sIdx < j) = true := decide_eq_true hlt
    dsimp only [routerQueryMacro]
    change (if decide (sIdx = j) = true then _ else _) = _
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (if decide (sIdx < j) = true then _ else _) = _
    rw [hlt']
    simp only [↓reduceIte, Comp.eval, Expr.eval, Env.get, pure_bind, renId2_eval,
      ite_eq_update,
      map_eq_bind_pure_comp, Function.comp_def]
    rfl
  · have hne : decide (sIdx = j) = false := decide_eq_false (Nat.ne_of_lt hgt).symm
    have hnotlt : decide (sIdx < j) = false := decide_eq_false (Nat.not_lt.mpr (Nat.le_of_lt hgt))
    dsimp only [routerQueryMacro]
    change (if decide (sIdx = j) = true then _ else _) = _
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (if decide (sIdx < j) = true then _ else _) = _
    rw [hnotlt]
    simp only [Bool.false_eq_true, ↓reduceIte, Comp.eval, Expr.eval, Env.get, pure_bind,
      renId2_eval, ite_eq_update,
      map_eq_bind_pure_comp, Function.comp_def]
    rfl

private abbrev RealEntryDom :=
  Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt) × Bool

private abbrev SlotEntryDom :=
  Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ×
    (ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)) × Bool

private def encRealEntry (e : RealEntryDom ℓ Pt) : (Ty.prod .bool (Ty.opt (hybSessStTy ℓ Pt))).denote :=
  (e.2, e.1.map (encHybSessSt ℓ Pt))

private def encSlotEntry (e : SlotEntryDom ℓ Pt) : (Ty.prod .bool (Ty.opt (slotSessStTy ℓ Pt))).denote :=
  (e.2, e.1.map (encSlotSessSt ℓ Pt))

private def encRouterTbls (tReal : ℕ → RealEntryDom ℓ Pt) (tSlot : ℕ → SlotEntryDom ℓ Pt) :
    (routerStTy ℓ Pt).denote :=
  (fun s => encRealEntry ℓ Pt (tReal s), fun s => encSlotEntry ℓ Pt (tSlot s))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem encRouterTbls_update_real (tReal : ℕ → RealEntryDom ℓ Pt)
    (tSlot : ℕ → SlotEntryDom ℓ Pt) (sIdx : ℕ) (e : RealEntryDom ℓ Pt) :
    (Function.update (encRouterTbls ℓ Pt tReal tSlot).1 sIdx (encRealEntry ℓ Pt e),
      (encRouterTbls ℓ Pt tReal tSlot).2) =
      encRouterTbls ℓ Pt (Function.update tReal sIdx e) tSlot := by
  refine Prod.ext (funext fun s => ?_) rfl
  by_cases h : s = sIdx
  · subst h; simp [encRouterTbls]
  · simp [encRouterTbls, h]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem encRouterTbls_update_slot (tReal : ℕ → RealEntryDom ℓ Pt)
    (tSlot : ℕ → SlotEntryDom ℓ Pt) (sIdx : ℕ) (e : SlotEntryDom ℓ Pt) :
    ((encRouterTbls ℓ Pt tReal tSlot).1,
      Function.update (encRouterTbls ℓ Pt tReal tSlot).2 sIdx (encSlotEntry ℓ Pt e)) =
      encRouterTbls ℓ Pt tReal (Function.update tSlot sIdx e) := by
  refine Prod.ext rfl (funext fun s => ?_)
  by_cases h : s = sIdx
  · subst h; simp [encRouterTbls]
  · simp [encRouterTbls, h]

private abbrev realWrapPubImpl (stage la : Bool) (qR : ℕ) :
    QueryImpl (FsPubSpec ℓ Pt) (StateT (RealEntryDom ℓ Pt) ProbComp) :=
  let N := authHopCutoff maxForwardJumps qR la
  let mSlotR := if stage then N else 0
  Computational.Proofs.HeadlineV1.Stage2RouterHelpers.wrapPubImpl
    (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
    (CryptoVerification.E2E.Signed.SessionRouter.lazyInit
      CryptoVerification.E2E.Signed.SessionFS.fsInit
      (CryptoVerification.E2E.Signed.SessionFS.fsImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp mSlotR mSlotR la)))

private abbrev slotWrapPubImpl (stage la : Bool) (qR : ℕ) :
    QueryImpl (FsPubSpec ℓ Pt) (StateT (SlotEntryDom ℓ Pt) ProbComp) :=
  let N := authHopCutoff maxForwardJumps qR la
  Computational.Proofs.HeadlineV1.Stage2RouterHelpers.wrapPubImpl
    (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
    (CryptoVerification.E2E.Signed.SessionRouter.lazyInit
      (CryptoVerification.E2E.Signed.SessionFS.fsSlotInit
        (pure fun _ => ({} : CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt)))
      (CryptoVerification.E2E.Signed.SessionFS.fsSlotImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps N la
        (slotSaltProtoByNf ℓ Pt C encT idOf stage)))

private def qNotCr : (FsPubSpec ℓ Pt).Domain → Prop
  | .inl (.inl (.inr _)) => False
  | _ => True

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem fsDomTag_ne_cr {q : (FsPubSpec ℓ Pt).Domain} (hq : qNotCr ℓ Pt q) :
    toFsTag (fsDomTag ℓ Pt q) ≠ .cr := by
  rcases q with (((((⟨_, _, _⟩ | ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩) | ⟨⟩) | ⟨⟩) | ⟨_, _⟩) | ⟨_, _⟩) <;>
    simp [qNotCr, fsDomTag, toFsTag] at hq ⊢

private theorem iface_liftP_map_local {S : Sig} {ι α β : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) (f : α → β) (p : ProbComp α) :
    f <$> I.liftP p = I.liftP (f <$> p) := by
  simp [ReductionDsl.Iface.liftP, simulateQ_map]

private theorem evalDistEq_probComp_bind_of_support_local {α β : Type} (p : ProbComp α)
    {g₁ g₂ : α → ProbComp β} (hg : ∀ a ∈ support p, g₁ a =ᵈ g₂ a) :
    (p >>= g₁) =ᵈ (p >>= g₂) := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa using hg a (by simp)
  | query_bind n k ih =>
    simp only [bind_assoc]
    exact EvalDistEq.rfl.bind fun u => ih u fun a ha =>
      hg a (by simp only [mem_support_bind_iff]; exact ⟨u, by simp, ha⟩)

private theorem evalDistEq_simulateQ_liftM_gen {κ : Type} {H : OracleSpec.{0, 0} κ}
    {σ : Type} (impl : QueryImpl (unifSpec + H) (StateT σ ProbComp))
    (himpl : Computational.Proofs.ReductionDsl.FsAtomicMacros.ValidCoinSim
      (fun n => query (spec := unifSpec + H) (.inl n)) impl)
    {α : Type} (p : ProbComp α) :
    ∀ (s : σ),
      (simulateQ impl (liftM p : OracleComp (unifSpec + H) α)).run s =ᵈ
        (p >>= fun a => pure (a, s)) := by
  induction p using OracleComp.inductionOn with
  | pure a => intro s; simp
  | query_bind n k ih =>
    intro s
    change (simulateQ impl
        ((query (spec := unifSpec + H) (.inl n)) >>= fun u =>
          (liftM (k u) : OracleComp (unifSpec + H) α))).run s =ᵈ _
    rw [simulateQ_bind, StateT.run_bind]
    refine ((himpl.coin_eq n s).bind fun z => ih z.1 z.2).trans ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl

private theorem coinSimEquiv_liftP_bind_liftM_of_support
    {S : Sig} {κ α β : Type} {H : OracleSpec.{0, 0} κ}
    (I : Iface S (unifSpec + H))
    (hFwd : I.fwdU = fun n => query (spec := unifSpec + H) (.inl n))
    (p : ProbComp α)
    (D₁ D₂ : α → OracleComp (unifSpec + H) β)
    (hD : ∀ a ∈ support p, CoinSimEquiv I.fwdU (D₁ a) (D₂ a)) :
    CoinSimEquiv I.fwdU
      (I.liftP p >>= D₁)
      ((liftM p : OracleComp (unifSpec + H) α) >>= D₂) := ⟨by
  intro σ impl hv s
  have hv' : Computational.Proofs.ReductionDsl.FsAtomicMacros.ValidCoinSim
      (fun n => query (spec := unifSpec + H) (.inl n)) impl := hFwd ▸ hv
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  have hL := Computational.Proofs.ReductionDsl.FsAtomicMacros.evalDistEq_simulateQ_liftP I impl hv p s
  have hR := evalDistEq_simulateQ_liftM_gen impl hv' p s
  refine ((hL.bind fun _ => EvalDistEq.rfl).trans ?_).trans
    ((hR.bind fun _ => EvalDistEq.rfl).symm)
  simp only [bind_assoc, pure_bind]
  exact evalDistEq_probComp_bind_of_support_local p fun a ha => (hD a ha).run_eq impl hv s⟩

private theorem coinSimEquiv_liftP_map_bind_liftM_of_support
    {S : Sig} {κ α β₁ β₂ γ : Type} {H : OracleSpec.{0, 0} κ}
    (I : Iface S (unifSpec + H))
    (hFwd : I.fwdU = fun n => query (spec := unifSpec + H) (.inl n))
    (p : ProbComp α) (f₁ : α → β₁) (f₂ : α → β₂)
    (D₁ : β₁ → OracleComp (unifSpec + H) γ)
    (D₂ : β₂ → OracleComp (unifSpec + H) γ)
    (hD : ∀ a ∈ support p, CoinSimEquiv I.fwdU (D₁ (f₁ a)) (D₂ (f₂ a))) :
    CoinSimEquiv I.fwdU
      (I.liftP (f₁ <$> p) >>= D₁)
      ((f₂ <$> (liftM p : OracleComp (unifSpec + H) α)) >>= D₂) := by
  rw [← iface_liftP_map_local]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  exact coinSimEquiv_liftP_bind_liftM_of_support I hFwd p _ _ hD

private theorem sessRedImpl_inl_eq {ι σL σR : Type} {spec : OracleSpec.{0, 0} ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    (k n : ℕ) (sL : ℕ → σL) (sR : ℕ → σR) :
    (CryptoVerification.E2E.Signed.SessionRouter.sessRedImpl implL implR k (.inl n)).run (sL, sR) =
      (query (spec := unifSpec + spec) (.inl n) >>= fun a => pure (a, (sL, sR))) := rfl

private theorem sessRedImpl_inr_same_eq {ι σL σR : Type} {spec : OracleSpec.{0, 0} ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    (k : ℕ) (q' : ι) (sL : ℕ → σL) (sR : ℕ → σR) :
    (CryptoVerification.E2E.Signed.SessionRouter.sessRedImpl implL implR k (.inr ⟨k, q'⟩)).run (sL, sR) =
      (query (spec := unifSpec + spec) (.inr q') >>= fun a => pure (a, (sL, sR))) := by
  simp only [CryptoVerification.E2E.Signed.SessionRouter.sessRedImpl, ↓reduceIte, StateT.run_lift]
  rfl

private theorem sessRedImpl_inr_lt_eq {ι σL σR : Type} {spec : OracleSpec.{0, 0} ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    {s k : ℕ} (hsk : s < k) (q' : ι) (sL : ℕ → σL) (sR : ℕ → σR) :
    (CryptoVerification.E2E.Signed.SessionRouter.sessRedImpl implL implR k (.inr ⟨s, q'⟩)).run (sL, sR) =
      (fun r => (r.1, (sL, Function.update sR s r.2))) <$>
        (liftM ((implR q').run (sR s)) : OracleComp (unifSpec + spec) (spec.Range q' × σR)) := by
  have hne : s ≠ k := Nat.ne_of_lt hsk
  simp only [CryptoVerification.E2E.Signed.SessionRouter.sessRedImpl, hne, hsk, ↓reduceIte,
    StateT.run_mk, liftM_map]
  rfl

private theorem sessRedImpl_inr_gt_eq {ι σL σR : Type} {spec : OracleSpec.{0, 0} ι}
    (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp))
    {s k : ℕ} (hks : k < s) (q' : ι) (sL : ℕ → σL) (sR : ℕ → σR) :
    (CryptoVerification.E2E.Signed.SessionRouter.sessRedImpl implL implR k (.inr ⟨s, q'⟩)).run (sL, sR) =
      (fun r => (r.1, (Function.update sL s r.2, sR))) <$>
        (liftM ((implL q').run (sL s)) : OracleComp (unifSpec + spec) (spec.Range q' × σL)) := by
  have hne : s ≠ k := (Nat.ne_of_lt hks).symm
  have hnotlt : ¬ s < k := Nat.not_lt.mpr (Nat.le_of_lt hks)
  simp only [CryptoVerification.E2E.Signed.SessionRouter.sessRedImpl, hne, hnotlt, ↓reduceIte,
    StateT.run_mk, liftM_map]
  rfl

private theorem wrapPubImpl_lazyInit_eq {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)
      (StateT σ ProbComp))
    (q : (FsPubSpec ℓ Pt).Domain) (endedPub : Bool) (os : Option σ) :
    ((fun z =>
        (fsDomRetDec ℓ Pt q
          ((IfaceF).dec (toFsTag (fsDomTag ℓ Pt q)) (fsDomPayload ℓ Pt q) z.1.1),
        (z.2, z.1.2))) <$>
      (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.fwd
        (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl))
        ((CryptoGames.FSAEAD.pubRedImpl
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
          ((IfaceF).enc (toFsTag (fsDomTag ℓ Pt q)) (fsDomPayload ℓ Pt q))).run endedPub)).run os) =
    (Computational.Proofs.HeadlineV1.Stage2RouterHelpers.wrapPubImpl
      (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2)
      (CryptoVerification.E2E.Signed.SessionRouter.lazyInit init impl) q).run (os, endedPub) := by
  rcases q with (((((⟨hdr, pub, m⟩ | ⟨hdr, ⟨pub0, m0⟩, ⟨pub1, m1⟩⟩) | ⟨⟩) | ⟨⟩) | ⟨hdr, c⟩) | ⟨hdr, c⟩)
  all_goals
    dsimp only [fsDomTag, fsDomPayload, fsDomRetDec, toFsTag, fsaeadHeaderIface,
      Computational.Proofs.HeadlineV1.Stage2RouterHelpers.wrapPubImpl,
      Computational.Proofs.HeadlineV1.Stage2RouterHelpers.wrapTrImpl, StateT.run_mk]
    repeat rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lpubOfV_lpubV]
    repeat rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lctOfV_lctV]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun z => ?_
    rcases z with ⟨⟨res, b'⟩, s'⟩
    cases res with
    | none => rfl
    | some val =>
      simp only [Option.map, Prod.map]
      try rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.lctOfV_lctV]
      try rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.fsSendStOfV_fsSendStV]
      try rw [Computational.Proofs.ReductionDsl.FsAtomicMacros.fsRecvStOfV_fsRecvStV]
      try rw [fsRrDec_fsRrEnc_lpub]
      try exact congrArg (fun x => pure (some x, s', b')) (Prod.eta.symm)

private theorem realWrapPubImpl_support_step (stage la : Bool) (qR : ℕ)
    (q : (FsPubSpec ℓ Pt).Domain) (e : RealEntryDom ℓ Pt)
    (n : ℕ) (hInv : RealOptInv ℓ Pt n e.1) :
    ∀ w ∈ support ((realWrapPubImpl ℓ Pt C encT idOf stage la qR q).run e),
      RealOptInv ℓ Pt (n + 1) w.2.1 := by
  intro w hw
  rw [show e = (e.1, e.2) from rfl, ← wrapPubImpl_lazyInit_eq ℓ Pt] at hw
  simp only [support_map, Set.mem_image] at hw
  rcases hw with ⟨z, hz, rfl⟩
  exact realStep_support_step ℓ Pt C encT idOf stage la qR
    (toFsTag (fsDomTag ℓ Pt q)) (fsDomPayload ℓ Pt q) e.2 e.1 n hInv z hz

private theorem slotWrapPubImpl_support_step (stage la : Bool) (qR : ℕ)
    (q : (FsPubSpec ℓ Pt).Domain) (e : SlotEntryDom ℓ Pt)
    (n : ℕ) (hInv : SlotOptInv ℓ Pt n e.1) :
    ∀ w ∈ support ((slotWrapPubImpl ℓ Pt C encT idOf stage la qR q).run e),
      SlotOptInv ℓ Pt (n + 1) w.2.1 := by
  intro w hw
  rw [show e = (e.1, e.2) from rfl, ← wrapPubImpl_lazyInit_eq ℓ Pt] at hw
  simp only [support_map, Set.mem_image] at hw
  rcases hw with ⟨z, hz, rfl⟩
  exact slotStep_support_step ℓ Pt C encT idOf stage la qR
    (toFsTag (fsDomTag ℓ Pt q)) (fsDomPayload ℓ Pt q) e.2 e.1 n hInv z hz

private theorem dslRouter_realBranch_coinSimEquiv (hinj : Function.Injective encT)
    (stage la : Bool) (j qR sIdx : ℕ) (q : (FsPubSpec ℓ Pt).Domain)
    (tReal : ℕ → RealEntryDom ℓ Pt) (tSlot : ℕ → SlotEntryDom ℓ Pt)
    (hBranch : (stage = false ∧ j < sIdx) ∨ (stage = true ∧ sIdx < j))
    (n : ℕ) (hn : n < 2 * qR + 4) (hInv : RealOptInv ℓ Pt n (tReal sIdx).1)
    (hNoCr : qNotCr ℓ Pt q)
    (hShort : ¬ CryptoGames.FSAEAD.encBadMsg
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (C := ℕ × LCt)
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr q) = true) :
    CoinSimEquiv (IfaceF).fwdU
      ((dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR (.inr ⟨sIdx, q⟩)).run
        (encRouterTbls ℓ Pt tReal tSlot))
      ((IfaceF).liftP
        ((fun w => (w.1, encRouterTbls ℓ Pt (Function.update tReal sIdx w.2) tSlot)) <$>
          (realWrapPubImpl ℓ Pt C encT idOf stage la qR q).run (tReal sIdx))) := by
  rw [dslRouterImpl_inr_eq,
    routerQueryMacro_eval_real ℓ Pt C Dh encPt encT idOf lam stage la j qR sIdx
      (fsDomTag ℓ Pt q) (fsDomPayload ℓ Pt q) (encRouterTbls ℓ Pt tReal tSlot) hBranch]
  simp only [Functor.map_map]
  refine ((realStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj stage la qR
    (toFsTag (fsDomTag ℓ Pt q)) (fsDomPayload ℓ Pt q) (tReal sIdx).2 (tReal sIdx).1
    n hn hInv (fsDomTag_ne_cr ℓ Pt hNoCr)
    (by rw [ifaceF_enc_fsDomPayload]; exact hShort)).map
    (fun y => (fsDomRetDec ℓ Pt q y.1,
      (Function.update (encRouterTbls ℓ Pt tReal tSlot).1 sIdx y.2,
        (encRouterTbls ℓ Pt tReal tSlot).2)))).trans (CoinSimEquiv.of_eq ?_)
  rw [iface_liftP_map_local, show tReal sIdx = ((tReal sIdx).1, (tReal sIdx).2) from rfl,
    ← wrapPubImpl_lazyInit_eq ℓ Pt]
  simp only [Functor.map_map]
  congr 2; funext z
  exact Prod.ext rfl (encRouterTbls_update_real ℓ Pt tReal tSlot sIdx (z.2, z.1.2))

private theorem dslRouter_slotBranch_coinSimEquiv (hinj : Function.Injective encT)
    (stage la : Bool) (j qR sIdx : ℕ) (q : (FsPubSpec ℓ Pt).Domain)
    (tReal : ℕ → RealEntryDom ℓ Pt) (tSlot : ℕ → SlotEntryDom ℓ Pt)
    (hBranch : (stage = false ∧ sIdx < j) ∨ (stage = true ∧ j < sIdx))
    (n : ℕ) (hn : n < 2 * qR + 4) (hInv : SlotOptInv ℓ Pt n (tSlot sIdx).1)
    (hNoCr : qNotCr ℓ Pt q)
    (hShort : ¬ CryptoGames.FSAEAD.encBadMsg
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (C := ℕ × LCt)
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr q) = true) :
    CoinSimEquiv (IfaceF).fwdU
      ((dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR (.inr ⟨sIdx, q⟩)).run
        (encRouterTbls ℓ Pt tReal tSlot))
      ((IfaceF).liftP
        ((fun w => (w.1, encRouterTbls ℓ Pt tReal (Function.update tSlot sIdx w.2))) <$>
          (slotWrapPubImpl ℓ Pt C encT idOf stage la qR q).run (tSlot sIdx))) := by
  rw [dslRouterImpl_inr_eq,
    routerQueryMacro_eval_slot ℓ Pt C Dh encPt encT idOf lam stage la j qR sIdx
      (fsDomTag ℓ Pt q) (fsDomPayload ℓ Pt q) (encRouterTbls ℓ Pt tReal tSlot) hBranch]
  simp only [Functor.map_map]
  refine ((slotStep_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj stage la qR
    (toFsTag (fsDomTag ℓ Pt q)) (fsDomPayload ℓ Pt q) (tSlot sIdx).2 (tSlot sIdx).1
    n hn hInv (fsDomTag_ne_cr ℓ Pt hNoCr)
    (by rw [ifaceF_enc_fsDomPayload]; exact hShort)).map
    (fun y => (fsDomRetDec ℓ Pt q y.1,
      ((encRouterTbls ℓ Pt tReal tSlot).1,
        Function.update (encRouterTbls ℓ Pt tReal tSlot).2 sIdx y.2)))).trans
    (CoinSimEquiv.of_eq ?_)
  rw [iface_liftP_map_local, show tSlot sIdx = ((tSlot sIdx).1, (tSlot sIdx).2) from rfl,
    ← wrapPubImpl_lazyInit_eq ℓ Pt]
  simp only [Functor.map_map]
  congr 2; funext z
  exact Prod.ext rfl (encRouterTbls_update_slot ℓ Pt tReal tSlot sIdx (z.2, z.1.2))

private theorem coinSimEquiv_bind_left {ι α β : Type} {T : OracleSpec.{0, 0} ι}
    {fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))}
    {oa₁ oa₂ : OracleComp T α} (h : CoinSimEquiv fwdU oa₁ oa₂)
    (k : α → OracleComp T β) :
    CoinSimEquiv fwdU (oa₁ >>= k) (oa₂ >>= k) := ⟨by
  intro σ impl hv s
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  exact (h.run_eq impl hv s).bind fun _ => EvalDistEq.rfl⟩

private theorem coinSimEquiv_query_bind {ι α : Type} {T : OracleSpec.{0, 0} ι}
    {fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))}
    (t : T.Domain) (k₁ k₂ : T.Range t → OracleComp T α)
    (hk : ∀ u, CoinSimEquiv fwdU (k₁ u) (k₂ u)) :
    CoinSimEquiv fwdU (query t >>= k₁) (query t >>= k₂) := ⟨by
  intro σ impl hv s
  rw [simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind,
    simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind]
  exact EvalDistEq.rfl.bind fun z => (hk z.1).run_eq impl hv z.2⟩

private theorem coinSimEquiv_query_pure_bind {ι α β₁ β₂ : Type} {T : OracleSpec.{0, 0} ι}
    {fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))}
    {t : T.Domain} (f₁ : T.Range t → β₁) (f₂ : T.Range t → β₂)
    (k₁ : β₁ → OracleComp T α) (k₂ : β₂ → OracleComp T α)
    (hk : ∀ u, CoinSimEquiv fwdU (k₁ (f₁ u)) (k₂ (f₂ u))) :
    CoinSimEquiv fwdU
      ((query t >>= fun u => pure (f₁ u)) >>= k₁)
      ((query t >>= fun u => pure (f₂ u)) >>= k₂) := by
  simp only [bind_assoc, pure_bind]
  exact coinSimEquiv_query_bind t _ _ hk

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem realOptInv_mono {n m : ℕ} (hnm : n ≤ m)
    {os : Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt)}
    (h : RealOptInv ℓ Pt n os) : RealOptInv ℓ Pt m os := by
  cases os with
  | none => trivial
  | some s => exact CryptoGames.FSAEAD.Thm5.HInv.mono h hnm

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem slotOptInv_mono {n m : ℕ} (hnm : n ≤ m)
    {os : Option (CryptoGames.FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt ×
      (ℕ → CryptoGames.Ratchet.LibsignalInst.SaltSlotSt Pt))}
    (h : SlotOptInv ℓ Pt n os) : SlotOptInv ℓ Pt m os := by
  rcases os with _ | ⟨s, tbl⟩
  · trivial
  · exact ⟨CryptoGames.FSAEAD.Thm5.HInv.mono h.1 hnm, fun i => (h.2 i).trans hnm⟩

@[expose] def qOnSess (s : ℕ) :
    (unifSpec + OracleSpec.sigma (fun _ : ℕ => FsPubSpec ℓ Pt)).Domain → Bool
  | .inl _ => false
  | .inr ⟨s', _⟩ => decide (s' = s)

@[expose] def qIsCr :
    (unifSpec + OracleSpec.sigma (fun _ : ℕ => FsPubSpec ℓ Pt)).Domain → Bool
  | .inr ⟨_, .inl (.inl (.inr _))⟩ => true
  | _ => false

@[expose] def qIsShortBad (s : ℕ) :
    (unifSpec + OracleSpec.sigma (fun _ : ℕ => FsPubSpec ℓ Pt)).Domain → Bool
  | .inl _ => false
  | .inr ⟨s', q⟩ => decide (s' = s) &&
      CryptoGames.FSAEAD.encBadMsg
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AD := Header Pt) (C := ℕ × LCt)
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr q)

private theorem qb_step_zero {ι α : Type} {S : OracleSpec ι}
    {t : S.Domain} {k : S.Range t → OracleComp S α} {P : S.Domain → Bool}
    (h : (liftM (OracleSpec.query t) >>= k).IsQueryBoundP (fun x => P x = true) 0) :
    P t = false ∧ ∀ u, (k u).IsQueryBoundP (fun x => P x = true) 0 := by
  rw [isQueryBoundP_query_bind_iff] at h
  have ht : P t = false := Bool.eq_false_iff.mpr (h.1.resolve_right (Nat.not_lt_zero 0))
  refine ⟨ht, fun u => ?_⟩
  have hu := h.2 u; rw [ht] at hu; simpa using hu

private theorem qb_step_of_false {ι α : Type} {S : OracleSpec ι}
    {t : S.Domain} {k : S.Range t → OracleComp S α} {P : S.Domain → Bool} {b : ℕ}
    (h : (liftM (OracleSpec.query t) >>= k).IsQueryBoundP (fun x => P x = true) b)
    (ht : P t = false)
    (u : S.Range t) :
    (k u).IsQueryBoundP (fun x => P x = true) b := by
  rw [isQueryBoundP_query_bind_iff] at h
  have hu := h.2 u; rw [ht] at hu; simpa using hu

private theorem qb_step_of_true {ι α : Type} {S : OracleSpec ι}
    {t : S.Domain} {k : S.Range t → OracleComp S α} {P : S.Domain → Bool} {b : ℕ}
    (ht : P t = true)
    (h : (liftM (OracleSpec.query t) >>= k).IsQueryBoundP (fun x => P x = true) b) :
    0 < b ∧ ∀ u, (k u).IsQueryBoundP (fun x => P x = true) (b - 1) := by
  rw [isQueryBoundP_query_bind_iff] at h
  refine ⟨h.1.resolve_left (by simp [ht]), fun u => ?_⟩
  have hu := h.2 u; rw [ht] at hu; simpa using hu

private theorem dslRouter_run_coinSimEquiv_false (hinj : Function.Injective encT)
    (la : Bool) (j qR : ℕ) {α : Type}
    (M : OracleComp (unifSpec + OracleSpec.sigma (fun _ : ℕ => FsPubSpec ℓ Pt)) α) :
    ∀ (rem used : ℕ → ℕ)
      (tReal : ℕ → RealEntryDom ℓ Pt) (tSlot : ℕ → SlotEntryDom ℓ Pt),
      (∀ s ≠ j, M.IsQueryBoundP (fun t => qOnSess ℓ Pt s t = true) (rem s)) →
      M.IsQueryBoundP (fun t => qIsCr ℓ Pt t = true) 0 →
      (∀ s ≠ j, M.IsQueryBoundP (fun t => qIsShortBad ℓ Pt s t = true) 0) →
      (∀ s ≠ j, used s + rem s ≤ 2 * qR + 4) →
      (∀ s ≠ j, RealOptInv ℓ Pt (used s) (tReal s).1) →
      (∀ s ≠ j, SlotOptInv ℓ Pt (used s) (tSlot s).1) →
      CoinSimEquiv (IfaceF).fwdU
        ((simulateQ (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam false la j qR) M).run
          (encRouterTbls ℓ Pt tReal tSlot))
        (Prod.map id (fun p => encRouterTbls ℓ Pt p.1 p.2) <$>
          (simulateQ
            (CryptoVerification.E2E.Signed.SessionRouter.sessRedImpl
              (realWrapPubImpl ℓ Pt C encT idOf false la qR)
              (slotWrapPubImpl ℓ Pt C encT idOf false la qR) j)
            M).run (tReal, tSlot)) := by
  induction M using OracleComp.inductionOn with
  | pure a =>
    intro _ _ _ _ _ _ _ _ _ _
    exact CoinSimEquiv.of_eq (by simp [Prod.map])
  | query_bind t k ih =>
    intro rem used tReal tSlot hRem hCr hSh hSum hReal hSlot
    obtain ⟨h0Cr, hCrK⟩ := qb_step_zero hCr
    simp only [simulateQ_query_bind, monadLift_self, OracleQuery.input_query,
      OracleQuery.cont_query, StateT.run_bind, map_bind]
    rcases t with n | ⟨sIdx, q⟩
    · have hInl : (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam false la j qR (.inl n)).run
          (encRouterTbls ℓ Pt tReal tSlot) =
          (query (spec := unifSpec + FsPubSpec ℓ Pt) (.inl n) >>=
            fun u => pure (u, encRouterTbls ℓ Pt tReal tSlot)) := stateT_run_lift _ _
      rw [hInl, sessRedImpl_inl_eq]
      simp only [bind_assoc, pure_bind]
      apply coinSimEquiv_query_bind; intro u
      exact ih u rem used tReal tSlot
        (fun s hs => qb_step_of_false (hRem s hs) rfl u)
        (hCrK u)
        (fun s hs => qb_step_of_false (hSh s hs) rfl u)
        hSum hReal hSlot
    · by_cases hEq : sIdx = j
      · subst hEq
        rw [dslRouterImpl_inr_same, sessRedImpl_inr_same_eq]
        refine coinSimEquiv_query_pure_bind _ _ _ _ fun u =>
          ih u rem used tReal tSlot
            (fun s hs => qb_step_of_false (hRem s hs) (decide_eq_false (Ne.symm hs)) u)
            (hCrK u)
            (fun s hs => qb_step_of_false (hSh s hs)
              (by simp [qIsShortBad, decide_eq_false (Ne.symm hs)]) u)
            hSum hReal hSlot
      · have hNotCr : qNotCr ℓ Pt q := by
          rcases q with (((((⟨_, _, _⟩ | ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩) | ⟨⟩) | ⟨⟩) | ⟨_, _⟩) | ⟨_, _⟩) <;>
            simp [qIsCr, qNotCr] at h0Cr ⊢
        have hNotBad : ¬ CryptoGames.FSAEAD.encBadMsg
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (AD := Header Pt) (C := ℕ × LCt)
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr q) = true := by
          have h0 := (qb_step_zero (hSh sIdx hEq)).1
          simpa [qIsShortBad] using h0
        have hShK : ∀ u s, s ≠ j → (k u).IsQueryBoundP (fun t' => qIsShortBad ℓ Pt s t' = true) 0 :=
          fun u s hs => (qb_step_zero (hSh s hs)).2 u
        obtain ⟨hPos, hRemIdxK⟩ := qb_step_of_true (by simp [qOnSess]) (hRem sIdx hEq)
        have hn : used sIdx < 2 * qR + 4 := by have := hSum sIdx hEq; omega
        let rem' := Function.update rem sIdx (rem sIdx - 1)
        let used' := Function.update used sIdx (used sIdx + 1)
        have hRemK : ∀ u s, s ≠ j → (k u).IsQueryBoundP (fun t' => qOnSess ℓ Pt s t' = true) (rem' s) :=
          fun u s hs => by
            by_cases hss : s = sIdx
            · subst hss; simpa [rem'] using hRemIdxK u
            · simpa [rem', hss] using
                qb_step_of_false (hRem s hs) (decide_eq_false (Ne.symm hss)) u
        have hSum' : ∀ s ≠ j, used' s + rem' s ≤ 2 * qR + 4 := fun s hs => by
          by_cases hss : s = sIdx
          · subst hss; simp only [used', rem', Function.update_self]; have := hSum s hs; omega
          · simp only [used', rem', Function.update_of_ne hss]; exact hSum s hs
        by_cases hLt : sIdx < j
        · refine (coinSimEquiv_bind_left
            (dslRouter_slotBranch_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj
              false la j qR sIdx q tReal tSlot (Or.inl ⟨rfl, hLt⟩)
              (used sIdx) hn (hSlot sIdx hEq) hNotCr hNotBad) _).trans ?_
          rw [sessRedImpl_inr_lt_eq _ _ hLt]
          refine coinSimEquiv_liftP_map_bind_liftM_of_support (IfaceF) rfl
            ((slotWrapPubImpl ℓ Pt C encT idOf false la qR q).run (tSlot sIdx)) _ _ _ _ fun w hw => ?_
          have hwInv := slotWrapPubImpl_support_step ℓ Pt C encT idOf false la qR q
            (tSlot sIdx) (used sIdx) (hSlot sIdx hEq) w hw
          exact ih w.1 rem' used' tReal (Function.update tSlot sIdx w.2)
            (hRemK w.1) (hCrK w.1) (hShK w.1) hSum'
            (fun s hs => by
              by_cases hss : s = sIdx
              · subst hss; simp only [used', Function.update_self]
                exact realOptInv_mono ℓ Pt (Nat.le_succ _) (hReal s hs)
              · simp only [used', Function.update_of_ne hss]; exact hReal s hs)
            (fun s hs => by
              by_cases hss : s = sIdx
              · subst hss; simpa [used'] using hwInv
              · simp only [used', Function.update_of_ne hss]; exact hSlot s hs)
        · have hGt : j < sIdx := Nat.lt_of_le_of_ne (Nat.not_lt.mp hLt) (Ne.symm hEq)
          refine (coinSimEquiv_bind_left
            (dslRouter_realBranch_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj
              false la j qR sIdx q tReal tSlot (Or.inl ⟨rfl, hGt⟩)
              (used sIdx) hn (hReal sIdx hEq) hNotCr hNotBad) _).trans ?_
          rw [sessRedImpl_inr_gt_eq _ _ hGt]
          refine coinSimEquiv_liftP_map_bind_liftM_of_support (IfaceF) rfl
            ((realWrapPubImpl ℓ Pt C encT idOf false la qR q).run (tReal sIdx)) _ _ _ _ fun w hw => ?_
          have hwInv := realWrapPubImpl_support_step ℓ Pt C encT idOf false la qR q
            (tReal sIdx) (used sIdx) (hReal sIdx hEq) w hw
          exact ih w.1 rem' used' (Function.update tReal sIdx w.2) tSlot
            (hRemK w.1) (hCrK w.1) (hShK w.1) hSum'
            (fun s hs => by
              by_cases hss : s = sIdx
              · subst hss; simpa [used'] using hwInv
              · simp only [used', Function.update_of_ne hss]; exact hReal s hs)
            (fun s hs => by
              by_cases hss : s = sIdx
              · subst hss; simp only [used', Function.update_self]
                exact slotOptInv_mono ℓ Pt (Nat.le_succ _) (hSlot s hs)
              · simp only [used', Function.update_of_ne hss]; exact hSlot s hs)

private theorem dslRouter_run_coinSimEquiv_true (hinj : Function.Injective encT)
    (la : Bool) (j qR : ℕ) {α : Type}
    (M : OracleComp (unifSpec + OracleSpec.sigma (fun _ : ℕ => FsPubSpec ℓ Pt)) α) :
    ∀ (rem used : ℕ → ℕ)
      (tReal : ℕ → RealEntryDom ℓ Pt) (tSlot : ℕ → SlotEntryDom ℓ Pt),
      (∀ s ≠ j, M.IsQueryBoundP (fun t => qOnSess ℓ Pt s t = true) (rem s)) →
      M.IsQueryBoundP (fun t => qIsCr ℓ Pt t = true) 0 →
      (∀ s ≠ j, M.IsQueryBoundP (fun t => qIsShortBad ℓ Pt s t = true) 0) →
      (∀ s ≠ j, used s + rem s ≤ 2 * qR + 4) →
      (∀ s ≠ j, RealOptInv ℓ Pt (used s) (tReal s).1) →
      (∀ s ≠ j, SlotOptInv ℓ Pt (used s) (tSlot s).1) →
      CoinSimEquiv (IfaceF).fwdU
        ((simulateQ (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam true la j qR) M).run
          (encRouterTbls ℓ Pt tReal tSlot))
        (Prod.map id (fun p => encRouterTbls ℓ Pt p.2 p.1) <$>
          (simulateQ
            (CryptoVerification.E2E.Signed.SessionRouter.sessRedImpl
              (slotWrapPubImpl ℓ Pt C encT idOf true la qR)
              (realWrapPubImpl ℓ Pt C encT idOf true la qR) j)
            M).run (tSlot, tReal)) := by
  induction M using OracleComp.inductionOn with
  | pure a =>
    intro _ _ _ _ _ _ _ _ _ _
    exact CoinSimEquiv.of_eq (by simp [Prod.map])
  | query_bind t k ih =>
    intro rem used tReal tSlot hRem hCr hSh hSum hReal hSlot
    obtain ⟨h0Cr, hCrK⟩ := qb_step_zero hCr
    simp only [simulateQ_query_bind, monadLift_self, OracleQuery.input_query,
      OracleQuery.cont_query, StateT.run_bind, map_bind]
    rcases t with n | ⟨sIdx, q⟩
    · have hInl : (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam true la j qR (.inl n)).run
          (encRouterTbls ℓ Pt tReal tSlot) =
          (query (spec := unifSpec + FsPubSpec ℓ Pt) (.inl n) >>=
            fun u => pure (u, encRouterTbls ℓ Pt tReal tSlot)) := stateT_run_lift _ _
      rw [hInl, sessRedImpl_inl_eq]
      simp only [bind_assoc, pure_bind]
      apply coinSimEquiv_query_bind; intro u
      exact ih u rem used tReal tSlot
        (fun s hs => qb_step_of_false (hRem s hs) rfl u)
        (hCrK u)
        (fun s hs => qb_step_of_false (hSh s hs) rfl u)
        hSum hReal hSlot
    · by_cases hEq : sIdx = j
      · subst hEq
        rw [dslRouterImpl_inr_same, sessRedImpl_inr_same_eq]
        refine coinSimEquiv_query_pure_bind _ _ _ _ fun u =>
          ih u rem used tReal tSlot
            (fun s hs => qb_step_of_false (hRem s hs) (decide_eq_false (Ne.symm hs)) u)
            (hCrK u)
            (fun s hs => qb_step_of_false (hSh s hs)
              (by simp [qIsShortBad, decide_eq_false (Ne.symm hs)]) u)
            hSum hReal hSlot
      · have hNotCr : qNotCr ℓ Pt q := by
          rcases q with (((((⟨_, _, _⟩ | ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩) | ⟨⟩) | ⟨⟩) | ⟨_, _⟩) | ⟨_, _⟩) <;>
            simp [qIsCr, qNotCr] at h0Cr ⊢
        have hNotBad : ¬ CryptoGames.FSAEAD.encBadMsg
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (AD := Header Pt) (C := ℕ × LCt)
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr q) = true := by
          have h0 := (qb_step_zero (hSh sIdx hEq)).1
          simpa [qIsShortBad] using h0
        have hShK : ∀ u s, s ≠ j → (k u).IsQueryBoundP (fun t' => qIsShortBad ℓ Pt s t' = true) 0 :=
          fun u s hs => (qb_step_zero (hSh s hs)).2 u
        obtain ⟨hPos, hRemIdxK⟩ := qb_step_of_true (by simp [qOnSess]) (hRem sIdx hEq)
        have hn : used sIdx < 2 * qR + 4 := by have := hSum sIdx hEq; omega
        let rem' := Function.update rem sIdx (rem sIdx - 1)
        let used' := Function.update used sIdx (used sIdx + 1)
        have hRemK : ∀ u s, s ≠ j → (k u).IsQueryBoundP (fun t' => qOnSess ℓ Pt s t' = true) (rem' s) :=
          fun u s hs => by
            by_cases hss : s = sIdx
            · subst hss; simpa [rem'] using hRemIdxK u
            · simpa [rem', hss] using
                qb_step_of_false (hRem s hs) (decide_eq_false (Ne.symm hss)) u
        have hSum' : ∀ s ≠ j, used' s + rem' s ≤ 2 * qR + 4 := fun s hs => by
          by_cases hss : s = sIdx
          · subst hss; simp only [used', rem', Function.update_self]; have := hSum s hs; omega
          · simp only [used', rem', Function.update_of_ne hss]; exact hSum s hs
        by_cases hLt : sIdx < j
        · refine (coinSimEquiv_bind_left
            (dslRouter_realBranch_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj
              true la j qR sIdx q tReal tSlot (Or.inr ⟨rfl, hLt⟩)
              (used sIdx) hn (hReal sIdx hEq) hNotCr hNotBad) _).trans ?_
          rw [sessRedImpl_inr_lt_eq _ _ hLt]
          refine coinSimEquiv_liftP_map_bind_liftM_of_support (IfaceF) rfl
            ((realWrapPubImpl ℓ Pt C encT idOf true la qR q).run (tReal sIdx)) _ _ _ _ fun w hw => ?_
          have hwInv := realWrapPubImpl_support_step ℓ Pt C encT idOf true la qR q
            (tReal sIdx) (used sIdx) (hReal sIdx hEq) w hw
          exact ih w.1 rem' used' (Function.update tReal sIdx w.2) tSlot
            (hRemK w.1) (hCrK w.1) (hShK w.1) hSum'
            (fun s hs => by
              by_cases hss : s = sIdx
              · subst hss; simpa [used'] using hwInv
              · simp only [used', Function.update_of_ne hss]; exact hReal s hs)
            (fun s hs => by
              by_cases hss : s = sIdx
              · subst hss; simp only [used', Function.update_self]
                exact slotOptInv_mono ℓ Pt (Nat.le_succ _) (hSlot s hs)
              · simp only [used', Function.update_of_ne hss]; exact hSlot s hs)
        · have hGt : j < sIdx := Nat.lt_of_le_of_ne (Nat.not_lt.mp hLt) (Ne.symm hEq)
          refine (coinSimEquiv_bind_left
            (dslRouter_slotBranch_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hinj
              true la j qR sIdx q tReal tSlot (Or.inr ⟨rfl, hGt⟩)
              (used sIdx) hn (hSlot sIdx hEq) hNotCr hNotBad) _).trans ?_
          rw [sessRedImpl_inr_gt_eq _ _ hGt]
          refine coinSimEquiv_liftP_map_bind_liftM_of_support (IfaceF) rfl
            ((slotWrapPubImpl ℓ Pt C encT idOf true la qR q).run (tSlot sIdx)) _ _ _ _ fun w hw => ?_
          have hwInv := slotWrapPubImpl_support_step ℓ Pt C encT idOf true la qR q
            (tSlot sIdx) (used sIdx) (hSlot sIdx hEq) w hw
          exact ih w.1 rem' used' tReal (Function.update tSlot sIdx w.2)
            (hRemK w.1) (hCrK w.1) (hShK w.1) hSum'
            (fun s hs => by
              by_cases hss : s = sIdx
              · subst hss; simp only [used', Function.update_self]
                exact realOptInv_mono ℓ Pt (Nat.le_succ _) (hReal s hs)
              · simp only [used', Function.update_of_ne hss]; exact hReal s hs)
            (fun s hs => by
              by_cases hss : s = sIdx
              · subst hss; simpa [used'] using hwInv
              · simp only [used', Function.update_of_ne hss]; exact hSlot s hs)

theorem dslRouter_coinSimEquiv (hinj : Function.Injective encT)
    (stage la : Bool) (j qR : ℕ)
    (M : MultiSessPubFsAdv Pt ℓ)
    (hSimQ : ∀ s ≠ j, M.IsQueryBoundP (fun t => qOnSess ℓ Pt s t = true) (2 * qR + 4))
    (hNoCr : M.IsQueryBoundP (fun t => qIsCr ℓ Pt t = true) 0)
    (hShort : ∀ s ≠ j, M.IsQueryBoundP (fun t => qIsShortBad ℓ Pt s t = true) 0) :
    let cut := authHopCutoff maxForwardJumps qR la
    CoinSimEquiv (IfaceF).fwdU
      (Prod.fst <$>
        (simulateQ (dslRouterImpl ℓ Pt C Dh encPt encT idOf lam stage la j qR) M).run
          ((fun _ => (false, none), fun _ => (false, none)) : (routerStTy ℓ Pt).denote))
      (if stage then
        Computational.Proofs.HeadlineV1.Stage2RouterHelpers.lPubWireSessAdv
          C protoSignalCodec ℓ encT (fun _ => idOf) maxForwardJumps cut la (fun _ => M)
          (hp cut cut la) () j
      else
        Computational.Proofs.HeadlineV1.Stage2RouterHelpers.lPubSessAdv
          C protoSignalCodec ℓ encT (fun _ => idOf) maxForwardJumps cut la (fun _ => M) () j) := by
  intro cut
  cases stage
  · refine ((dslRouter_run_coinSimEquiv_false ℓ Pt C Dh encPt encT idOf lam hinj la j qR M
      (fun _ => 2 * qR + 4) (fun _ => 0) (fun _ => (none, false)) (fun _ => (none, false))
      hSimQ hNoCr hShort (fun _ _ => by simp) (fun _ _ => trivial) (fun _ _ => trivial)).map
      Prod.fst).trans (CoinSimEquiv.of_eq ?_)
    simp only [Functor.map_map, Bool.false_eq_true, ↓reduceIte]
    rfl
  · refine ((dslRouter_run_coinSimEquiv_true ℓ Pt C Dh encPt encT idOf lam hinj la j qR M
      (fun _ => 2 * qR + 4) (fun _ => 0) (fun _ => (none, false)) (fun _ => (none, false))
      hSimQ hNoCr hShort (fun _ _ => by simp) (fun _ _ => trivial) (fun _ _ => trivial)).map
      Prod.fst).trans (CoinSimEquiv.of_eq ?_)
    simp only [Functor.map_map, ↓reduceIte]
    rfl

end RouterDSL

end Computational.Proofs.SessionCostedFig8.BundlesMultiFsEval

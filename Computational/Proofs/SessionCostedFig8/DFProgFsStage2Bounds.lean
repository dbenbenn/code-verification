/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.DFProgBucketBounds -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFs -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs
import Computational.Proofs.SessionCostedFig8.BundlesAuxSize
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase
import Computational.Proofs.SessionCostedFig8.DFProgBoundsBase
import Computational.Proofs.SessionCostedFig8.DFProgSizeBounds
import Computational.Proofs.ReductionDsl.SM.DeliverForge
import Computational.Proofs.ReductionDsl.Fig8SourceCosts
import Computational.Proofs.ReductionDsl.Fig8ExcessCosts
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
import Computational.Proofs.ReductionDsl.Fig8WeightedParts
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.ReductionDsl.Notation
import Mathlib.Data.Nat.Log
import Computational.Proofs.SessionCostedFig8.DFProgFsStage2StepCost
import Computational.Proofs.SessionCostedFig8.DFProgFsStage2DeliverCost
import Computational.Proofs.E2E.RefuseCorrB0Core
import Computational.Proofs.E2E.Relabel.GameEq
import Computational.Proofs.E2E.SpkHop1A
import Computational.Proofs.HeadlineV1.CouplingV1
import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.PubRed
import ToMathlib.Control.StateT
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.Append
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Stage-2 Multi-Session FS-AEAD Atomic Program Bounds (`[B7]` & `[B7] × [B8]`)

Compiles the multi-session `SM.specDF` FS-AEAD reductions (`redFSAuthDFMultiProg`,
`redFSAuthDFMultiBucketProg`, `redFSAuthDFPaperMultiProg`, `redFSAuthDFShiftedPaperMultiProg`,
`redFSAuthDFShiftedDir2PaperMultiProg`, and `redFSAuthDFPaperMultiBucketProg`) via
`BundlesMultiFs.compileFsMultiDFAtomic` and proves `GRedBounded` within `ratchetCostBudget q qep`.-/

namespace Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds

open Computational.Proofs.SessionCostedFig8.DFProgFsStage2DeliverCost (
  implECDF_multi_compCostW_le implECDFShiftedPaperGen_multi_compCostW_le)
open Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs (
  coinBranchRed coinBranchRed_eval coinBranchRed_compCostW coinBranchRed_totalQueries_le
  coinBranchRed_compSizeW coinBranchRed_compListMNodes coinBranchRed_compQueryCount
  ckaCoinBranchDFRed ckaCoinBranchDFRed_eval ckaCoinBranchDFRed_eval_sampleT
  ckaCoinBranchDFRed_isQueryBoundP redFSAuthDFMultiAtomicProg redFSAuthDFMultiBucketAtomicProg
  redFSAuthDFPaperMultiAtomicProg redFSAuthDFShiftedPaperMultiAtomicProg
  redFSAuthDFShiftedDir2PaperMultiAtomicProg redFSAuthDFCasePaperMultiAtomicProg
  redFSAuthDFPaperMultiBucketAtomicProg redFSAuthDFPaperMultiBucketAtomicProg_eq_compile)

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.SM.Construction (Header healEpoch redFSAuthDFMultiProg
  redFSAuthDFMultiBucketProg redFSAuthDFPaperMultiProg redFSAuthDFPaperMultiBucketProg
  redFSAuthDFPaperMultiBucketModeProg fsaeadMultiHeaderAdIface)
open _root_.ReductionDsl (Sig Ops Ty Var Env Expr Comp Iface GameCodec CostedReduction
  fsaeadHeaderIface fig8SmCodecDF bits reductionSizeBudget bits_le_succ liftRen)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (exprCostUB exprCost_le_costUB
  compCostUB compCost_le_costUB)
open scoped Computational.Proofs.ReductionDsl.Notation
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
local notation "Bytes" => List (BitVec 8)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun CKASamp)
open _root_.CryptoGames.PRFPRNG (prngSMCodecDF)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalSession (GRedBounded ratchetCostBudget)
open Computational.Proofs.SessionCostedFig8.Bundles (ckaOpS ckaSampS ckaQueryS exprSizeW compSizeW)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (compileFsMultiDFAtomic
  compileFsMultiDFAtomic_gRedBounded)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase (fsMultiQueryC fsMultiQueryS
  compListMNodes compQueryCount comp_renameM_queries)
open Computational.Proofs.SessionCostedFig8.DFProgBucketBounds (dummyFsStage2AtomicProg
  dummyFsStage2AtomicProg_gRedBounded)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMultiGenProg redFSAuthDFShiftedPaperMultiProg
  redFSAuthDFShiftedDir2PaperMultiProg)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW compCostW compCostW_rename)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded authOutE_cost_le
  bits_le_bits_qep_add bits_succ_le cCompContainsE_cost_le cGsEpoch_cost cGsSetWin_cost
  cGsSt_cost cInTransitE_cost_le cRecPos_cost cTrivialE_cost_le commitEC_cost_le esAbort_cost
  esG_cost esH_cost esSetG_cost esSetH_cost implEC_cost_le isSomeE_cost
  modeCfgEC_injectFullE_cost_le otherE_cost pGet_cost v0_cost v1_cost v2_cost v3_cost v4_cost
  v5_cost v6_cost vRecvC_cost_le)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (HooksExcessBounded ckaOpC ckaSampC
  cInTransitE_excessUB commitEC_excessUB_le compCostW_le_cost_add_excessUB compExcessUB
  compExcessUB_bind compExcessUB_caseOpt compExcessUB_caseSum compExcessUB_ite compExcessUB_query
  compExcessUB_ret compExcessUB_sample corrDoomE_excessUB exprExcessUB exprExcessUB_add
  exprExcessUB_and exprExcessUB_anyB exprExcessUB_appendL exprExcessUB_bool exprExcessUB_caseOpt
  exprExcessUB_caseSum exprExcessUB_cons exprExcessUB_divK exprExcessUB_eqN exprExcessUB_findB
  exprExcessUB_foldrB exprExcessUB_fst exprExcessUB_inl exprExcessUB_inr exprExcessUB_ite
  exprExcessUB_len exprExcessUB_letE exprExcessUB_lt exprExcessUB_mapB exprExcessUB_modK
  exprExcessUB_mulK exprExcessUB_nat exprExcessUB_nil exprExcessUB_none exprExcessUB_not
  exprExcessUB_op exprExcessUB_pair exprExcessUB_snd exprExcessUB_some exprExcessUB_sub
  exprExcessUB_take exprExcessUB_tconst exprExcessUB_tget exprExcessUB_tset exprExcessUB_unit
  exprExcessUB_v0 exprExcessUB_v1 exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4 exprExcessUB_v5
  exprExcessUB_v6 exprExcessUB_v7 exprExcessUB_var modeCfgEC_challMsgE_excessUB
  modeCfgEC_challOKE_excessUB modeCfgEC_injectFullE_excessUB optNatLit_excessUB
  pureEngineExprs_excessUB rangeListC_excessUB vRecvC_excessUB_le vSendC_excessUB_le)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound compCostW_le_of_parts
  bits_le_add_one)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (HooksSizeBounded
  bits_B0_le_ratchetCostBudget bits_four bits_le_ratchetCostBudget_of_le_linear bits_one
  bits_qep_le_ratchetCostBudget bits_three bits_two bits_zero compSizeW_bind compSizeW_caseOpt
  compSizeW_caseSum compSizeW_ite compSizeW_query compSizeW_ret compSizeW_sample exprSizeW_add
  exprSizeW_and exprSizeW_anyB exprSizeW_bool exprSizeW_caseOpt exprSizeW_caseSum exprSizeW_cons
  exprSizeW_eqN exprSizeW_findB exprSizeW_foldrB exprSizeW_fst exprSizeW_inl exprSizeW_inr
  exprSizeW_ite exprSizeW_letE exprSizeW_lt exprSizeW_modK exprSizeW_mulK exprSizeW_nat
  exprSizeW_nil exprSizeW_none exprSizeW_not exprSizeW_op exprSizeW_pair exprSizeW_snd
  exprSizeW_some exprSizeW_sub exprSizeW_tconst exprSizeW_tget exprSizeW_tset exprSizeW_unit
  exprSizeW_v0 exprSizeW_v1 exprSizeW_v2 exprSizeW_v3 exprSizeW_v4 exprSizeW_v5 exprSizeW_v6
  exprSizeW_v7 exprSizeW_var fsTransFindE_sizeW_le implEC_sizeW_le optNatLit_sizeW
  pureEngineExprs_sizeW_le rangeListC_sizeW size_le_ratchetSizeBudget)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_pos size_le_budget_of_log_cost)







private theorem compCostW_bind_ret_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec}
    {opC : O'.Op → ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {a r : Ty S'}
    (e : Expr O' Γ' a) (k : Comp O' I' (a :: Γ') r)
    {ce ck : ℕ} (he : exprCostW opC e ≤ ce) (hk : compCostW opC sC qC k ≤ ck) :
    compCostW opC sC qC (.bind (.ret e) k) ≤ ce + ck + 2 := by
  simp only [compCostW]
  omega

private theorem compCostW_caseSum_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec}
    {opC : O'.Op → ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {a b r : Ty S'}
    (s : Expr O' Γ' (.sum a b)) (l : Comp O' I' (a :: Γ') r) (d : Comp O' I' (b :: Γ') r)
    {cs m : ℕ} (hs : exprCostW opC s ≤ cs)
    (hl : compCostW opC sC qC l ≤ m) (hd : compCostW opC sC qC d ≤ m) :
    compCostW opC sC qC (.caseSum s l d) ≤ cs + m + 1 := by
  simp only [compCostW]
  exact Nat.add_le_add (Nat.add_le_add hs (max_le hl hd)) le_rfl


private theorem cost_bind_ret_le_costUB {S : Sig} {O : Ops S} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S TSpec} {Γ' : List (Ty S)} {t u : Ty S}
    (e : Expr O Γ' t) (k : Comp O I' (t :: Γ') u) :
    (Comp.bind (.ret e) k).cost ≤ e.cost + compCostUB k + 2 := by
  have hk := compCost_le_costUB k; simp only [Comp.cost]; omega

section MultiFsHookBounds

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "S_cka" => _root_.CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  _root_.CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM_fs" =>
  _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
local notation "mHsTy" =>
  _root_.CryptoGames.SM.Construction.fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mVpTy" =>
  _root_.CryptoGames.SM.Construction.fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mEsTy" =>
  _root_.CryptoGames.SM.Construction.fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E

/-! ### 1. Shared Multi-Session Helper Bounds (`tableLookupE`, `lookupMultiFC`, `regSess*`, `rootFSMultiC`, `fsTrans*`, `unliftMultiVRE`) -/

set_option linter.unusedSimpArgs false in
private theorem tableLookupE_bounds (B0 L : ℕ) {Γ'}
    (tblE : Expr OO_cka Γ' (.list (_root_.CryptoGames.SM.Construction.fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (ikE : Expr OO_cka Γ' (.base .i)) :
    (_root_.CryptoGames.SM.Construction.tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L tblE ikE).cost ≤ tblE.cost + ikE.cost + 30 * L + 20 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tblE ikE) ≤
      exprExcessUB (ckaOpC B0) tblE + exprExcessUB (ckaOpC B0) ikE + 10 * L ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tblE ikE) ≤
      exprSizeW (ckaOpS B0) tblE + exprSizeW (ckaOpS B0) ikE + bits L + 400 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.tableLookupE, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaOps, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.tableLookupE, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var, exprExcessUB_none,
      exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_foldrB, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.tableLookupE, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_none, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_letE, exprSizeW_op,
      exprSizeW_foldrB, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem lookupMultiFC_bounds (B0 L : ℕ) {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ}
    {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ikE : Expr OO_cka Γ' (.base .i)) :
    (_root_.CryptoGames.SM.Construction.lookupMultiFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE ikE).cost ≤
      hE.cost + ikE.cost + 30 * L + 80 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.lookupMultiFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE ikE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ikE + 10 * L + 210 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.lookupMultiFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE ikE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ikE + bits L + 800 := by
  let Γ0 : List (Ty S_cka) := .prod mHsTy (.base .i) :: Γ'
  have htl := tableLookupE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0)
    (_root_.CryptoGames.SM.Construction.fsMultiHsTable (.fst .v0)) (.snd .v0)
  rcases htl with ⟨htlC, htlE, htlS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiHsTable, Expr.cost, v0_cost, Nat.reduceAdd] at htlC
    simp only [_root_.CryptoGames.SM.Construction.lookupMultiFC, _root_.CryptoGames.SM.Construction.fsMultiHsSetTable,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface, _root_.CryptoGames.PRFPRNG.prngSamplers,
      _root_.CryptoGames.CKA.ckaSamplers, Comp.cost, Expr.cost, v0_cost, v1_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiHsTable, exprExcessUB_v0, exprExcessUB_fst,
      exprExcessUB_snd, Nat.reduceAdd] at htlE
    simp only [_root_.CryptoGames.SM.Construction.lookupMultiFC, _root_.CryptoGames.SM.Construction.fsMultiHsSetTable,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      ckaSampC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_unit, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_cons, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_caseOpt, compExcessUB_sample, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiHsTable, exprSizeW_v0, exprSizeW_fst,
      exprSizeW_snd, Nat.reduceAdd] at htlS
    simp only [_root_.CryptoGames.SM.Construction.lookupMultiFC, _root_.CryptoGames.SM.Construction.fsMultiHsSetTable,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      ckaSampS, exprSizeW_v0, exprSizeW_v1, exprSizeW_unit, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_cons, compSizeW_ret, compSizeW_bind, compSizeW_caseOpt,
      compSizeW_sample, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem regSessMultiE_bounds (B0 L : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ikE : Expr OO_cka Γ' (.base .i)) :
    (_root_.CryptoGames.SM.Construction.regSessMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L hE ikE).cost ≤ hE.cost + ikE.cost + 90 * L + 120 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.regSessMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L hE ikE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ikE + 20 * L ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.regSessMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L hE ikE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ikE + 4 * bits L + 900 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.regSessMultiE, _root_.CryptoGames.SM.Construction.sessionsMemE,
      _root_.CryptoGames.SM.Construction.sessionsIdxOfE, _root_.CryptoGames.SM.Construction.sessionsLenE,
      _root_.CryptoGames.SM.Construction.sessionsAppendOneE, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetSessions, _root_.CryptoGames.SM.Construction.fsMultiHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiHsCache, _root_.CryptoGames.SM.Construction.fsMultiHsTable,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.orE, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, v2_cost, bits_zero, bits_one,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  · simp only [_root_.CryptoGames.SM.Construction.regSessMultiE, _root_.CryptoGames.SM.Construction.sessionsMemE,
      _root_.CryptoGames.SM.Construction.sessionsIdxOfE, _root_.CryptoGames.SM.Construction.sessionsLenE,
      _root_.CryptoGames.SM.Construction.sessionsAppendOneE, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetSessions, _root_.CryptoGames.SM.Construction.fsMultiHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiHsCache, _root_.CryptoGames.SM.Construction.fsMultiHsTable,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.orE, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var, exprExcessUB_bool,
      exprExcessUB_nat, exprExcessUB_nil, exprExcessUB_add, exprExcessUB_ite, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_cons, exprExcessUB_letE, exprExcessUB_op,
      exprExcessUB_foldrB, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.regSessMultiE, _root_.CryptoGames.SM.Construction.sessionsMemE,
      _root_.CryptoGames.SM.Construction.sessionsIdxOfE, _root_.CryptoGames.SM.Construction.sessionsLenE,
      _root_.CryptoGames.SM.Construction.sessionsAppendOneE, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetSessions, _root_.CryptoGames.SM.Construction.fsMultiHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiHsCache, _root_.CryptoGames.SM.Construction.fsMultiHsTable,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.orE, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_nil, exprSizeW_add, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_cons, exprSizeW_letE, exprSizeW_op, exprSizeW_foldrB, bits_zero, bits_one,
      Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem regSessOptMultiE_bounds (B0 L : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (sidE : Expr OO_cka Γ' (.opt (.base .i))) :
    (_root_.CryptoGames.SM.Construction.regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L hE sidE).cost ≤ hE.cost + sidE.cost + 180 * L + 280 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L hE sidE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) sidE + 40 * L ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L hE sidE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) sidE + 8 * bits L + 1900 := by
  let Γ0 : List (Ty S_cka) := .base .i :: .prod mHsTy (.opt (.base .i)) :: Γ'
  have hr := regSessMultiE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0) (.fst .v1) .v0
  rcases hr with ⟨hrC, hrE, hrS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [Expr.cost, v0_cost, v1_cost, Nat.reduceAdd] at hrC
    simp only [_root_.CryptoGames.SM.Construction.regSessOptMultiE, Expr.cost, v0_cost, v1_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  · simp only [exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_fst, Nat.reduceAdd] at hrE
    simp only [_root_.CryptoGames.SM.Construction.regSessOptMultiE, exprExcessUB_v0, exprExcessUB_v1,
      exprExcessUB_none, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE, Nat.reduceAdd]
    omega
  · simp only [exprSizeW_v0, exprSizeW_v1, exprSizeW_fst, Nat.reduceAdd] at hrS
    simp only [_root_.CryptoGames.SM.Construction.regSessOptMultiE, exprSizeW_v0, exprSizeW_v1,
      exprSizeW_none, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_letE, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem rootFSMultiC_bounds (B0 L : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (tE : Expr OO_cka Γ' .nat)
    (ikE : Expr OO_cka Γ' (.base .i)) (σE : Expr OO_cka Γ' (.base .sig)) :
    (_root_.CryptoGames.SM.Construction.rootFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE).cost ≤
      hE.cost + tE.cost + ikE.cost + σE.cost + 30 * L + 2 * bits mo.tStar + 2 * bits mo.tH + 260 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.rootFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) tE +
        exprExcessUB (ckaOpC B0) ikE + exprExcessUB (ckaOpC B0) σE + 10 * L + 1200 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.rootFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) ikE +
        exprSizeW (ckaOpS B0) σE + bits L + 4 * bits mo.tStar + 4 * bits mo.tH + 3800 := by
  let Γ0 : List (Ty S_cka) := .prod mHsTy (.prod .nat (.prod (.base .i) (.base .sig))) :: Γ'
  have hlk := lookupMultiFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (qC := qC) (qS := qS)
    B0 L (Γ' := Γ0) (.fst .v0) (.fst (.snd (.snd .v0)))
  rcases hlk with ⟨hlkC, hlkE, hlkS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [Expr.cost, v0_cost, Nat.reduceAdd] at hlkC
    simp only [_root_.CryptoGames.SM.Construction.rootFSMultiC, _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaSamplers,
      _root_.CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, Nat.reduceAdd]
    omega
  · simp only [exprExcessUB_v0, exprExcessUB_fst, exprExcessUB_snd, Nat.reduceAdd] at hlkE
    simp only [_root_.CryptoGames.SM.Construction.rootFSMultiC, ckaOpC,
      ckaSampC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_unit,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_and, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some,
      exprExcessUB_op, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_sample,
      Nat.reduceAdd]
    omega
  · simp only [exprSizeW_v0, exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at hlkS
    simp only [_root_.CryptoGames.SM.Construction.rootFSMultiC, ckaOpS,
      ckaSampS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_unit, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_none, exprSizeW_lt, exprSizeW_eqN, exprSizeW_and, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_op, compSizeW_ret, compSizeW_bind,
      compSizeW_ite, compSizeW_sample, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem fsTransFindE_bounds (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ' (.list (_root_.CryptoGames.SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (hcE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (_root_.CryptoGames.SM.Construction.fsTransFindE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L trE hcE).cost ≤ trE.cost + hcE.cost + 55 * L + 20 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.fsTransFindE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L trE hcE) ≤
      exprExcessUB (ckaOpC B0) trE + exprExcessUB (ckaOpC B0) hcE + 150 * L ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.fsTransFindE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L trE hcE) ≤
      exprSizeW (ckaOpS B0) trE + exprSizeW (ckaOpS B0) hcE + bits L + 700 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFindE, _root_.CryptoGames.SM.Engine.hdrCtEqE,
      _root_.CryptoGames.SM.Engine.optTEqE, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, v2_cost, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFindE, _root_.CryptoGames.SM.Engine.hdrCtEqE,
      _root_.CryptoGames.SM.Engine.optTEqE, ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
      exprExcessUB_var, exprExcessUB_bool, exprExcessUB_eqN, exprExcessUB_and, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
      exprExcessUB_findB, Nat.reduceAdd]
    omega
  · exact ProgSizeBounds.fsTransFindE_sizeW_le B0 L trE hcE

set_option linter.unusedSimpArgs false in
private theorem fsTransFilterE_bounds (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ' (.list (_root_.CryptoGames.SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (dropE : Expr OO_cka Γ' .nat) :
    (_root_.CryptoGames.SM.Construction.fsTransFilterE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L trE dropE).cost ≤ trE.cost + dropE.cost + 15 * L + 15 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.fsTransFilterE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L trE dropE) ≤
      exprExcessUB (ckaOpC B0) trE + exprExcessUB (ckaOpC B0) dropE ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.fsTransFilterE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L trE dropE) ≤
      exprSizeW (ckaOpS B0) trE + exprSizeW (ckaOpS B0) dropE + bits L + 100 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFilterE, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFilterE, exprExcessUB_v0, exprExcessUB_v1,
      exprExcessUB_v2, exprExcessUB_nil, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_cons, exprExcessUB_letE,
      exprExcessUB_foldrB, Nat.reduceAdd, Nat.mul_zero]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFilterE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
      exprSizeW_nil, exprSizeW_eqN, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_cons, exprSizeW_letE, exprSizeW_foldrB, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem unliftMultiVRE_bounds (B0 L : ℕ) {Γ'}
    (vRE : Expr OO_cka Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO_cka Γ' (.list .nat)) :
    (_root_.CryptoGames.SM.Construction.unliftMultiVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L vRE rngE).cost ≤ vRE.cost + rngE.cost + 220 * L + 30 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.unliftMultiVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprExcessUB (ckaOpC B0) vRE + exprExcessUB (ckaOpC B0) rngE ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.unliftMultiVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprSizeW (ckaOpS B0) vRE + exprSizeW (ckaOpS B0) rngE + bits L + 100 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.unliftMultiVRE, _root_.CryptoGames.SM.Construction.unliftMultiEntryE,
      Expr.cost, v0_cost, v1_cost, v2_cost, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.unliftMultiVRE, _root_.CryptoGames.SM.Construction.unliftMultiEntryE,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_none, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum,
      exprExcessUB_letE, exprExcessUB_foldrB, exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
      Nat.reduceAdd, Nat.mul_zero]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.unliftMultiVRE, _root_.CryptoGames.SM.Construction.unliftMultiEntryE,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_none, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE,
      exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset, Nat.reduceAdd]
    omega

/-! ### 2. Multi-Session Hook, Init, and Finish Bounds (`hooksFSMultiC`, `hooksFSMultiDFC`) -/


set_option linter.unusedSimpArgs false in
private theorem fsMultiStartSendC_bounds (B0 L : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σE : Expr OO_cka Γ' (.base .sig))
    (rE : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    (_root_.CryptoGames.SM.Construction.fsMultiStartSendC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE ctxE pE tE γE σE rE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + γE.cost + σE.cost + rE.cost) +
        1400 * L + 2 * bits mo.tStar + 2 * bits mo.tH + 3000 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiStartSendC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE ctxE pE tE γE σE rE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) γE + exprExcessUB (ckaOpC B0) σE +
        exprExcessUB (ckaOpC B0) rE) + 350 * L + 3000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiStartSendC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE ctxE pE tE γE σE rE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) γE + exprSizeW (ckaOpS B0) σE +
        exprSizeW (ckaOpS B0) rE) + 65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + 24000 := by
  let Γ0 : List (Ty S_cka) := .base .ccoins :: .prod mHsTy (.prod .nat (.prod (.base .γ)
    (.prod (.base .sig) (.opt (.base .ccoins))))) :: Γ'
  let Γ1 : List (Ty S_cka) := .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mHsTy :: Γ0
  have hrt := rootFSMultiC_bounds (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (qC := qC) (qS := qS) B0 L mo
    (Γ' := Γ0) (.fst .v1) (.fst (.snd .v1))
    (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
    (.fst (.snd (.snd (.snd .v1))))
  have hreg := regSessOptMultiE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1) (.snd .v0) (.snd (.snd (.fst .v0)))
  rcases hrt with ⟨hrtC, hrtE, hrtS⟩
  rcases hreg with ⟨hregC, hregE, hregS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps, Expr.cost, v0_cost, v1_cost,
      Nat.reduceAdd] at hrtC hregC
    simp only [_root_.CryptoGames.SM.Construction.fsMultiStartSendC, _root_.CryptoGames.SM.Construction.fsMultiHsSetCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface, _root_.CryptoGames.PRFPRNG.prngSamplers,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_op, Nat.reduceAdd] at hrtE hregE
    simp only [_root_.CryptoGames.SM.Construction.fsMultiStartSendC, _root_.CryptoGames.SM.Construction.fsMultiHsSetCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      ckaOpC, ckaSampC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_unit,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_op, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_caseOpt, compExcessUB_sample, Nat.reduceAdd]
    omega
  · simp only [ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_op, Nat.reduceAdd] at hrtS hregS
    simp only [_root_.CryptoGames.SM.Construction.fsMultiStartSendC, _root_.CryptoGames.SM.Construction.fsMultiHsSetCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      ckaOpS, ckaSampS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_unit, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_op, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_caseOpt, compSizeW_sample,
      Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem fsMultiStartRecvC_bounds (B0 L : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode) (gMain : Bool)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σE : Expr OO_cka Γ' (.base .sig)) (tnE : Expr OO_cka Γ' (.base .t)) :
    (_root_.CryptoGames.SM.Construction.fsMultiStartRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo gMain hE ctxE pE tE γE σE tnE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + γE.cost + σE.cost + tnE.cost) +
        250 * L + bits mo.tStar + 600 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiStartRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo gMain hE ctxE pE tE γE σE tnE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) γE + exprExcessUB (ckaOpC B0) σE +
        exprExcessUB (ckaOpC B0) tnE) + 60 * L + 2000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiStartRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo gMain hE ctxE pE tE γE σE tnE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) γE + exprSizeW (ckaOpS B0) σE +
        exprSizeW (ckaOpS B0) tnE) + 10 * bits L + bits mo.tStar + 8000 := by
  let Γ0 : List (Ty S_cka) := .prod mHsTy (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))) :: Γ'
  let Γ1 : List (Ty S_cka) := .prod (.base .k) mHsTy :: Γ0
  have hlk := lookupMultiFC_bounds (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (qC := qC) (qS := qS) B0 L
    (Γ' := Γ0) (.fst .v0)
    (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))
  have hreg := regSessMultiE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1) (.snd .v0)
    (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))
  rcases hlk with ⟨hlkC, hlkE, hlkS⟩
  rcases hreg with ⟨hregC, hregE, hregS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps, Expr.cost, v0_cost, v1_cost,
      Nat.reduceAdd] at hlkC hregC
    simp only [_root_.CryptoGames.SM.Construction.fsMultiStartRecvC, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  · simp only [ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_op, Nat.reduceAdd] at hlkE hregE
    simp only [_root_.CryptoGames.SM.Construction.fsMultiStartRecvC, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_bool, exprExcessUB_nat,
      exprExcessUB_none, exprExcessUB_eqN, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_op, exprExcessUB_tget, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_ite, compExcessUB_caseOpt, Nat.reduceAdd]
    omega
  · simp only [ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_op, Nat.reduceAdd] at hlkS hregS
    simp only [_root_.CryptoGames.SM.Construction.fsMultiStartRecvC, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_eqN, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tget,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem fsMultiDFStartRecvC_bounds (B0 L : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σE : Expr OO_cka Γ' (.base .sig)) (tnE : Expr OO_cka Γ' (.base .t)) :
    (_root_.CryptoGames.SM.Construction.fsMultiDFStartRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE ctxE pE tE γE σE tnE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + γE.cost + σE.cost + tnE.cost) +
        250 * L + bits mo.tStar + 600 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiDFStartRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE ctxE pE tE γE σE tnE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) γE + exprExcessUB (ckaOpC B0) σE +
        exprExcessUB (ckaOpC B0) tnE) + 60 * L + 2000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiDFStartRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE ctxE pE tE γE σE tnE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) γE + exprSizeW (ckaOpS B0) σE +
        exprSizeW (ckaOpS B0) tnE) + 10 * bits L + bits mo.tStar + 8000 := by
  let Γ0 : List (Ty S_cka) := .prod mHsTy (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))) :: Γ'
  let Γ1 : List (Ty S_cka) := .prod (.base .k) mHsTy :: Γ0
  have hlk := lookupMultiFC_bounds (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (qC := qC) (qS := qS) B0 L
    (Γ' := Γ0) (.fst .v0)
    (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))
  have hreg := regSessMultiE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1) (.snd .v0)
    (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))
  rcases hlk with ⟨hlkC, hlkE, hlkS⟩
  rcases hreg with ⟨hregC, hregE, hregS⟩
  have heqLk : _root_.CryptoGames.SM.Construction.lookupMultiDFFC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L (Γ' := Γ0) (.fst .v0)
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))))) =
    _root_.CryptoGames.SM.Construction.lookupMultiFC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L (Γ' := Γ0) (.fst .v0)
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))))) := rfl
  have heqReg : _root_.CryptoGames.SM.Construction.regSessMultiDFE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L (Γ' := Γ1) (.snd .v0)
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))) =
    _root_.CryptoGames.SM.Construction.regSessMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L (Γ' := Γ1) (.snd .v0)
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))) := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps, Expr.cost, v0_cost, v1_cost,
      Nat.reduceAdd] at hlkC hregC
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFStartRecvC, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      heqLk, heqReg, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost,
      v0_cost, v1_cost, v2_cost, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  · simp only [ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_op, Nat.reduceAdd] at hlkE hregE
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFStartRecvC, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      heqLk, heqReg, ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_bool,
      exprExcessUB_nat, exprExcessUB_none, exprExcessUB_eqN, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_op, exprExcessUB_tget, compExcessUB_ret,
      compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.reduceAdd]
    omega
  · simp only [ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_op, Nat.reduceAdd] at hlkS hregS
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFStartRecvC, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      heqLk, heqReg, ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_eqN, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_op,
      exprSizeW_tget, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, Nat.reduceAdd]
    omega

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem fsMultiFsSendC_bounds (B0 Δcka : ℕ) (la : Bool) (hΔ : Δcka ≤ 1)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (ssvE : Expr OO_cka Γ' (.sum (.base .ss) .nat))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (mE : Expr OO_cka Γ' (.base .msg)) (pairE : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (_root_.CryptoGames.SM.Construction.fsMultiFsSendC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + ssvE.cost + hdrE.cost + mE.cost + pairE.cost) + 2000 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiFsSendC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) ssvE + exprExcessUB (ckaOpC B0) hdrE +
        exprExcessUB (ckaOpC B0) mE + exprExcessUB (ckaOpC B0) pairE) +
        qC .cs + qC .tr + qC .ch + 762000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiFsSendC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) ssvE + exprSizeW (ckaOpS B0) hdrE +
        exprSizeW (ckaOpS B0) mE + exprSizeW (ckaOpS B0) pairE) +
        qS .cs + qS .tr + qS .ch + 6000 := by
  have hΔb : bits (2 + Δcka) ≤ 3 := by
    rcases (by omega : Δcka = 0 ∨ Δcka = 1) with rfl | rfl <;> decide
  cases la
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [_root_.CryptoGames.SM.Construction.fsMultiFsSendC]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine (cost_bind_ret_le_costUB _ _).trans ?_
      simp only [_root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cGsTL,
        _root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt,
        _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
        _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
        _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
        _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
        _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
        _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
        _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface, _root_.CryptoGames.PRFPRNG.prngOps,
        _root_.CryptoGames.CKA.ckaOps, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
        bits_zero, bits_one, bits_two, bits_three, dsl_cost, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Construction.fsMultiFsSendC, Bool.false_eq_true, ↓reduceIte,
        _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cGsTL,
        _root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt,
        _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
        _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
        _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
        _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
        _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
        _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
        _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
        exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
        exprExcessUB_nil, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_not, exprExcessUB_and,
        exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
        exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
        exprExcessUB_cons, exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind,
        compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Construction.fsMultiFsSendC, Bool.false_eq_true, ↓reduceIte,
        _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cGsTL,
        _root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt,
        _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
        _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
        _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
        _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
        _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
        _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
        _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
        exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
        exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
        exprSizeW_add, exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
        exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
        exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
        exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite,
        compSizeW_caseOpt, compSizeW_caseSum, compSizeW_query, bits_zero, bits_one, bits_two, bits_three,
        Nat.reduceAdd]
      omega

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem fsMultiDFFsSendC_bounds (B0 Δcka : ℕ) (la : Bool) (hΔ : Δcka ≤ 1)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (ssvE : Expr OO_cka Γ' (.sum (.base .ss) .nat))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (mE : Expr OO_cka Γ' (.base .msg)) (pairE : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (_root_.CryptoGames.SM.Construction.fsMultiDFFsSendC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + ssvE.cost + hdrE.cost + mE.cost + pairE.cost) + 2000 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiDFFsSendC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) ssvE + exprExcessUB (ckaOpC B0) hdrE +
        exprExcessUB (ckaOpC B0) mE + exprExcessUB (ckaOpC B0) pairE) +
        qC .cs + qC .tr + qC .ch + 762000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiDFFsSendC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) ssvE + exprSizeW (ckaOpS B0) hdrE +
        exprSizeW (ckaOpS B0) mE + exprSizeW (ckaOpS B0) pairE) +
        qS .cs + qS .tr + qS .ch + 6000 := by
  have hΔb : bits (2 + Δcka) ≤ 3 := by
    rcases (by omega : Δcka = 0 ∨ Δcka = 1) with rfl | rfl <;> decide
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [_root_.CryptoGames.SM.Construction.fsMultiDFFsSendC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [_root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsMk, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsTable, _root_.CryptoGames.SM.Construction.fsMultiDFHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsBook, _root_.CryptoGames.SM.Construction.fsMultiDFHsLfWin,
      _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaOps, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
      bits_zero, bits_one, bits_two, bits_three, dsl_cost, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFFsSendC,
      _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsMk, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsTable, _root_.CryptoGames.SM.Construction.fsMultiDFHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsBook, _root_.CryptoGames.SM.Construction.fsMultiDFHsLfWin,
      _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
      exprExcessUB_nil, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_not, exprExcessUB_and,
      exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
      exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
      exprExcessUB_cons, exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFFsSendC,
      _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsMk, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsTable, _root_.CryptoGames.SM.Construction.fsMultiDFHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsBook, _root_.CryptoGames.SM.Construction.fsMultiDFHsLfWin,
      _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
      exprSizeW_add, exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
      exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite,
      compSizeW_caseOpt, compSizeW_caseSum, compSizeW_query, bits_zero, bits_one, bits_two, bits_three,
      Nat.reduceAdd]
    omega

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem fsMultiFsRecvC_bounds_false (B0 L B Δcka : ℕ) (hΔ : Δcka ≤ 1)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (rsvE : Expr OO_cka Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (eE : Expr OO_cka Γ' (.base .ct)) (recE : Expr OO_cka Γ' (.opt _root_.CryptoGames.SM.Engine.cRecTy)) :
    (_root_.CryptoGames.SM.Construction.fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B false Δcka hE ctxE pE tE rsvE hdrE eE recE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + rsvE.cost + hdrE.cost + eE.cost + recE.cost) +
        300 * L + (B + 1) + 2900 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B false Δcka hE ctxE pE tE rsvE hdrE eE recE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) rsvE + exprExcessUB (ckaOpC B0) hdrE +
        exprExcessUB (ckaOpC B0) eE + exprExcessUB (ckaOpC B0) recE) +
        750 * L + 20 * B0 + 3 * bits B + qC .cs + qC .dl + qC .ij + 2725000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B false Δcka hE ctxE pE tE rsvE hdrE eE recE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) rsvE + exprSizeW (ckaOpS B0) hdrE +
        exprSizeW (ckaOpS B0) eE + exprSizeW (ckaOpS B0) recE) +
        6 * bits B0 + 4 * bits B + 7 * bits L + qS .cs + qS .dl + qS .ij + 10500 := by
  have hB := bits_le_add_one B
  have hΔ01 : Δcka = 0 ∨ Δcka = 1 := by omega
  have hΔb : bits (2 + Δcka) ≤ 3 := by rcases hΔ01 with rfl | rfl <;> simp only [Nat.reduceAdd, bits_two, bits_three] <;> omega
  let hdrT := _root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
  let tupT : Ty S_cka := .prod mHsTy (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpTy) (.prod .nat
    (.prod (.sum (.base .rs) .nat) (.prod hdrT
      (.prod (.base .ct) (.opt _root_.CryptoGames.SM.Engine.cRecTy))))))
  let Γ0 : List (Ty S_cka) := .nat :: tupT :: Γ'
  let rrT : Ty S_cka := .sum .unit (.prod .nat (.opt (.base .msg)))
  let outVTy : Ty S_cka := .opt (.prod (.sum (.base .rs) .nat) (.prod .nat (.base .msg)))
  let Γ_ok : List (Ty S_cka) := .prod .bool mHsTy :: Γ0
  let Γ2 : List (Ty S_cka) := .prod .nat (.opt (.base .msg)) :: rrT :: .opt rrT :: Γ_ok
  let Γ3 : List (Ty S_cka) := outVTy :: Γ2
  have htf0 := fsTransFindE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v1) .v0)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))))
  have htf_ok := fsTransFindE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_ok)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v2) .v1)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v2))))) (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))
  have htf2 := fsTransFindE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v5) .v4)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5)))))))
  have hfl2 := fsTransFilterE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.snd .v3) .v4)))
    (.caseOpt (_root_.CryptoGames.SM.Construction.fsTransFindE L
        (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v5) .v4)))
        (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
      (.fst .v0) (.fst .v0))
  have htf3 := fsTransFindE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ3)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v6) .v5)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v6))))) (.fst (.snd (.snd (.snd (.snd (.snd .v6)))))))
  have hfl3 := fsTransFilterE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ3)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.snd .v4) .v5)))
    (.caseOpt (_root_.CryptoGames.SM.Construction.fsTransFindE L
        (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v6) .v5)))
        (.pair (.fst (.snd (.snd (.snd (.snd .v6))))) (.fst (.snd (.snd (.snd (.snd (.snd .v6))))))))
      (.fst .v1) (.fst .v0))
  rcases htf0 with ⟨_, htf0E, htf0S⟩
  rcases htf_ok with ⟨_, htfOkE, htfOkS⟩
  rcases htf2 with ⟨_, htf2E, htf2S⟩
  rcases hfl2 with ⟨_, hfl2E, hfl2S⟩
  rcases htf3 with ⟨_, htf3E, htf3S⟩
  rcases hfl3 with ⟨_, hfl3E, hfl3S⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold _root_.CryptoGames.SM.Construction.fsMultiFsRecvC
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.Construction.fsTransFindE, _root_.CryptoGames.SM.Construction.fsTransFilterE,
      _root_.CryptoGames.SM.Engine.hdrCtEqE, _root_.CryptoGames.SM.Engine.optTEqE,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
      bits_zero, bits_one, bits_two, bits_three, dsl_cost, Nat.reduceAdd]
    omega
  · unfold _root_.CryptoGames.SM.Construction.fsMultiFsRecvC
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsBook,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_v5, exprExcessUB_v6,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_nil, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_tget, Nat.reduceAdd] at htf0E htfOkE htf2E hfl2E htf3E hfl3E
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
      exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add, exprExcessUB_lt,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
      exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
    omega
  · unfold _root_.CryptoGames.SM.Construction.fsMultiFsRecvC
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsBook,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, Expr.v6, exprSizeW_var,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_nil, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_caseOpt, exprSizeW_tget, bits_zero, Nat.reduceAdd] at htf0S htfOkS htf2S hfl2S htf3S hfl3S
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, Expr.v6,
      exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
      exprSizeW_add, exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_tget,
      exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
      compSizeW_caseSum, compSizeW_query, bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
    omega

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem fsMultiFsRecvC_bounds_true (B0 L B Δcka : ℕ) (hΔ : Δcka ≤ 1)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (rsvE : Expr OO_cka Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (eE : Expr OO_cka Γ' (.base .ct)) (recE : Expr OO_cka Γ' (.opt _root_.CryptoGames.SM.Engine.cRecTy)) :
    (_root_.CryptoGames.SM.Construction.fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B true Δcka hE ctxE pE tE rsvE hdrE eE recE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + rsvE.cost + hdrE.cost + eE.cost + recE.cost) +
        300 * L + (B + 1) + 2900 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B true Δcka hE ctxE pE tE rsvE hdrE eE recE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) rsvE + exprExcessUB (ckaOpC B0) hdrE +
        exprExcessUB (ckaOpC B0) eE + exprExcessUB (ckaOpC B0) recE) +
        750 * L + 20 * B0 + 3 * bits B + qC .cs + qC .dl + qC .ij + 2725000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B true Δcka hE ctxE pE tE rsvE hdrE eE recE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) rsvE + exprSizeW (ckaOpS B0) hdrE +
        exprSizeW (ckaOpS B0) eE + exprSizeW (ckaOpS B0) recE) +
        6 * bits B0 + 4 * bits B + 7 * bits L + qS .cs + qS .dl + qS .ij + 10500 := by
  have hB := bits_le_add_one B
  have hΔ01 : Δcka = 0 ∨ Δcka = 1 := by omega
  have hΔb : bits (2 + Δcka) ≤ 3 := by rcases hΔ01 with rfl | rfl <;> simp only [Nat.reduceAdd, bits_two, bits_three] <;> omega
  let hdrT := _root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
  let tupT : Ty S_cka := .prod mHsTy (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpTy) (.prod .nat
    (.prod (.sum (.base .rs) .nat) (.prod hdrT
      (.prod (.base .ct) (.opt _root_.CryptoGames.SM.Engine.cRecTy))))))
  let Γ0 : List (Ty S_cka) := .nat :: tupT :: Γ'
  let rrT : Ty S_cka := .sum .unit (.prod .nat (.opt (.base .msg)))
  let outVTy : Ty S_cka := .opt (.prod (.sum (.base .rs) .nat) (.prod .nat (.base .msg)))
  let Γ1 : List (Ty S_cka) := .prod .nat (.opt (.base .msg)) :: rrT :: .opt rrT :: Γ0
  let Γ1_v : List (Ty S_cka) := outVTy :: Γ1
  have htf0 := fsTransFindE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v1) .v0)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))))
  have htf1 := fsTransFindE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v4) .v3)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) (.fst (.snd (.snd (.snd (.snd (.snd .v4)))))))
  have hfl := fsTransFilterE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v4) .v3)))
    (.caseOpt (_root_.CryptoGames.SM.Construction.fsTransFindE L
        (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v4) .v3)))
        (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))))
      (.fst .v0) (.fst .v0))
  have htf1_v := fsTransFindE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1_v)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v5) .v4)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5)))))))
  have hfl_v := fsTransFilterE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1_v)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v5) .v4)))
    (.caseOpt (_root_.CryptoGames.SM.Construction.fsTransFindE L
        (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt (.fst .v5) .v4)))
        (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
      (.fst .v1) (.fst .v0))
  rcases htf0 with ⟨_, htf0E, htf0S⟩
  rcases htf1 with ⟨_, htf1E, htf1S⟩
  rcases hfl with ⟨_, hflE, hflS⟩
  rcases htf1_v with ⟨_, htf1vE, htf1vS⟩
  rcases hfl_v with ⟨_, hflvE, hflvS⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold _root_.CryptoGames.SM.Construction.fsMultiFsRecvC
    simp only [↓reduceIte]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.Construction.fsTransFindE, _root_.CryptoGames.SM.Construction.fsTransFilterE,
      _root_.CryptoGames.SM.Engine.hdrCtEqE, _root_.CryptoGames.SM.Engine.optTEqE,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
      bits_zero, bits_one, bits_two, bits_three, dsl_cost, Nat.reduceAdd]
    omega
  · unfold _root_.CryptoGames.SM.Construction.fsMultiFsRecvC
    simp only [↓reduceIte]
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsBook,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_v5, exprExcessUB_bool,
      exprExcessUB_nat, exprExcessUB_nil, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_caseOpt, exprExcessUB_tget, Nat.reduceAdd] at htf0E htf1E hflE htf1vE hflvE
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_v5,
      exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
      exprExcessUB_add, exprExcessUB_lt, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
      exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE,
      exprExcessUB_op, exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret,
      compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_caseSum,
      compExcessUB_query, Nat.reduceAdd]
    omega
  · unfold _root_.CryptoGames.SM.Construction.fsMultiFsRecvC
    simp only [↓reduceIte]
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsBook,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_nil, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_tget,
      bits_zero, Nat.reduceAdd] at htf0S htf1S hflS htf1vS hflvS
    simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_var,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_lt,
      exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE,
      exprSizeW_op, exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind,
      compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum, compSizeW_query,
      bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
    omega

private theorem fsMultiFsRecvC_bounds (B0 L B Δcka : ℕ) (la : Bool) (hΔ : Δcka ≤ 1)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (rsvE : Expr OO_cka Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (eE : Expr OO_cka Γ' (.base .ct)) (recE : Expr OO_cka Γ' (.opt _root_.CryptoGames.SM.Engine.cRecTy)) :
    (_root_.CryptoGames.SM.Construction.fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B la Δcka hE ctxE pE tE rsvE hdrE eE recE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + rsvE.cost + hdrE.cost + eE.cost + recE.cost) +
        300 * L + (B + 1) + 2900 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B la Δcka hE ctxE pE tE rsvE hdrE eE recE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) rsvE + exprExcessUB (ckaOpC B0) hdrE +
        exprExcessUB (ckaOpC B0) eE + exprExcessUB (ckaOpC B0) recE) +
        750 * L + 20 * B0 + 3 * bits B + qC .cs + qC .dl + qC .ij + 2725000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B la Δcka hE ctxE pE tE rsvE hdrE eE recE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) rsvE + exprSizeW (ckaOpS B0) hdrE +
        exprSizeW (ckaOpS B0) eE + exprSizeW (ckaOpS B0) recE) +
        6 * bits B0 + 4 * bits B + 7 * bits L + qS .cs + qS .dl + qS .ij + 10500 := by
  cases la
  · exact fsMultiFsRecvC_bounds_false B0 L B Δcka hΔ hE ctxE pE tE rsvE hdrE eE recE
  · exact fsMultiFsRecvC_bounds_true B0 L B Δcka hΔ hE ctxE pE tE rsvE hdrE eE recE

set_option linter.unusedSimpArgs false in
private theorem fsMultiDFFsRecvC_bounds (B0 L B : ℕ) (la : Bool)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (rsvE : Expr OO_cka Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (eE : Expr OO_cka Γ' (.base .ct)) (recE : Expr OO_cka Γ' (.opt _root_.CryptoGames.SM.Engine.cRecTy)) :
    (_root_.CryptoGames.SM.Construction.fsMultiDFFsRecvC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B la hE ctxE pE tE rsvE hdrE eE recE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + rsvE.cost + hdrE.cost + eE.cost + recE.cost) +
        250 * L + (B + 1) + 2500 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiDFFsRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B la hE ctxE pE tE rsvE hdrE eE recE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) rsvE + exprExcessUB (ckaOpC B0) hdrE +
        exprExcessUB (ckaOpC B0) eE + exprExcessUB (ckaOpC B0) recE) +
        500 * L + 20 * B0 + 3 * bits B + qC .dl + qC .ij + 2720000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiDFFsRecvC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B la hE ctxE pE tE rsvE hdrE eE recE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) rsvE + exprSizeW (ckaOpS B0) hdrE +
        exprSizeW (ckaOpS B0) eE + exprSizeW (ckaOpS B0) recE) +
        6 * bits B0 + 4 * bits B + 6 * bits L + qS .dl + qS .ij + 10000 := by
  have hB := bits_le_add_one B
  let hdrT := _root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
  let tupT : Ty S_cka := .prod mHsTy (.prod (.sum (.base .rs) .nat) (.prod hdrT
    (.prod (.base .ct) (.opt _root_.CryptoGames.SM.Engine.cRecTy))))
  let Γ0 : List (Ty S_cka) := .nat :: tupT :: Γ'
  let rrT : Ty S_cka := .sum .unit (.prod .nat (.opt (.base .msg)))
  let Γ1 : List (Ty S_cka) := .prod .nat (.opt (.base .msg)) :: rrT :: .opt rrT :: Γ0
  have htf0 := fsTransFindE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt (.fst .v1) .v0)))
    (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
  have htf1 := fsTransFindE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt (.fst .v4) .v3)))
    (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4)))))
  have hfl := fsTransFilterE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
    (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt (.fst .v4) .v3)))
    (.caseOpt (_root_.CryptoGames.SM.Construction.fsTransFindE L
        (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt (.fst .v4) .v3)))
        (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))))
      (.fst .v0) (.fst .v0))
  rcases htf0 with ⟨htf0C, htf0E, htf0S⟩
  rcases htf1 with ⟨htf1C, htf1E, htf1S⟩
  rcases hfl with ⟨hflC, hflE, hflS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsBook,
      Expr.cost, v0_cost, v1_cost, v3_cost, v4_cost, bits_zero,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd] at htf0C htf1C hflC
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFFsRecvC, _root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsSetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsMk, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsTable, _root_.CryptoGames.SM.Construction.fsMultiDFHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsBook, _root_.CryptoGames.SM.Construction.fsMultiDFHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost,
      v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, bits_zero,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs at hflC ⊢ <;> omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsBook,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_bool,
      exprExcessUB_nat, exprExcessUB_nil, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_caseOpt, exprExcessUB_tget, Nat.reduceAdd] at htf0E htf1E hflE
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFFsRecvC, _root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsSetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsMk, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsTable, _root_.CryptoGames.SM.Construction.fsMultiDFHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsBook, _root_.CryptoGames.SM.Construction.fsMultiDFHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil, exprExcessUB_lt,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_op,
      exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite,
      compExcessUB_caseOpt, compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsBook,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v3, exprSizeW_v4, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_nil, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_tget,
      bits_zero, Nat.reduceAdd] at htf0S htf1S hflS
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFFsRecvC, _root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsSetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsMk, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsTable, _root_.CryptoGames.SM.Construction.fsMultiDFHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsBook, _root_.CryptoGames.SM.Construction.fsMultiDFHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_lt,
      exprSizeW_not, exprSizeW_and, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_op,
      exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite,
      compSizeW_caseOpt, compSizeW_caseSum, compSizeW_query, bits_zero, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem fsMultiRevealC_bounds (B0 L : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode) (la : Bool)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (vpE : Expr OO_cka Γ' mVpTy) :
    (_root_.CryptoGames.SM.Construction.fsMultiRevealC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + vpE.cost) + 360 * L + bits mo.tStar + 1000 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiRevealC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) vpE) + qC .cs + 1000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiRevealC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) vpE) + 4 * bits L + bits mo.tStar + qS .cs + 4000 := by
  let Γ0 : List (Ty S_cka) := .prod mHsTy mVpTy :: Γ'
  cases la
  · let Γ3 : List (Ty S_cka) := .list .nat :: .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) mHsTy :: Γ0
    have huv := unliftMultiVRE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ3) (_root_.CryptoGames.SM.Engine.vpVR (.snd .v3)) .v0
    rcases huv with ⟨_huvC, huvE, huvS⟩
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [_root_.CryptoGames.SM.Construction.fsMultiRevealC]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine (cost_bind_ret_le_costUB _ _).trans ?_
      simp only [_root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt,
        _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
        _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
        _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
        _root_.CryptoGames.SM.Construction.rangeListC,
        _root_.CryptoGames.SM.Construction.unliftMultiVRE, _root_.CryptoGames.SM.Construction.unliftMultiEntryE,
        _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
        _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
        _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
        _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
        Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, bits_zero, bits_one,
        dsl_cost, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Engine.vpVR, exprExcessUB_v0, exprExcessUB_v3, exprExcessUB_fst,
        exprExcessUB_snd, Nat.reduceAdd] at huvE
      simp only [_root_.CryptoGames.SM.Construction.fsMultiRevealC, Bool.false_eq_true, ↓reduceIte,
        _root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt,
        _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
        _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
        _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
        _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
        _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
        _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
        rangeListC_excessUB, ckaOpC, ckaSampC,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_var,
        exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
        exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some,
        exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE, exprExcessUB_tget, exprExcessUB_tset,
        compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
        compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Engine.vpVR, exprSizeW_v0, exprSizeW_v3, exprSizeW_var, exprSizeW_fst,
        exprSizeW_snd, Nat.reduceAdd] at huvS
      simp only [_root_.CryptoGames.SM.Construction.fsMultiRevealC, Bool.false_eq_true, ↓reduceIte,
        _root_.CryptoGames.SM.Construction.fsMultiHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiHsSetBookAt,
        _root_.CryptoGames.SM.Construction.fsMultiHsMk, _root_.CryptoGames.SM.Construction.fsMultiHsCache,
        _root_.CryptoGames.SM.Construction.fsMultiHsTable, _root_.CryptoGames.SM.Construction.fsMultiHsSessions,
        _root_.CryptoGames.SM.Construction.fsMultiHsBook, _root_.CryptoGames.SM.Construction.fsMultiHsLfWin,
        _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
        _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
        _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
        rangeListC_sizeW, ckaOpS, ckaSampS,
        exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
        exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
        exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some,
        exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_tget, exprSizeW_tset,
        compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
        compSizeW_caseSum, compSizeW_query, bits_zero, Nat.reduceAdd]
      omega
  · let Γ2t : List (Ty S_cka) := .list .nat :: .opt (.base .ss) :: Γ0
    have huv := unliftMultiVRE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2t) (_root_.CryptoGames.SM.Engine.vpVR (.snd .v2)) .v0
    rcases huv with ⟨_huvC, huvE, huvS⟩
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [_root_.CryptoGames.SM.Construction.fsMultiRevealC]
      simp only [↓reduceIte]
      refine (cost_bind_ret_le_costUB _ _).trans ?_
      simp only [_root_.CryptoGames.SM.Construction.rangeListC,
        _root_.CryptoGames.SM.Construction.unliftMultiVRE, _root_.CryptoGames.SM.Construction.unliftMultiEntryE,
        _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
        _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
        _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
        Expr.cost, Expr.v0, Expr.v1, Expr.v2, bits_zero, bits_one,
        dsl_cost, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Engine.vpVR, exprExcessUB_v0, exprExcessUB_v2, exprExcessUB_fst,
        exprExcessUB_snd, Nat.reduceAdd] at huvE
      simp only [_root_.CryptoGames.SM.Construction.fsMultiRevealC, ↓reduceIte,
        _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
        _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
        _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
        rangeListC_excessUB, ckaOpC, ckaSampC,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_var,
        exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
        exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some,
        exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE, exprExcessUB_tget,
        compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
        Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Engine.vpVR, exprSizeW_v0, exprSizeW_v2, exprSizeW_var, exprSizeW_fst,
        exprSizeW_snd, Nat.reduceAdd] at huvS
      simp only [_root_.CryptoGames.SM.Construction.fsMultiRevealC, ↓reduceIte,
        _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
        _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
        _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
        rangeListC_sizeW, ckaOpS, ckaSampS,
        exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
        exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
        exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some,
        exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_tget,
        compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
        bits_zero, Nat.reduceAdd]
      omega

set_option linter.unusedSimpArgs false in
private theorem fsMultiDFRevealC_bounds (B0 L : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode) (la : Bool)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mHsTy) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool) (vpE : Expr OO_cka Γ' mVpTy) :
    (_root_.CryptoGames.SM.Construction.fsMultiDFRevealC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + vpE.cost) + 360 * L + bits mo.tStar + 1000 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.fsMultiDFRevealC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE + exprExcessUB (ckaOpC B0) pE +
        exprExcessUB (ckaOpC B0) vpE) + qC .cs + 1000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.fsMultiDFRevealC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) vpE) + 4 * bits L + bits mo.tStar + qS .cs + 4000 := by
  let Γ0 : List (Ty S_cka) := .prod mHsTy mVpTy :: Γ'
  let Γ3 : List (Ty S_cka) := .list .nat :: .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) mHsTy :: Γ0
  have huv := unliftMultiVRE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ3) (_root_.CryptoGames.SM.Engine.vpVR (.snd .v3)) .v0
  have heqUv : ∀ {Γ''} (v : Expr OO_cka Γ'' (.tbl (.opt (.sum (.base .rs) .nat)))) (r : Expr OO_cka Γ'' (.list .nat)),
      _root_.CryptoGames.SM.Construction.unliftMultiDFVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L v r =
      _root_.CryptoGames.SM.Construction.unliftMultiVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L v r := fun _ _ => rfl
  rcases huv with ⟨_huvC, huvE, huvS⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [_root_.CryptoGames.SM.Construction.fsMultiDFRevealC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsMk, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsTable, _root_.CryptoGames.SM.Construction.fsMultiDFHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsBook, _root_.CryptoGames.SM.Construction.fsMultiDFHsLfWin,
      _root_.CryptoGames.SM.Construction.rangeListC,
      _root_.CryptoGames.SM.Construction.unliftMultiDFVRE, _root_.CryptoGames.SM.Construction.unliftMultiDFEntryE,
      _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
      _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
      _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, bits_zero, bits_one,
      dsl_cost, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Engine.vpVR, exprExcessUB_v0, exprExcessUB_v3, exprExcessUB_fst,
      exprExcessUB_snd, Nat.reduceAdd] at huvE
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFRevealC, heqUv,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsMk, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsTable, _root_.CryptoGames.SM.Construction.fsMultiDFHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsBook, _root_.CryptoGames.SM.Construction.fsMultiDFHsLfWin,
      _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
      _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
      _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
      rangeListC_excessUB, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Engine.vpVR, exprSizeW_v0, exprSizeW_v3, exprSizeW_var, exprSizeW_fst,
      exprSizeW_snd, Nat.reduceAdd] at huvS
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFRevealC, heqUv,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsGetBookAt, _root_.CryptoGames.SM.Construction.fsMultiDFHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsMk, _root_.CryptoGames.SM.Construction.fsMultiDFHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsTable, _root_.CryptoGames.SM.Construction.fsMultiDFHsSessions,
      _root_.CryptoGames.SM.Construction.fsMultiDFHsBook, _root_.CryptoGames.SM.Construction.fsMultiDFHsLfWin,
      _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
      _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
      _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
      rangeListC_sizeW, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_tget, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
      compSizeW_caseSum, compSizeW_query, bits_zero, Nat.reduceAdd]
    omega

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem hooksFSMultiC_bounds (B0 L B Δcka : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode)
    (gMain la : Bool) (hΔ : Δcka ≤ 1)
    (qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ) (qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ) :
    HooksCostBounded
      (_root_.CryptoGames.SM.Construction.hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      (1400 * L + 2 * bits mo.tStar + 2 * bits mo.tH + (B + 1) + 3000) ∧
    HooksExcessBounded B0 ckaSampC qC
      (_root_.CryptoGames.SM.Construction.hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      (350 * L + qC .cs + 3000) (qC .cs + qC .tr + qC .ch + 762000)
      (750 * L + 20 * B0 + 3 * bits B + qC .cs + qC .dl + qC .ij + 2725000) ∧
    HooksSizeBounded B0 ckaSampS qS
      (_root_.CryptoGames.SM.Construction.hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      (65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + qS .cs + 24000)
      (qS .cs + qS .tr + qS .ch + 6000)
      (6 * bits B0 + 4 * bits B + 7 * bits L + qS .cs + qS .dl + qS .ij + 10500) := by
  dsimp only [_root_.CryptoGames.SM.Construction.hooksFSMultiC]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro Γ' h ctx p t γv σ r
    exact (fsMultiStartSendC_bounds B0 L mo (qC := qC) (qS := qS) h ctx p t γv σ r).1.trans (by omega)
  · intro Γ' h ctx p t γv σ tn
    exact (fsMultiStartRecvC_bounds B0 L mo gMain (qC := qC) (qS := qS) h ctx p t γv σ tn).1.trans (by omega)
  · intro Γ' h ctx p t ss hdr m pair
    exact (fsMultiFsSendC_bounds B0 Δcka la hΔ (qC := qC) (qS := qS) h ctx p t ss hdr m pair).1.trans (by omega)
  · intro Γ' h ctx p t rs hdr e rec_
    exact (fsMultiFsRecvC_bounds B0 L B Δcka la hΔ (qC := qC) (qS := qS) h ctx p t rs hdr e rec_).1.trans (by omega)
  · intro Γ' h ctx p old new
    simp only [_root_.CryptoGames.SM.Construction.fsMultiCommitC,
      Comp.cost, Expr.cost, Nat.reduceAdd]; omega
  · intro Γ' h ctx p vp
    exact (fsMultiRevealC_bounds B0 L mo la (qC := qC) (qS := qS) h ctx p vp).1.trans (by omega)
  · intro Γ' h ctx p t γv σ r
    exact (fsMultiStartSendC_bounds B0 L mo (qC := qC) (qS := qS) h ctx p t γv σ r).2.1.trans (by omega)
  · intro Γ' h ctx p t γv σ tn
    exact (fsMultiStartRecvC_bounds B0 L mo gMain (qC := qC) (qS := qS) h ctx p t γv σ tn).2.1.trans (by omega)
  · intro Γ' h ctx p t ss hdr m pair
    exact (fsMultiFsSendC_bounds B0 Δcka la hΔ (qC := qC) (qS := qS) h ctx p t ss hdr m pair).2.1.trans (by omega)
  · intro Γ' h ctx p t rs hdr e rec_
    exact (fsMultiFsRecvC_bounds B0 L B Δcka la hΔ (qC := qC) (qS := qS) h ctx p t rs hdr e rec_).2.1.trans (by omega)
  · intro Γ' h ctx p old new
    simp only [_root_.CryptoGames.SM.Construction.fsMultiCommitC,
      exprExcessUB_pair, exprExcessUB_some, compExcessUB_ret, Nat.reduceAdd]; omega
  · intro Γ' h ctx p vp
    exact (fsMultiRevealC_bounds B0 L mo la (qC := qC) (qS := qS) h ctx p vp).2.1.trans (by omega)
  · intro Γ' h ctx p t γv σ r
    exact (fsMultiStartSendC_bounds B0 L mo (qC := qC) (qS := qS) h ctx p t γv σ r).2.2.trans (by omega)
  · intro Γ' h ctx p t γv σ tn
    exact (fsMultiStartRecvC_bounds B0 L mo gMain (qC := qC) (qS := qS) h ctx p t γv σ tn).2.2.trans (by omega)
  · intro Γ' h ctx p t ss hdr m pair
    exact (fsMultiFsSendC_bounds B0 Δcka la hΔ (qC := qC) (qS := qS) h ctx p t ss hdr m pair).2.2.trans (by omega)
  · intro Γ' h ctx p t rs hdr e rec_
    exact (fsMultiFsRecvC_bounds B0 L B Δcka la hΔ (qC := qC) (qS := qS) h ctx p t rs hdr e rec_).2.2.trans (by omega)
  · intro Γ' h ctx p old new
    simp only [_root_.CryptoGames.SM.Construction.fsMultiCommitC,
      exprSizeW_pair, exprSizeW_some, compSizeW_ret, Nat.reduceAdd]; omega
  · intro Γ' h ctx p vp
    exact (fsMultiRevealC_bounds B0 L mo la (qC := qC) (qS := qS) h ctx p vp).2.2.trans (by omega)

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem hooksFSMultiDFC_bounds (B0 L B Δcka : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode)
    (la : Bool) (hΔ : Δcka ≤ 1)
    (qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ) (qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ) :
    HooksCostBounded
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo la)
      (1400 * L + 2 * bits mo.tStar + 2 * bits mo.tH + (B + 1) + 3000) ∧
    HooksExcessBounded B0 ckaSampC qC
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo la)
      (350 * L + qC .cs + 3000) (qC .cs + qC .tr + qC .ch + 762000)
      (500 * L + 20 * B0 + 3 * bits B + qC .dl + qC .ij + 2720000) ∧
    HooksSizeBounded B0 ckaSampS qS
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo la)
      (65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + qS .cs + 24000)
      (qS .cs + qS .tr + qS .ch + 6000)
      (6 * bits B0 + 4 * bits B + 6 * bits L + qS .dl + qS .ij + 10000) := by
  dsimp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFC]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro Γ' h ctx p t γv σ r
    exact (fsMultiStartSendC_bounds B0 L mo (qC := qC) (qS := qS) h ctx p t γv σ r).1.trans (by omega)
  · intro Γ' h ctx p t γv σ tn
    exact (fsMultiDFStartRecvC_bounds B0 L mo (qC := qC) (qS := qS) h ctx p t γv σ tn).1.trans (by omega)
  · intro Γ' h ctx p t ss hdr m pair
    exact (fsMultiDFFsSendC_bounds B0 Δcka la hΔ (qC := qC) (qS := qS) h ctx p t ss hdr m pair).1.trans (by omega)
  · intro Γ' h ctx p t rs hdr e rec_
    exact (fsMultiDFFsRecvC_bounds B0 L B la (qC := qC) (qS := qS) h ctx p t rs hdr e rec_).1.trans (by omega)
  · intro Γ' h ctx p old new
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFCommitC,
      Comp.cost, Expr.cost, Nat.reduceAdd]; omega
  · intro Γ' h ctx p vp
    exact (fsMultiDFRevealC_bounds B0 L mo la (qC := qC) (qS := qS) h ctx p vp).1.trans (by omega)
  · intro Γ' h ctx p t γv σ r
    exact (fsMultiStartSendC_bounds B0 L mo (qC := qC) (qS := qS) h ctx p t γv σ r).2.1.trans (by omega)
  · intro Γ' h ctx p t γv σ tn
    exact (fsMultiDFStartRecvC_bounds B0 L mo (qC := qC) (qS := qS) h ctx p t γv σ tn).2.1.trans (by omega)
  · intro Γ' h ctx p t ss hdr m pair
    exact (fsMultiDFFsSendC_bounds B0 Δcka la hΔ (qC := qC) (qS := qS) h ctx p t ss hdr m pair).2.1.trans (by omega)
  · intro Γ' h ctx p t rs hdr e rec_
    exact (fsMultiDFFsRecvC_bounds B0 L B la (qC := qC) (qS := qS) h ctx p t rs hdr e rec_).2.1.trans (by omega)
  · intro Γ' h ctx p old new
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFCommitC,
      exprExcessUB_pair, exprExcessUB_some, compExcessUB_ret, Nat.reduceAdd]; omega
  · intro Γ' h ctx p vp
    exact (fsMultiDFRevealC_bounds B0 L mo la (qC := qC) (qS := qS) h ctx p vp).2.1.trans (by omega)
  · intro Γ' h ctx p t γv σ r
    exact (fsMultiStartSendC_bounds B0 L mo (qC := qC) (qS := qS) h ctx p t γv σ r).2.2.trans (by omega)
  · intro Γ' h ctx p t γv σ tn
    exact (fsMultiDFStartRecvC_bounds B0 L mo (qC := qC) (qS := qS) h ctx p t γv σ tn).2.2.trans (by omega)
  · intro Γ' h ctx p t ss hdr m pair
    exact (fsMultiDFFsSendC_bounds B0 Δcka la hΔ (qC := qC) (qS := qS) h ctx p t ss hdr m pair).2.2.trans (by omega)
  · intro Γ' h ctx p t rs hdr e rec_
    exact (fsMultiDFFsRecvC_bounds B0 L B la (qC := qC) (qS := qS) h ctx p t rs hdr e rec_).2.2.trans (by omega)
  · intro Γ' h ctx p old new
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFCommitC,
      exprSizeW_pair, exprSizeW_some, compSizeW_ret, Nat.reduceAdd]; omega
  · intro Γ' h ctx p vp
    exact (fsMultiDFRevealC_bounds B0 L mo la (qC := qC) (qS := qS) h ctx p vp).2.2.trans (by omega)

set_option linter.unusedSimpArgs false in
private theorem initFSMultiEStateC_bounds (B0 L : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    (_root_.CryptoGames.SM.Construction.initFSMultiEStateC (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo bE).cost ≤
      bE.cost + 1500 * L + 2 * bits mo.tStar + 2 * bits mo.tH + 4000 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.initFSMultiEStateC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo bE) ≤
      exprExcessUB (ckaOpC B0) bE + 350 * L + 4000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.initFSMultiEStateC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo bE) ≤
      exprSizeW (ckaOpS B0) bE + 65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + 25000 := by
  let Γ0 : List (Ty S_cka) := .base .kc :: .base .kr :: .bool :: Γ'
  let Γ1 : List (Ty S_cka) := .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mHsTy :: Γ0
  have hrt := rootFSMultiC_bounds (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (qC := qC) (qS := qS) B0 L mo
    (Γ' := Γ0) _root_.CryptoGames.SM.Construction.fsMultiHsEmptyE (.nat 0)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.lamI .unit)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.prngInit .v1)
  have hreg := regSessOptMultiE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1) (.snd .v0) (.snd (.snd (.fst .v0)))
  rcases hrt with ⟨hrtC, hrtE, hrtS⟩
  rcases hreg with ⟨hregC, hregE, hregS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiHsEmptyE, _root_.CryptoGames.SM.Construction.fsMultiHsMk,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps, Expr.cost, v0_cost, v1_cost, bits_zero,
      Nat.reduceAdd] at hrtC hregC
    simp only [_root_.CryptoGames.SM.Construction.initFSMultiEStateC,
      _root_.CryptoGames.SM.Construction.fsMultiHsEmptyE, _root_.CryptoGames.SM.Construction.fsMultiHsMk,
      _root_.CryptoGames.SM.Engine.mkPartiesE,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, bits_zero,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiHsEmptyE, _root_.CryptoGames.SM.Construction.fsMultiHsMk,
      ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
      exprExcessUB_none, exprExcessUB_nil, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_op, exprExcessUB_tconst, Nat.reduceAdd] at hrtE hregE
    simp only [_root_.CryptoGames.SM.Construction.initFSMultiEStateC,
      _root_.CryptoGames.SM.Construction.fsMultiHsEmptyE, _root_.CryptoGames.SM.Construction.fsMultiHsMk,
      _root_.CryptoGames.SM.Engine.mkPartiesE,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Engine.vpMk, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
      exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
      exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
      exprExcessUB_tconst, exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind, compExcessUB_sample,
      Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiHsEmptyE, _root_.CryptoGames.SM.Construction.fsMultiHsMk,
      ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_nil, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_op, exprSizeW_tconst, bits_zero, Nat.reduceAdd] at hrtS hregS
    simp only [_root_.CryptoGames.SM.Construction.initFSMultiEStateC,
      _root_.CryptoGames.SM.Construction.fsMultiHsEmptyE, _root_.CryptoGames.SM.Construction.fsMultiHsMk,
      _root_.CryptoGames.SM.Engine.mkPartiesE,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Engine.vpMk, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
      exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl,
      exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op,
      exprSizeW_tconst, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_sample,
      bits_zero, Nat.reduceAdd]
    omega

private theorem finishFSMultiE_bounds (B0 L Δ : ℕ) (pol : _root_.CryptoGames.SM.Engine.Policy)
    (la : Bool) (hΔ : Δ = 2 ∨ Δ = 3) {Γ'}
    (es : Expr OO_cka Γ' (_root_.CryptoGames.SM.Construction.fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (_root_.CryptoGames.SM.Construction.finishFSMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L Δ pol la es).cost ≤
      es.cost + 100 * L + 2 * bits (pol.tL.getD 0) + 2 * bits pol.tStar + 500 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.finishFSMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L Δ pol la es) ≤
      exprExcessUB (ckaOpC B0) es ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.finishFSMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L Δ pol la es) ≤
      6 * exprSizeW (ckaOpS B0) es + 12 * bits L + 6 * bits (pol.tL.getD 0) + 6 * bits pol.tStar + 500 := by
  cases la
  · have hc0 := authOutE_cost_le (O' := OO_cka) (vpT := mVpTy) (hsT := mHsTy) L pol es
    have he0 := (pureEngineExprs_excessUB (ckaOpC B0) L 3 0 pol es).1
    have hs0 := (pureEngineExprs_sizeW_le (ckaOpS B0) L pol es).1
    rcases hΔ with rfl | rfl
    · have hEqC : (_root_.CryptoGames.SM.Engine.authOutE L 2 pol es).cost =
          (_root_.CryptoGames.SM.Engine.authOutE L 3 pol es).cost := rfl
      have hEqE : exprExcessUB (ckaOpC B0) (_root_.CryptoGames.SM.Engine.authOutE L 2 pol es) =
          exprExcessUB (ckaOpC B0) (_root_.CryptoGames.SM.Engine.authOutE L 3 pol es) := rfl
      have hEqS : exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.authOutE L 2 pol es) =
          exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.authOutE L 3 pol es) := rfl
      simp only [_root_.CryptoGames.SM.Construction.finishFSMultiE, Bool.false_eq_true, ↓reduceIte,
        hEqC, hEqE, hEqS]
      exact ⟨by omega, by omega, by omega⟩
    · simp only [_root_.CryptoGames.SM.Construction.finishFSMultiE, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, by omega, by omega⟩
  · simp only [_root_.CryptoGames.SM.Construction.finishFSMultiE, ↓reduceIte,
      _root_.CryptoGames.SM.Construction.fsMultiHsLfWin, _root_.CryptoGames.SM.Engine.esH,
      Expr.cost, exprExcessUB_fst, exprExcessUB_snd, exprSizeW_fst, exprSizeW_snd]
    exact ⟨by omega, by omega, by omega⟩

/-! ### 3. Tight Multi-Session Engine Excess/Cost/Size Helpers & Single-Epoch Bounds -/



private theorem fsMultiQueryC_bounds_all (qep qR B0 : ℕ) :
    fsMultiQueryC qep qR B0 .cs ≤ 50000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 ∧
    fsMultiQueryC qep qR B0 .tr ≤ 2000000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 ∧
    fsMultiQueryC qep qR B0 .ch ≤ 2000000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 ∧
    fsMultiQueryC qep qR B0 .dl ≤ 3500000 + 6 * bits (qep + 1) + 2500 * qR + 10 * B0 ∧
    fsMultiQueryC qep qR B0 .ij ≤ 3500000 + 6 * bits (qep + 1) + 2500 * qR + 10 * B0 := by
  rw [BundlesMultiFsBase.fsMultiQueryC_cs, BundlesMultiFsBase.fsMultiQueryC_tr,
      BundlesMultiFsBase.fsMultiQueryC_ch, BundlesMultiFsBase.fsMultiQueryC_dl,
      BundlesMultiFsBase.fsMultiQueryC_ij]
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩


private theorem bits_le_bits_succ_add15 {x q : ℕ} (hx : x ≤ 32768 * (q + 1)) :
    bits x ≤ bits (q + 1) + 15 := by
  by_cases hx0 : x = 0
  · subst hx0; rw [bits_zero]; omega
  · unfold _root_.ReductionDsl.bits
    by_contra hlt
    have hge : Nat.log 2 (q + 1) + 16 ≤ Nat.log 2 x := by omega
    have hp1 : 2 ^ (Nat.log 2 (q + 1) + 16) ≤ 2 ^ Nat.log 2 x :=
      Nat.pow_le_pow_right (by decide) hge
    have hp2 : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hx0
    have hp3 : q + 1 < 2 ^ (Nat.log 2 (q + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by decide) (q + 1)
    have hp4 : 2 ^ (Nat.log 2 (q + 1) + 16) = 2 ^ (Nat.log 2 (q + 1) + 1) * 32768 := by
      rw [show Nat.log 2 (q + 1) + 16 = (Nat.log 2 (q + 1) + 1) + 15 by omega, Nat.pow_add]
    omega


private theorem bits_add_le_add (n : ℕ) : ∀ k, bits (n + k) ≤ bits n + k
  | 0 => le_rfl
  | k + 1 => (bits_succ_le (n + k)).trans (by have := bits_add_le_add n k; omega)

private theorem healEpoch_le_add3 {tL : Option ℕ} {m : ℕ} (h : tL.getD 0 ≤ m) :
    healEpoch tL ≤ m + 3 := by
  cases tL <;> simp [healEpoch] at h ⊢; omega

@[local simp] private theorem priv_exprCostW_v0 {S' : Sig} {O' : Ops S'} (opC : O'.Op → ℕ)
    {t : Ty S'} {Γ' : List (Ty S')} :
    exprCostW opC (Expr.v0 : Expr O' (t :: Γ') t) = 1 := rfl

@[local simp] private theorem priv_exprCostW_v1 {S' : Sig} {O' : Ops S'} (opC : O'.Op → ℕ)
    {t0 t1 : Ty S'} {Γ' : List (Ty S')} :
    exprCostW opC (Expr.v1 : Expr O' (t0 :: t1 :: Γ') t1) = 1 := rfl




private theorem le_fig8AtomicStepBound_parts (q qepC B0 Lbq X : ℕ)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (hLbq : Lbq ≤ (q + 1) * (3 * bits qepC + 60))
    (h : X ≤ 100000 * (q + 1) + Lbq + 120 * B0 + 200 * bits qepC + 25000000) :
    X ≤ fig8AtomicStepBound q qepC := by
  unfold fig8AtomicStepBound
  dsimp only
  subst hB0
  omega

private theorem two_mul_bits_succ_add25_le_ratchet (q qep : ℕ) :
    2 * bits (q + 1) + 25 ≤ bits (ratchetCostBudget q qep) := by
  have hpow : 2 ^ Nat.log 2 (q + 1) ≤ q + 1 := Nat.pow_log_le_self 2 (by omega)
  have hsq : 2 ^ (2 * Nat.log 2 (q + 1) + 26) ≤ ratchetCostBudget q qep := by
    unfold ratchetCostBudget maxForwardJumps
    have hexp : 2 ^ (2 * Nat.log 2 (q + 1) + 26) =
        2 ^ 12 * ((2 ^ Nat.log 2 (q + 1)) ^ 2) * 16384 := by
      rw [show 2 * Nat.log 2 (q + 1) + 26 = 2 * Nat.log 2 (q + 1) + 12 + 14 by omega,
        Nat.pow_add, Nat.pow_add, Nat.mul_comm 2 (Nat.log 2 (q + 1)), Nat.pow_mul]
      ring
    rw [hexp]
    have hpow2 : (2 ^ Nat.log 2 (q + 1)) ^ 2 ≤ (q + 1) ^ 2 := by
      rw [Nat.pow_two, Nat.pow_two]
      exact Nat.mul_le_mul hpow hpow
    exact Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 12) hpow2) (by omega)
  have hlog := Nat.le_log_of_pow_le (by omega) hsq
  unfold _root_.ReductionDsl.bits
  omega

private theorem le_size_bound_of_bR_priv {X q qepC : ℕ}
    (h : ∀ bR, 2 * bits (q + 1) + 25 ≤ bR → X ≤ 1400000 + 810 * bR) :
    X ≤ 1400000 + 810 * bits (ratchetCostBudget q qepC) :=
  h (bits (ratchetCostBudget q qepC)) (two_mul_bits_succ_add25_le_ratchet q qepC)














private theorem implECDF_sizeW_le_local {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep maxSkip : ℕ) (mo : _root_.CryptoGames.SM.Construction.Mode)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.esTy
      (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    compSizeW (ckaOpS B0) sS qS
      (_root_.CryptoGames.SM.Engine.implECDF hk L 3 qep maxSkip
        (_root_.CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) ≤
      60 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) q) +
        9 * Ho + 2 * Hs + 3 * Hr + 100 * bits L + 25 * bits qep + 10 * bits maxSkip +
        20 * bits (mo.tL.getD 0) + 30 * bits mo.tStar + 42000 := by
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := _root_.CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smqdfT := _root_.CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let dfQ : Ty S_cka := .prod .bool (.prod (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
    (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))
  have him := implEC_sizeW_le hk Ho Hs Hr L qep maxSkip mo hhk
    (Γ' := smqT :: .prod esT smqdfT :: Γ') (.fst .v1) .v0
  have hdf := DFProgSizeBounds.deliverForgeEC_sizeW_le hk Ho Hs Hr L qep mo hhk
    (Γ' := dfQ :: .prod esT smqdfT :: Γ') (.fst .v1) .v0
  simp only [exprSizeW_fst, exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd] at him hdf
  simp only [_root_.CryptoGames.SM.Engine.implECDF, compSizeW_bind, compSizeW_ret, compSizeW_caseSum,
    exprSizeW_pair, exprSizeW_inl, exprSizeW_inr, exprSizeW_fst, exprSizeW_snd, exprSizeW_v0,
    Nat.reduceAdd]; omega

private theorem cCorrAllowedPaperE_costW_le {O' : Ops S_cka} {vpT : Ty S_cka}
    (opC : O'.Op → ℕ) {Γ'} (L : ℕ)
    (s : Expr O' Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    exprCostW opC (_root_.CryptoGames.SM.Engine.cCorrAllowedPaperE L s p) ≤
      exprCostW opC (_root_.CryptoGames.SM.Engine.cCorrAllowedE L s p) := by
  unfold _root_.CryptoGames.SM.Engine.cCorrAllowedPaperE _root_.CryptoGames.SM.Engine.cCorrAllowedE
  dsimp only [exprCostW]; omega

private theorem corrECPaper_costW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opC : (OO_cka).Op → ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L : ℕ) (π : _root_.CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.esTy
      (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    compCostW opC sC qC (_root_.CryptoGames.SM.Engine.corrECPaper hk L π es p) ≤
      compCostW opC sC qC (_root_.CryptoGames.SM.Engine.corrEC hk L π es p) := by
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  unfold _root_.CryptoGames.SM.Engine.corrECPaper _root_.CryptoGames.SM.Engine.corrEC
  have h := cCorrAllowedPaperE_costW_le opC (vpT := vpT)
    (Γ' := .prod (_root_.CryptoGames.SM.Engine.esTy vpT hsT) .bool :: Γ') L (_root_.CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  dsimp only [compCostW, exprCostW, _root_.CryptoGames.SM.orE]; omega

private theorem implECDFPaper_costW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (opC : (OO_cka).Op → ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfg : _root_.CryptoGames.SM.Engine.ConfigEC OO_cka)
    (π : _root_.CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.esTy
      (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    compCostW opC sC qC (_root_.CryptoGames.SM.Engine.implECDFPaper hk L Δ qep maxSkip cfg π es q) ≤
      compCostW opC sC qC (_root_.CryptoGames.SM.Engine.implECDF hk L Δ qep maxSkip cfg π es q) := by
  let esT := _root_.CryptoGames.SM.Engine.esTy
    (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT
  let smQ := _root_.CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smQDF := _root_.CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  unfold _root_.CryptoGames.SM.Engine.implECDFPaper _root_.CryptoGames.SM.Engine.implECDF
    _root_.CryptoGames.SM.Engine.implECPaper _root_.CryptoGames.SM.Engine.implEC
  have h := corrECPaper_costW_le opC sC qC hk L π
    (Γ' := .bool :: .prod esT smQ :: smQ :: .prod esT smQDF :: Γ') (.fst .v1) .v0
  dsimp only [compCostW, exprCostW]; omega















set_option maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFMultiProg_bounds
    (q qepC qR : ℕ) (la : Bool) (tL : Option ℕ) (t : ℕ)
    (hqepC : qepC ≤ q + 11) (ht : t ≤ qepC + 3)
    (htL : ∀ x, tL = some x → x ≤ qepC + 3) (hqR : qR ≤ 2 * q + 2) :
    let L := q + 1
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qepC maxForwardJumps la tL t
    (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.init +
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.finish + 100000 ≤
        fig8AtomicStepBound q qepC ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.handle + 200000 ≤
        fig8AtomicStepBound q qepC) ∧
    (compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.finish + 400 ≤
        1400000 + 810 * bits (ratchetCostBudget q qepC)) ∧
    R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  intro L B0 R0
  let mo : _root_.CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  let qC := fsMultiQueryC qepC qR B0
  let qS := fsMultiQueryS qepC qR B0
  have hmfj : maxForwardJumps = 25000 := rfl
  have htL0 : mo.tL.getD 0 ≤ qepC + 3 := by
    cases tL with
    | none => simp [mo]
    | some x => exact htL x rfl
  have htH0 : mo.tH ≤ qepC + 6 := by
    have := healEpoch_le_add3 htL0
    simp only [_root_.CryptoGames.SM.Construction.Mode.tH]; omega
  have ht_b : bits mo.tStar ≤ bits qepC + 3 :=
    (bits_mono (by simp [mo]; exact ht)).trans (bits_add_le_add qepC 3)
  have htL_b : bits (mo.tL.getD 0) ≤ bits qepC + 3 :=
    (bits_mono htL0).trans (bits_add_le_add qepC 3)
  have htH_b : bits mo.tH ≤ bits qepC + 6 :=
    (bits_mono htH0).trans (bits_add_le_add qepC 6)
  obtain ⟨hqCs, hqTr, hqCh, hqDl, hqIj⟩ := fsMultiQueryC_bounds_all qepC qR B0
  have hinit0 := initFSMultiEStateC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    (qC := qC) (qS := qS) B0 L mo (Γ' := [.unit]) (.bool false)
  rcases hinit0 with ⟨hi0C, hi0E, hi0S⟩
  have hfin0 := finishFSMultiE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (2 + 1) mo.policy la (Or.inr rfl)
    (Γ' := [mEsTy, .bool]) .v0
  rcases hfin0 with ⟨hf0C, hf0E, hf0S⟩
  have hhk := hooksFSMultiDFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B0 L B0 1 mo la le_rfl qC qS
  rcases hhk with ⟨hhkC, hhkE, hhkS⟩
  have hhkE' : HooksExcessBounded B0 ckaSampC qC
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 1 mo la)
      (3350 * L + 6 * bits (qepC + 1) + 10 * B0 + 53000)
      (9000 * L + 18 * bits (qepC + 1) + 30 * B0 + 4820000)
      (14000 * L + 18 * bits (qepC + 1) + 50 * B0 + 3 * bits B0 + 9800000) :=
    hhkE.mono (by dsimp only [L, qC] at hqCs ⊢; omega)
      (by dsimp only [L, qC] at hqCs hqTr hqCh ⊢; omega)
      (by dsimp only [L, qC] at hqCs hqDl hqIj ⊢; omega)
  have hbB0_15 : bits B0 ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add15 (by dsimp only [B0]; rw [hmfj]; omega)
  have hbqep_15 : bits qepC ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbmfj_15 : bits maxForwardJumps ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbtS_15 : bits mo.tStar ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by dsimp only [mo]; omega)
  have hbtL_15 : bits (mo.tL.getD 0) ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbtH_15 : bits mo.tH ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbqSum_15 : bits (qepC + qR + B0 + 1) ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add15 (by dsimp only [B0]; rw [hmfj]; omega)
  have hpolL : mo.policy.tL = mo.tL := rfl
  have hpolS : mo.policy.tStar = mo.tStar := rfl
  rw [hpolL, hpolS] at hf0C hf0S
  simp only [Expr.cost, v0_cost, exprExcessUB_bool, exprExcessUB_v0,
    exprSizeW_bool, exprSizeW_v0] at hi0C hi0E hi0S hf0C hf0E hf0S
  have hInitDef : (_root_.CryptoGames.SM.Construction.initFSMultiDFEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L ⟨true, tL, t⟩ (Γ' := [.unit]) (.bool false)) =
    _root_.CryptoGames.SM.Construction.initFSMultiEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L ⟨true, tL, t⟩ (Γ' := [.unit]) (.bool false) := rfl
  have hFinDef : (_root_.CryptoGames.SM.Construction.finishFSMultiDFE (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (2 + 1) (⟨true, tL, t⟩ : _root_.CryptoGames.SM.Construction.Mode).policy la (Γ' := [mEsTy, .bool]) .v0) =
    _root_.CryptoGames.SM.Construction.finishFSMultiE (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (2 + 1) (⟨true, tL, t⟩ : _root_.CryptoGames.SM.Construction.Mode).policy la (Γ' := [mEsTy, .bool]) .v0 := rfl
  have hiW : compCostW (ckaOpC B0) ckaSampC qC R0.init ≤
      1850 * L + 2 * bits mo.tStar + 2 * bits mo.tH + 8020 := by
    refine compCostW_le_of_parts
      (a := 1500 * L + 2 * bits mo.tStar + 2 * bits mo.tH + 4010)
      (b := 350 * L + 4010) ?_ ?_ (by omega)
    · dsimp only [R0, _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
      rw [hInitDef]
      dsimp only [mo] at hi0C ⊢
      simp only [Comp.cost, Expr.cost, v0_cost]
      omega
    · dsimp only [R0, _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
      rw [hInitDef]
      dsimp only [mo] at hi0E ⊢
      simp only [compExcessUB_bind, compExcessUB_ret,
        exprExcessUB_pair, exprExcessUB_unit, exprExcessUB_v0]
      omega
  have hfW : compCostW (ckaOpC B0) ckaSampC qC R0.finish ≤
      100 * L + 2 * bits (mo.tL.getD 0) + 2 * bits mo.tStar + 520 := by
    refine compCostW_le_of_parts
      (a := 100 * L + 2 * bits (mo.tL.getD 0) + 2 * bits mo.tStar + 510)
      (b := 10) ?_ ?_ (by omega)
    · dsimp only [R0, _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
      rw [hFinDef]
      dsimp only [mo] at hf0C ⊢
      simp only [Comp.cost]
      omega
    · dsimp only [R0, _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
      rw [hFinDef]
      dsimp only [mo] at hf0E ⊢
      simp only [compExcessUB_ret]
      omega
  have hiS : compSizeW (ckaOpS B0) ckaSampS qS R0.init ≤
      65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + 25020 := by
    dsimp only [R0, _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
    rw [hInitDef]
    dsimp only [mo] at hi0S ⊢
    simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit, exprSizeW_v0]
    omega
  have hfS : compSizeW (ckaOpS B0) ckaSampS qS R0.finish ≤
      12 * bits L + 6 * bits (mo.tL.getD 0) + 6 * bits mo.tStar + 520 := by
    dsimp only [R0, _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
    rw [hFinDef]
    dsimp only [mo] at hf0S ⊢
    simp only [compSizeW_ret]
    omega
  have hhdS := implECDF_sizeW_le_local
    (_root_.CryptoGames.SM.Construction.hooksFSMultiDFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 1 mo la)
    (65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + qS .cs + 24000)
    (qS .cs + qS .tr + qS .ch + 6000)
    (6 * bits B0 + 4 * bits B0 + 6 * bits L + qS .dl + qS .ij + 10000)
    L qepC maxForwardJumps mo hhkS
    (Γ' := [mEsTy, _root_.CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [exprSizeW_v0, exprSizeW_v1] at hhdS
  have hhdS' : compSizeW (ckaOpS B0) ckaSampS qS R0.handle ≤
      9 * (65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + qS .cs + 24000) +
      2 * (qS .cs + qS .tr + qS .ch + 6000) +
      3 * (6 * bits B0 + 4 * bits B0 + 6 * bits L + qS .dl + qS .ij + 10000) +
      100 * bits L + 25 * bits qepC + 10 * bits maxForwardJumps +
      30 * bits (mo.tL.getD 0) + 40 * bits mo.tStar + 46200 := by
    dsimp only [R0, _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers, mo] at hhdS ⊢
    exact hhdS.trans (by omega)
  clear hhdS
  dsimp only [qS] at hhdS'
  simp only [BundlesMultiFsBase.fsMultiQueryS_apply] at hhdS'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · refine (Nat.add_le_add (Nat.add_le_add hiW hfW) le_rfl).trans
      (le_fig8AtomicStepBound_parts q qepC B0 0 _ rfl (Nat.zero_le _) ?_)
    dsimp only [L] at hiW hfW ⊢
    omega
  · dsimp only [R0, _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
    exact implECDF_multi_compCostW_le _ q qepC mo (by simp [mo]; exact ht) htL0 hhkC hhkE'
  · refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hiS hhdS') hfS) le_rfl).trans
      (le_size_bound_of_bR_priv fun bR h2bL_bR => ?_)
    dsimp only [L] at hiS hhdS' hfS ⊢
    omega
  · dsimp only [R0]
    exact (_root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg_totalQueries
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qepC maxForwardJumps la tL t q).trans (by omega)

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFPaperMultiProg_bounds
    (q qepC qR : ℕ) (la : Bool) (tL : Option ℕ) (t : ℕ)
    (hqepC : qepC ≤ q + 11) (ht : t ≤ qepC + 3)
    (htL : ∀ x, tL = some x → x ≤ qepC + 3) (hqR : qR ≤ 2 * q + 2) :
    let L := q + 1
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qepC maxForwardJumps la tL t
    (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.init +
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.finish + 100000 ≤
        fig8AtomicStepBound q qepC ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.handle + 200000 ≤
        fig8AtomicStepBound q qepC) ∧
    (compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.finish + 400 ≤
        1400000 + 810 * bits (ratchetCostBudget q qepC)) ∧
    R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  intro L B0 R1
  let mo : _root_.CryptoGames.SM.Construction.Mode := ⟨true, tL, t⟩
  let qC := fsMultiQueryC qepC qR B0
  let qS := fsMultiQueryS qepC qR B0
  have hmfj : maxForwardJumps = 25000 := rfl
  have htL0 : mo.tL.getD 0 ≤ qepC + 3 := by
    cases tL with
    | none => simp [mo]
    | some x => exact htL x rfl
  have htH0 : mo.tH ≤ qepC + 6 := by
    have := healEpoch_le_add3 htL0
    simp only [_root_.CryptoGames.SM.Construction.Mode.tH]; omega
  have ht_b : bits mo.tStar ≤ bits qepC + 3 :=
    (bits_mono (by simp [mo]; exact ht)).trans (bits_add_le_add qepC 3)
  have htL_b : bits (mo.tL.getD 0) ≤ bits qepC + 3 :=
    (bits_mono htL0).trans (bits_add_le_add qepC 3)
  have htH_b : bits mo.tH ≤ bits qepC + 6 :=
    (bits_mono htH0).trans (bits_add_le_add qepC 6)
  obtain ⟨hqCs, hqTr, hqCh, hqDl, hqIj⟩ := fsMultiQueryC_bounds_all qepC qR B0
  have hinit0 := initFSMultiEStateC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    (qC := qC) (qS := qS) B0 L mo (Γ' := [.unit]) (.bool false)
  rcases hinit0 with ⟨hi0C, hi0E, hi0S⟩
  have hfin0 := finishFSMultiE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (2 + 1) mo.policy la (Or.inr rfl)
    (Γ' := [mEsTy, .bool]) .v0
  rcases hfin0 with ⟨hf0C, hf0E, hf0S⟩
  have hhk := hooksFSMultiC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B0 L B0 1 mo false la le_rfl qC qS
  rcases hhk with ⟨hhkC, hhkE, hhkS⟩
  have hhkE' : HooksExcessBounded B0 ckaSampC qC
      (_root_.CryptoGames.SM.Construction.hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 1 mo false la)
      (3350 * L + 6 * bits (qepC + 1) + 10 * B0 + 53000)
      (9000 * L + 18 * bits (qepC + 1) + 30 * B0 + 4820000)
      (14000 * L + 18 * bits (qepC + 1) + 50 * B0 + 3 * bits B0 + 9800000) :=
    hhkE.mono (by dsimp only [L, qC] at hqCs ⊢; omega)
      (by dsimp only [L, qC] at hqCs hqTr hqCh ⊢; omega)
      (by dsimp only [L, qC] at hqCs hqDl hqIj ⊢; omega)
  have hbB0_15 : bits B0 ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add15 (by dsimp only [B0]; rw [hmfj]; omega)
  have hbqep_15 : bits qepC ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbmfj_15 : bits maxForwardJumps ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbtS_15 : bits mo.tStar ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by dsimp only [mo]; omega)
  have hbtL_15 : bits (mo.tL.getD 0) ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbtH_15 : bits mo.tH ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbqSum_15 : bits (qepC + qR + B0 + 1) ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add15 (by dsimp only [B0]; rw [hmfj]; omega)
  have hpolL : mo.policy.tL = mo.tL := rfl
  have hpolS : mo.policy.tStar = mo.tStar := rfl
  rw [hpolL, hpolS] at hf0C hf0S
  simp only [Expr.cost, v0_cost, exprExcessUB_bool, exprExcessUB_v0,
    exprSizeW_bool, exprSizeW_v0] at hi0C hi0E hi0S hf0C hf0E hf0S
  have hiW : compCostW (ckaOpC B0) ckaSampC qC R1.init ≤
      1850 * L + 2 * bits mo.tStar + 2 * bits mo.tH + 8020 := by
    refine compCostW_le_of_parts
      (a := 1500 * L + 2 * bits mo.tStar + 2 * bits mo.tH + 4010)
      (b := 350 * L + 4010) ?_ ?_ (by omega)
    · dsimp only [R1, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
        mo] at hi0C ⊢
      simp only [Comp.cost, Expr.cost, v0_cost]
      omega
    · dsimp only [R1, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
        mo] at hi0E ⊢
      simp only [compExcessUB_bind, compExcessUB_ret,
        exprExcessUB_pair, exprExcessUB_unit, exprExcessUB_v0]
      omega
  have hfW : compCostW (ckaOpC B0) ckaSampC qC R1.finish ≤
      100 * L + 2 * bits (mo.tL.getD 0) + 2 * bits mo.tStar + 520 := by
    refine compCostW_le_of_parts
      (a := 100 * L + 2 * bits (mo.tL.getD 0) + 2 * bits mo.tStar + 510)
      (b := 10) ?_ ?_ (by omega)
    · dsimp only [R1, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
        mo] at hf0C ⊢
      simp only [Comp.cost]
      omega
    · dsimp only [R1, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
        mo] at hf0E ⊢
      simp only [compExcessUB_ret]
      omega
  have hiS : compSizeW (ckaOpS B0) ckaSampS qS R1.init ≤
      65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + 25020 := by
    dsimp only [R1, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
      mo] at hi0S ⊢
    simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit, exprSizeW_v0]
    omega
  have hfS : compSizeW (ckaOpS B0) ckaSampS qS R1.finish ≤
      12 * bits L + 6 * bits (mo.tL.getD 0) + 6 * bits mo.tStar + 520 := by
    dsimp only [R1, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
      mo] at hf0S ⊢
    simp only [compSizeW_ret]
    omega
  have hhdS := DFProgSizeBounds.implECDFPaper_sizeW_le
    (_root_.CryptoGames.SM.Construction.hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 1 mo false la)
    (65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + qS .cs + 24000)
    (qS .cs + qS .tr + qS .ch + 6000)
    (6 * bits B0 + 4 * bits B0 + 7 * bits L + qS .cs + qS .dl + qS .ij + 10500)
    L qepC maxForwardJumps mo hhkS
    (Γ' := [mEsTy, _root_.CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [exprSizeW_v0, exprSizeW_v1] at hhdS
  have hhdS' : compSizeW (ckaOpS B0) ckaSampS qS R1.handle ≤
      9 * (65 * bits L + 6 * bits mo.tStar + 6 * bits mo.tH + qS .cs + 24000) +
      2 * (qS .cs + qS .tr + qS .ch + 6000) +
      3 * (6 * bits B0 + 4 * bits B0 + 7 * bits L + qS .cs + qS .dl + qS .ij + 10500) +
      100 * bits L + 25 * bits qepC + 10 * bits maxForwardJumps +
      30 * bits (mo.tL.getD 0) + 40 * bits mo.tStar + 46200 := by
    dsimp only [R1, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers, mo] at hhdS ⊢
    exact hhdS.trans (by omega)
  clear hhdS
  dsimp only [qS] at hhdS'
  simp only [BundlesMultiFsBase.fsMultiQueryS_apply] at hhdS'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · refine (Nat.add_le_add (Nat.add_le_add hiW hfW) le_rfl).trans
      (le_fig8AtomicStepBound_parts q qepC B0 0 _ rfl (Nat.zero_le _) ?_)
    dsimp only [L] at hiW hfW ⊢
    omega
  · dsimp only [R1, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
    have hle := implECDFPaper_costW_le (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 1 mo false la)
      L (2 + 1) qepC maxForwardJumps (_root_.CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
      (Γ' := [mEsTy, _root_.CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
    have hbase := implECDF_multi_compCostW_le _ q qepC mo (by simp [mo]; exact ht) htL0 hhkC hhkE'
    exact (Nat.add_le_add_right hle 200000).trans hbase
  · refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hiS hhdS') hfS) le_rfl).trans
      (le_size_bound_of_bR_priv fun bR h2bL_bR => ?_)
    dsimp only [L] at hiS hhdS' hfS ⊢
    omega
  · dsimp only [R1]
    exact (_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg_totalQueries
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qepC maxForwardJumps la tL t q).trans (by omega)

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFShiftedPaperMultiGenProg_bounds
    (q qepC qR Δcka l tStar : ℕ) (authH la : Bool)
    (haΔ : (authH = true ∧ Δcka = 1) ∨ (authH = false ∧ Δcka = 0))
    (hqepC : qepC ≤ q + 11) (hl : l ≤ qepC + 3) (htStar : tStar ≤ qepC + 3)
    (hqR : qR ≤ 2 * q + 2) :
    let L := q + 1
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R := redFSAuthDFShiftedPaperMultiGenProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 Δcka qepC maxForwardJumps l tStar authH la
    (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.init +
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.finish + 100000 ≤
        fig8AtomicStepBound q qepC ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.handle + 200000 ≤
        fig8AtomicStepBound q qepC) ∧
    (compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.finish + 400 ≤
        1400000 + 810 * bits (ratchetCostBudget q qepC)) ∧
    R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  intro L B0 R2
  let moHk : _root_.CryptoGames.SM.Construction.Mode := ⟨authH, some (l - 1), tStar⟩
  let mo : _root_.CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), tStar⟩
  let qC := fsMultiQueryC qepC qR B0
  let qS := fsMultiQueryS qepC qR B0
  have hΔle : Δcka ≤ 1 := by rcases haΔ with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  have hbΔ : ((!authH) = false ∧ 2 + Δcka = 3) ∨ ((!authH) = true ∧ 2 + Δcka = 2) := by
    rcases haΔ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hΔ23 : 2 + Δcka = 2 ∨ 2 + Δcka = 3 := by
    rcases haΔ with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> [exact Or.inr rfl; exact Or.inl rfl]
  have hΔ32 : 2 + Δcka = 3 ∨ 2 + Δcka = 2 := hΔ23.symm
  have hmfj : maxForwardJumps = 25000 := rfl
  have htLHk0 : moHk.tL.getD 0 ≤ qepC + 3 := by simp [moHk]; omega
  have htL0 : mo.tL.getD 0 ≤ qepC + 3 := by simp [mo]; omega
  have htHHk0 : moHk.tH ≤ qepC + 6 := by
    have := healEpoch_le_add3 htLHk0
    simp only [_root_.CryptoGames.SM.Construction.Mode.tH]; omega
  have htStarHk_b : bits moHk.tStar ≤ bits qepC + 3 :=
    (bits_mono (by simp [moHk]; exact htStar)).trans (bits_add_le_add qepC 3)
  have htHHk_b : bits moHk.tH ≤ bits qepC + 6 :=
    (bits_mono htHHk0).trans (bits_add_le_add qepC 6)
  have htL_b : bits (mo.tL.getD 0) ≤ bits qepC + 3 :=
    (bits_mono htL0).trans (bits_add_le_add qepC 3)
  have htStar_b : bits mo.tStar ≤ bits qepC + 3 :=
    (bits_mono (by simp [mo]; exact htStar)).trans (bits_add_le_add qepC 3)
  obtain ⟨hqCs, hqTr, hqCh, hqDl, hqIj⟩ := fsMultiQueryC_bounds_all qepC qR B0
  have hinit0 := initFSMultiEStateC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    (qC := qC) (qS := qS) B0 L moHk (Γ' := [.unit]) (.bool false)
  rcases hinit0 with ⟨hi0C, hi0E, hi0S⟩
  have hfin0 := finishFSMultiE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (2 + Δcka) mo.policy la hΔ23
    (Γ' := [mEsTy, .bool]) .v0
  rcases hfin0 with ⟨hf0C, hf0E, hf0S⟩
  have hhk := hooksFSMultiC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B0 L B0 Δcka moHk false la hΔle qC qS
  rcases hhk with ⟨hhkC, hhkE, hhkS⟩
  have hhkE' : HooksExcessBounded B0 ckaSampC qC
      (_root_.CryptoGames.SM.Construction.hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 Δcka moHk false la)
      (3350 * L + 6 * bits (qepC + 1) + 10 * B0 + 53000)
      (9000 * L + 18 * bits (qepC + 1) + 30 * B0 + 4820000)
      (14000 * L + 18 * bits (qepC + 1) + 50 * B0 + 3 * bits B0 + 9800000) :=
    hhkE.mono (by dsimp only [L, qC] at hqCs ⊢; omega)
      (by dsimp only [L, qC] at hqCs hqTr hqCh ⊢; omega)
      (by dsimp only [L, qC] at hqCs hqDl hqIj ⊢; omega)
  have hbB0_15 : bits B0 ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add15 (by dsimp only [B0]; rw [hmfj]; omega)
  have hbqep_15 : bits qepC ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbmfj_15 : bits maxForwardJumps ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbl_15 : bits l ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbt_15 : bits tStar ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbtSHk_15 : bits moHk.tStar ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by dsimp only [moHk]; omega)
  have hbtHHk_15 : bits moHk.tH ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbtS_15 : bits mo.tStar ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by dsimp only [mo]; omega)
  have hbtL_15 : bits (mo.tL.getD 0) ≤ bits (q + 1) + 15 := bits_le_bits_succ_add15 (by omega)
  have hbqSum_15 : bits (qepC + qR + B0 + 1) ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add15 (by dsimp only [B0]; rw [hmfj]; omega)
  have hpolL : mo.policy.tL = mo.tL := rfl
  have hpolS : mo.policy.tStar = mo.tStar := rfl
  rw [hpolL, hpolS] at hf0C hf0S
  simp only [Expr.cost, v0_cost, exprExcessUB_bool, exprExcessUB_v0,
    exprSizeW_bool, exprSizeW_v0] at hi0C hi0E hi0S hf0C hf0E hf0S
  have hiW : compCostW (ckaOpC B0) ckaSampC qC R2.init ≤
      1850 * L + 2 * bits moHk.tStar + 2 * bits moHk.tH + 8020 := by
    refine compCostW_le_of_parts
      (a := 1500 * L + 2 * bits moHk.tStar + 2 * bits moHk.tH + 4010)
      (b := 350 * L + 4010) ?_ ?_ (by omega)
    · dsimp only [R2, redFSAuthDFShiftedPaperMultiGenProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
        moHk] at hi0C ⊢
      simp only [Comp.cost, Expr.cost, v0_cost]
      omega
    · dsimp only [R2, redFSAuthDFShiftedPaperMultiGenProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
        moHk] at hi0E ⊢
      simp only [compExcessUB_bind, compExcessUB_ret,
        exprExcessUB_pair, exprExcessUB_unit, exprExcessUB_v0]
      omega
  have hfW : compCostW (ckaOpC B0) ckaSampC qC R2.finish ≤
      100 * L + 2 * bits (mo.tL.getD 0) + 2 * bits mo.tStar + 520 := by
    refine compCostW_le_of_parts
      (a := 100 * L + 2 * bits (mo.tL.getD 0) + 2 * bits mo.tStar + 510)
      (b := 10) ?_ ?_ (by omega)
    · dsimp only [R2, redFSAuthDFShiftedPaperMultiGenProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
        mo] at hf0C ⊢
      simp only [Comp.cost]
      omega
    · dsimp only [R2, redFSAuthDFShiftedPaperMultiGenProg,
        _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
        mo] at hf0E ⊢
      simp only [compExcessUB_ret]
      omega
  have hiS : compSizeW (ckaOpS B0) ckaSampS qS R2.init ≤
      65 * bits L + 6 * bits moHk.tStar + 6 * bits moHk.tH + 25020 := by
    dsimp only [R2, redFSAuthDFShiftedPaperMultiGenProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
      moHk] at hi0S ⊢
    simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit, exprSizeW_v0]
    omega
  have hfS : compSizeW (ckaOpS B0) ckaSampS qS R2.finish ≤
      12 * bits L + 6 * bits (mo.tL.getD 0) + 6 * bits mo.tStar + 520 := by
    dsimp only [R2, redFSAuthDFShiftedPaperMultiGenProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers,
      mo] at hf0S ⊢
    simp only [compSizeW_ret]
    omega
  have hhdS := DFProgSizeBounds.implECDFShiftedPaperGen_sizeW_le (!authH)
    (_root_.CryptoGames.SM.Construction.hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 Δcka moHk false la)
    (65 * bits L + 6 * bits moHk.tStar + 6 * bits moHk.tH + qS .cs + 24000)
    (qS .cs + qS .tr + qS .ch + 6000)
    (6 * bits B0 + 4 * bits B0 + 7 * bits L + qS .cs + qS .dl + qS .ij + 10500)
    L l (2 + Δcka) qepC maxForwardJumps tStar mo hΔ32 hhkS
    (Γ' := [mEsTy, _root_.CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [exprSizeW_v0, exprSizeW_v1] at hhdS
  have hhdS' : compSizeW (ckaOpS B0) ckaSampS qS R2.handle ≤
      9 * (65 * bits L + 6 * bits moHk.tStar + 6 * bits moHk.tH + qS .cs + 24000) +
      2 * (qS .cs + qS .tr + qS .ch + 6000) +
      3 * (6 * bits B0 + 4 * bits B0 + 7 * bits L + qS .cs + qS .dl + qS .ij + 10500) +
      100 * bits L + 80 * bits l + 25 * bits qepC + 10 * bits maxForwardJumps +
      20 * bits (mo.tL.getD 0) + 30 * bits mo.tStar + 6 * bits tStar + 46200 := by
    dsimp only [R2, redFSAuthDFShiftedPaperMultiGenProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
    exact hhdS.trans (by omega)
  clear hhdS
  dsimp only [qS] at hhdS'
  simp only [BundlesMultiFsBase.fsMultiQueryS_apply] at hhdS'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · refine (Nat.add_le_add (Nat.add_le_add hiW hfW) le_rfl).trans
      (le_fig8AtomicStepBound_parts q qepC B0 0 _ rfl (Nat.zero_le _) ?_)
    dsimp only [L] at hiW hfW ⊢
    omega
  · dsimp only [R2, redFSAuthDFShiftedPaperMultiGenProg,
      _root_.CryptoGames.PRFPRNG.prngSig, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.PRFPRNG.prngSamplers]
    exact implECDFShiftedPaperGen_multi_compCostW_le (!authH) _ q qepC l (2 + Δcka) moHk mo hbΔ
      (by simp [moHk]; exact htStar) htLHk0 (by simp [mo]; exact htStar) htL0 hl hhkC hhkE'
  · refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hiS hhdS') hfS) le_rfl).trans
      (le_size_bound_of_bR_priv fun bR h2bL_bR => ?_)
    dsimp only [L] at hiS hhdS' hfS ⊢
    omega
  · dsimp only [R2]
    exact (Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2.redFSAuthDFShiftedPaperMultiGenProg_totalQueries
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 Δcka qepC maxForwardJumps l tStar authH la q).trans (by omega)

end MultiFsHookBounds


private theorem bits_le_bits_succ_add_15 {x q : ℕ} (hx : x ≤ 32768 * (q + 1)) :
    bits x ≤ bits (q + 1) + 15 :=
  bits_le_bits_succ_add15 hx


section MultiFsBucketBounds

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "S_cka" => _root_.CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  _root_.CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM_fs" =>
  _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
local notation "mbHsTy" =>
  _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mVpTy" =>
  _root_.CryptoGames.SM.Construction.fsMultiDFVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbEsTy" =>
  _root_.CryptoGames.SM.Construction.fsMultiDFBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E


private theorem bind_ret_bucketInit_cost_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec} {σ : Ty S'}
    (c : Comp O' I' [.unit] σ) :
    (Comp.bind c (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))).cost ≤ c.cost + 8 := by
  simp only [Comp.cost, Expr.cost, v0_cost]; omega

private theorem bind_ret_bucketInit_excessUB_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec} {opC : O'.Op → ℕ}
    {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ} {σ : Ty S'}
    (c : Comp O' I' [.unit] σ) :
    compExcessUB opC sC qC (Comp.bind c (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))) ≤
      compExcessUB opC sC qC c := by
  simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit,
    exprExcessUB_v0, exprExcessUB_none, Nat.add_zero]; omega

private theorem bind_ret_bucketInit_sizeW_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec} {opS : O'.Op → ℕ}
    {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ} {σ : Ty S'}
    (c : Comp O' I' [.unit] σ) :
    compSizeW opS sS qS
      (Comp.bind c (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))) ≤
      compSizeW opS sS qS c + 10 := by
  simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit, exprSizeW_v0,
    exprSizeW_none]; omega

set_option linter.unusedSimpArgs false in
private theorem validGuessBucketParPaperE_bounds (B0 : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ'} (e : Expr OO_cka Γ' .nat) :
    (_root_.CryptoGames.SM.Construction.validGuessBucketParPaperE 4 tL par e).cost ≤
      3 * e.cost + (2 * bits (tL.getD 0) + 80) ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.validGuessBucketParPaperE 4 tL par e) ≤
      4 * exprExcessUB (ckaOpC B0) e ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.validGuessBucketParPaperE 4 tL par e) ≤
      4 * exprSizeW (ckaOpS B0) e + (4 * bits (tL.getD 0) + 150) := by
  have hb5 : bits 5 = 3 := rfl
  refine ⟨?_, ?_, ?_⟩
  · cases tL <;> cases par <;> ·
      simp only [_root_.CryptoGames.SM.Construction.validGuessBucketParPaperE, _root_.CryptoGames.SM.validGuessE,
        _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.optNatEqE, _root_.CryptoGames.SM.ltOptE,
        _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq,
        _root_.CryptoGames.SM.receiverOfE, _root_.CryptoGames.SM.senderOfE, _root_.CryptoGames.SM.Engine.optNatLit,
        Option.getD, Expr.cost, dsl_cost, v0_cost, v1_cost, bits_zero, bits_one, bits_two,
        bits_three, bits_four, hb5, Nat.reduceAdd]; omega
  · cases tL <;> cases par <;> ·
      simp only [_root_.CryptoGames.SM.Construction.validGuessBucketParPaperE, _root_.CryptoGames.SM.validGuessE,
        _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.optNatEqE, _root_.CryptoGames.SM.ltOptE,
        _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq,
        _root_.CryptoGames.SM.receiverOfE, _root_.CryptoGames.SM.senderOfE, optNatLit_excessUB,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat,
        exprExcessUB_add, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not,
        exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
        exprExcessUB_caseOpt, exprExcessUB_letE, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega
  · cases tL <;> cases par <;> ·
      simp only [_root_.CryptoGames.SM.Construction.validGuessBucketParPaperE, _root_.CryptoGames.SM.validGuessE,
        _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.optNatEqE, _root_.CryptoGames.SM.ltOptE,
        _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq,
        _root_.CryptoGames.SM.receiverOfE, _root_.CryptoGames.SM.senderOfE, _root_.CryptoGames.SM.Engine.optNatLit,
        Option.getD, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
        exprSizeW_none, exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
        exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some,
        exprSizeW_caseOpt, exprSizeW_letE, bits_zero, bits_one, bits_two, bits_three, bits_four,
        hb5, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
private theorem tableLookupB_bounds (B0 L : ℕ) {Γ'}
    (tblE : Expr OO_cka Γ' (.list (_root_.CryptoGames.SM.Construction.fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (ikE : Expr OO_cka Γ' (.base .i)) :
    (_root_.CryptoGames.SM.Construction.tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L tblE ikE).cost ≤ tblE.cost + ikE.cost + 30 * L + 20 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tblE ikE) ≤
      exprExcessUB (ckaOpC B0) tblE + exprExcessUB (ckaOpC B0) ikE + 10 * L ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tblE ikE) ≤
      exprSizeW (ckaOpS B0) tblE + exprSizeW (ckaOpS B0) ikE + bits L + 400 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.tableLookupE, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaOps, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.tableLookupE, _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var, exprExcessUB_none,
      exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_foldrB, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.tableLookupE, _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_none, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_letE, exprSizeW_op,
      exprSizeW_foldrB, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem lookupMultiDFBucketFC_bounds (B0 L : ℕ)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mbHsTy) (tE : Expr OO_cka Γ' .nat) (ikE : Expr OO_cka Γ' (.base .i)) :
    (_root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE tE ikE).cost ≤
      hE.cost + tE.cost + ikE.cost + 30 * L + 400 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE tE ikE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) tE +
        exprExcessUB (ckaOpC B0) ikE + 10 * L + 210 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE tE ikE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE +
        exprSizeW (ckaOpS B0) ikE + bits L + 800 := by
  let Γ0 : List (Ty S_cka) := .prod mbHsTy (.prod .nat (.base .i)) :: Γ'
  have htl := tableLookupB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0)
    (.tget (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl (.fst .v0)) (.fst (.snd .v0)))
    (.snd (.snd .v0))
  rcases htl with ⟨htlC, htlE, htlS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      Expr.cost, v0_cost, Nat.reduceAdd] at htlC
    simp only [_root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetTableAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      exprExcessUB_v0, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_tget, Nat.reduceAdd] at htlE
    simp only [_root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetTableAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      ckaSampC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_unit, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_cons, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_caseOpt, compExcessUB_sample, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      exprSizeW_v0, exprSizeW_fst, exprSizeW_snd, exprSizeW_tget, Nat.reduceAdd] at htlS
    simp only [_root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetTableAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      ckaSampS, exprSizeW_v0, exprSizeW_v1, exprSizeW_unit, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_cons, exprSizeW_tget, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_caseOpt, compSizeW_sample, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem regSessMultiDFBucketE_bounds (B0 L : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsTy) (tE : Expr OO_cka Γ' .nat) (ikE : Expr OO_cka Γ' (.base .i)) :
    (_root_.CryptoGames.SM.Construction.regSessMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L tL hE tE ikE).cost ≤
      hE.cost + tE.cost + ikE.cost + 120 * L + 2 * bits (healEpoch tL) + 600 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.regSessMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tL hE tE ikE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) tE +
        exprExcessUB (ckaOpC B0) ikE + 20 * L ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.regSessMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tL hE tE ikE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) ikE +
        6 * bits L + 2 * bits (healEpoch tL) + 800 := by
  have hbLm1 : bits (L - 1) ≤ bits L := _root_.ReductionDsl.bits_mono (Nat.sub_le L 1)
  have hbLs : bits L ≤ L + 1 := bits_le_succ L
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.regSessMultiDFBucketE,
      _root_.CryptoGames.SM.Construction.sessionsMemE,
      _root_.CryptoGames.SM.Construction.sessionsIdxOfE, _root_.CryptoGames.SM.Construction.sessionsLenE,
      _root_.CryptoGames.SM.Construction.sessionsAppendOneE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetSessionsAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.orE, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, v2_cost, bits_zero, bits_one,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  · simp only [_root_.CryptoGames.SM.Construction.regSessMultiDFBucketE,
      _root_.CryptoGames.SM.Construction.sessionsMemE, _root_.CryptoGames.SM.Construction.sessionsIdxOfE,
      _root_.CryptoGames.SM.Construction.sessionsLenE, _root_.CryptoGames.SM.Construction.sessionsAppendOneE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetSessionsAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.orE, _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var, exprExcessUB_bool,
      exprExcessUB_nat, exprExcessUB_nil, exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK,
      exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_cons,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_foldrB, exprExcessUB_tget,
      exprExcessUB_tset, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.regSessMultiDFBucketE,
      _root_.CryptoGames.SM.Construction.sessionsMemE, _root_.CryptoGames.SM.Construction.sessionsIdxOfE,
      _root_.CryptoGames.SM.Construction.sessionsLenE, _root_.CryptoGames.SM.Construction.sessionsAppendOneE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetSessionsAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.orE, _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_mulK, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_cons, exprSizeW_letE, exprSizeW_op,
      exprSizeW_foldrB, exprSizeW_tget, exprSizeW_tset, bits_zero, bits_one, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem regSessOptMultiDFBucketE_bounds (B0 L : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsTy) (tE : Expr OO_cka Γ' .nat)
    (sidE : Expr OO_cka Γ' (.opt (.base .i))) :
    (_root_.CryptoGames.SM.Construction.regSessOptMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L tL hE tE sidE).cost ≤
      hE.cost + tE.cost + sidE.cost + 240 * L + 4 * bits (healEpoch tL) + 1300 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.regSessOptMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tL hE tE sidE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) tE +
        exprExcessUB (ckaOpC B0) sidE + 40 * L ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.regSessOptMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tL hE tE sidE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) sidE +
        12 * bits L + 4 * bits (healEpoch tL) + 1700 := by
  let Γ0 : List (Ty S_cka) := .base .i :: .prod mbHsTy (.prod .nat (.opt (.base .i))) :: Γ'
  have hr := regSessMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ0) (.fst .v1) (.fst (.snd .v1)) .v0
  rcases hr with ⟨hrC, hrE, hrS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [Expr.cost, v0_cost, v1_cost, Nat.reduceAdd] at hrC
    simp only [_root_.CryptoGames.SM.Construction.regSessOptMultiDFBucketE,
      Expr.cost, v0_cost, v1_cost, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  · simp only [exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_fst, exprExcessUB_snd,
      Nat.reduceAdd] at hrE
    simp only [_root_.CryptoGames.SM.Construction.regSessOptMultiDFBucketE,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_none, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, Nat.reduceAdd]
    omega
  · simp only [exprSizeW_v0, exprSizeW_v1, exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at hrS
    simp only [_root_.CryptoGames.SM.Construction.regSessOptMultiDFBucketE,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_none, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem rootFSMultiDFBucketC_bounds (B0 L qep : ℕ) (tL : Option ℕ) (par : Bool)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mbHsTy) (tE : Expr OO_cka Γ' .nat)
    (ikE : Expr OO_cka Γ' (.base .i)) (σE : Expr OO_cka Γ' (.base .sig)) :
    (_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L 4 qep tL par hE tE ikE σE).cost ≤
      hE.cost + tE.cost + ikE.cost + σE.cost + 30 * L + bits (qep + 1) +
        3 * bits (healEpoch tL) + 2 * bits (tL.getD 0) + 650 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L 4 qep tL par hE tE ikE σE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) tE +
        exprExcessUB (ckaOpC B0) ikE + exprExcessUB (ckaOpC B0) σE + 20 * L + 2500 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L 4 qep tL par hE tE ikE σE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) ikE +
        exprSizeW (ckaOpS B0) σE + 2 * bits L + bits (qep + 1) +
        3 * bits (healEpoch tL) + 4 * bits (tL.getD 0) + 4500 := by
  let Γ0 : List (Ty S_cka) := .prod mbHsTy (.prod .nat (.prod (.base .i) (.base .sig))) :: Γ'
  have hvg := validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))
  have hlk := lookupMultiDFBucketFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (qC := qC) (qS := qS)
    B0 L (Γ' := Γ0) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
  rcases hvg with ⟨hvgC, hvgE, hvgS⟩
  rcases hlk with ⟨hlkC, hlkE, hlkS⟩
  have hvgEq : _root_.CryptoGames.SM.Construction.validGuessBucketParE (O' := OO_cka) 4 tL par
      (Γ' := Γ0) (.fst (.snd .v0)) =
      _root_.CryptoGames.SM.Construction.validGuessBucketParPaperE (O' := OO_cka) 4 tL par
      (Γ' := Γ0) (.fst (.snd .v0)) := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Expr.cost, v0_cost, Nat.reduceAdd] at hvgC hlkC
    simp only [_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketC, hvgEq,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  · simp only [exprExcessUB_v0, exprExcessUB_fst, exprExcessUB_snd, Nat.reduceAdd] at hvgE hlkE
    simp only [_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketC, hvgEq,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_unit,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_some, exprExcessUB_op, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite,
      compExcessUB_sample, Nat.reduceAdd]
    omega
  · simp only [exprSizeW_v0, exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at hvgS hlkS
    simp only [_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketC, hvgEq,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_op, compSizeW_ret, compSizeW_bind,
      compSizeW_ite, compSizeW_sample, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem fsTransFindB_bounds (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ' (.list (_root_.CryptoGames.SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (hcE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (_root_.CryptoGames.SM.Construction.fsTransFindE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L trE hcE).cost ≤ trE.cost + hcE.cost + 55 * L + 50 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.fsTransFindE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L trE hcE) ≤
      exprExcessUB (ckaOpC B0) trE + exprExcessUB (ckaOpC B0) hcE + 150 * L := by
  refine ⟨?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFindE, _root_.CryptoGames.SM.Engine.hdrCtEqE,
      _root_.CryptoGames.SM.Engine.optTEqE, _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFindE, _root_.CryptoGames.SM.Engine.hdrCtEqE,
      _root_.CryptoGames.SM.Engine.optTEqE, _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_eqN,
      exprExcessUB_and, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_findB, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem fsTransFilterB_bounds (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ' (.list (_root_.CryptoGames.SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (dropE : Expr OO_cka Γ' .nat) :
    (_root_.CryptoGames.SM.Construction.fsTransFilterE L trE dropE).cost ≤
      trE.cost + dropE.cost + 15 * L + 50 ∧
    exprExcessUB (ckaOpC B0) (_root_.CryptoGames.SM.Construction.fsTransFilterE L trE dropE) ≤
      exprExcessUB (ckaOpC B0) trE + exprExcessUB (ckaOpC B0) dropE ∧
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Construction.fsTransFilterE L trE dropE) ≤
      exprSizeW (ckaOpS B0) trE + exprSizeW (ckaOpS B0) dropE + bits L + 200 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFilterE, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFilterE, exprExcessUB_v0, exprExcessUB_v1,
      exprExcessUB_v2, exprExcessUB_var, exprExcessUB_nil, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_cons, exprExcessUB_letE, exprExcessUB_foldrB, Nat.add_zero, Nat.mul_zero,
      Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsTransFilterE, exprSizeW_v0, exprSizeW_v1,
      exprSizeW_v2, exprSizeW_var, exprSizeW_nil, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
      exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_cons, exprSizeW_letE,
      exprSizeW_foldrB, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem revealVRB_bounds (B0 L : ℕ) {Γ'}
    (vRE : Expr OO_cka Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO_cka Γ' (.list .nat)) :
    (_root_.CryptoGames.SM.Construction.anyExtMultiDFVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L vRE rngE).cost ≤ vRE.cost + rngE.cost + 100 * L + 50 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.anyExtMultiDFVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprExcessUB (ckaOpC B0) vRE + exprExcessUB (ckaOpC B0) rngE ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.anyExtMultiDFVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprSizeW (ckaOpS B0) vRE + exprSizeW (ckaOpS B0) rngE + bits L + 100 ∧
    (_root_.CryptoGames.SM.Construction.unliftMultiDFVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L vRE rngE).cost ≤ vRE.cost + rngE.cost + 250 * L + 50 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.unliftMultiDFVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprExcessUB (ckaOpC B0) vRE + exprExcessUB (ckaOpC B0) rngE ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.unliftMultiDFVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprSizeW (ckaOpS B0) vRE + exprSizeW (ckaOpS B0) rngE + bits L + 100 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.anyExtMultiDFVRE,
      _root_.CryptoGames.SM.Construction.isExtMultiDFEntryE, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]; omega
  · simp only [_root_.CryptoGames.SM.Construction.anyExtMultiDFVRE,
      _root_.CryptoGames.SM.Construction.isExtMultiDFEntryE, exprExcessUB_v0, exprExcessUB_v1,
      exprExcessUB_v2, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_ite, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_caseSum,
      exprExcessUB_letE, exprExcessUB_foldrB, exprExcessUB_tget, Nat.reduceAdd]; omega
  · simp only [_root_.CryptoGames.SM.Construction.anyExtMultiDFVRE,
      _root_.CryptoGames.SM.Construction.isExtMultiDFEntryE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
      exprSizeW_var, exprSizeW_bool, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_foldrB, exprSizeW_tget,
      Nat.reduceAdd]; omega
  · simp only [_root_.CryptoGames.SM.Construction.unliftMultiDFVRE,
      _root_.CryptoGames.SM.Construction.unliftMultiDFEntryE, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]; omega
  · simp only [_root_.CryptoGames.SM.Construction.unliftMultiDFVRE,
      _root_.CryptoGames.SM.Construction.unliftMultiDFEntryE, exprExcessUB_v0, exprExcessUB_v1,
      exprExcessUB_v2, exprExcessUB_var, exprExcessUB_none, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum,
      exprExcessUB_letE, exprExcessUB_foldrB, exprExcessUB_tconst, exprExcessUB_tget,
      exprExcessUB_tset, Nat.reduceAdd]; omega
  · simp only [_root_.CryptoGames.SM.Construction.unliftMultiDFVRE,
      _root_.CryptoGames.SM.Construction.unliftMultiDFEntryE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2,
      exprSizeW_var, exprSizeW_none, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_foldrB, exprSizeW_tconst,
      exprSizeW_tget, exprSizeW_tset, Nat.reduceAdd]; omega

private theorem bits_add_le_bits_add (n : ℕ) : ∀ k : ℕ, bits (n + k) ≤ bits n + k
  | 0 => by simp
  | k + 1 => by
    rw [← Nat.add_assoc n k 1]
    have h1 := bits_succ_le (n + k)
    have h2 := bits_add_le_bits_add n k
    omega

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem hooksFSMultiDFBucketC_costBounded (L B0 qep : ℕ) (tL : Option ℕ) (par la : Bool) :
    HooksCostBounded
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep tL par la)
      (2500 * L + 4 * bits (qep + 1) + 35 * bits (healEpoch tL) +
        10 * bits (tL.getD 0) + (B0 + 1) + 15000) where
  startSend_le {Γ'} hE ctxE pE tE γE σE rE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.opt (.base .ccoins))))) :: Γ'
    let Γ1 : List (Ty S_cka) := .base .ccoins :: Γ0
    let Γ2 : List (Ty S_cka) :=
      .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy :: Γ1
    have hrt := (rootFSMultiDFBucketC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fun _ => 0) (qS := fun _ => 0) B0 L qep tL par (Γ' := Γ1)
      (.fst .v1) (.fst (.snd .v1))
      (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1))))).1
    have hrg := (regSessOptMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ2)
      (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0)))).1
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, v2_cost, Nat.reduceAdd] at hrt hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  startRecv_le {Γ'} hE ctxE pE tE γE σE tnE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) mbHsTy :: Γ0
    have hvg := (validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))).1
    have hlk := (lookupMultiDFBucketFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fun _ => 0) (qS := fun _ => 0) B0 L (Γ' := Γ0)
      (.fst .v0) (.fst (.snd .v0))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))).1
    have hrg := (regSessMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ1)
      (.snd .v0) (.fst (.snd .v1))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))).1
    have hvgEq : _root_.CryptoGames.SM.Construction.validGuessBucketParE (O' := OO_cka) 4 tL par
        (Γ' := Γ0) (.fst (.snd .v0)) =
        _root_.CryptoGames.SM.Construction.validGuessBucketParPaperE (O' := OO_cka) 4 tL par
        (Γ' := Γ0) (.fst (.snd .v0)) := rfl
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, Nat.reduceAdd] at hvg hlk hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartRecvC, hvgEq,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  fsSend_le {Γ'} hE ctxE pE tE ssvE hdrE mE pairE := by
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cGsLeaks,
      _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
      bits_zero, bits_one, bits_three, dsl_cost, Nat.reduceAdd]
    omega
  fsRecv_le {Γ'} hE ctxE pE tE rsvE hdrE eE recE := by
    have hbB := bits_le_succ B0
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Construction.fsTransFindE, _root_.CryptoGames.SM.Construction.fsTransFilterE,
      _root_.CryptoGames.SM.Engine.hdrCtEqE, _root_.CryptoGames.SM.Engine.optTEqE,
      _root_.CryptoGames.SM.Engine.cRecMsg,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
      bits_zero, dsl_cost, Nat.reduceAdd]
    omega
  commit_le {Γ'} hE ctxE pE oldE newE := by
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketCommitC, Comp.cost, Expr.cost, Nat.reduceAdd]
    omega
  reveal_le {Γ'} hE ctxE pE vpE := by
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Construction.rangeListC,
      _root_.CryptoGames.SM.Construction.anyExtMultiDFVRE,
      _root_.CryptoGames.SM.Construction.isExtMultiDFEntryE,
      _root_.CryptoGames.SM.Construction.unliftMultiDFVRE,
      _root_.CryptoGames.SM.Construction.unliftMultiDFEntryE,
      _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk,
      _root_.CryptoGames.SM.Engine.vpId, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
      _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
      _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
      bits_zero, bits_one, dsl_cost, Nat.reduceAdd]
    omega

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem hooksFSMultiDFBucketC_excessBounded (L B0 qep qR : ℕ) (tL : Option ℕ)
    (par la : Bool) :
    HooksExcessBounded B0 ckaSampC (fsMultiQueryC qep qR B0)
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep tL par la)
      (350 * L + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 + 55000)
      (4900000 + 18 * bits (qep + 1) + 4500 * qR + 30 * B0)
      (9800000 + 12 * bits (qep + 1) + 5000 * qR + 40 * B0 + 3 * bits B0 + 500 * L) where
  startSend_le {Γ'} hE ctxE pE tE γE σE rE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.opt (.base .ccoins))))) :: Γ'
    let Γ1 : List (Ty S_cka) := .base .ccoins :: Γ0
    let Γ2 : List (Ty S_cka) :=
      .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy :: Γ1
    have hrt := (rootFSMultiDFBucketC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fsMultiQueryC qep qR B0) (qS := fun _ => 0) B0 L qep tL par (Γ' := Γ1)
      (.fst .v1) (.fst (.snd .v1))
      (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1))))).2.1
    have hrg := (regSessOptMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ2)
      (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0)))).2.1
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_op, Nat.reduceAdd] at hrt hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_unit, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_op, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_caseOpt, compExcessUB_sample, Nat.reduceAdd]
    omega
  startRecv_le {Γ'} hE ctxE pE tE γE σE tnE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) mbHsTy :: Γ0
    have hvg := (validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))).2.1
    have hlk := (lookupMultiDFBucketFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fsMultiQueryC qep qR B0) (qS := fun _ => 0) B0 L (Γ' := Γ0)
      (.fst .v0) (.fst (.snd .v0))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))).2.1
    have hrg := (regSessMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ1)
      (.snd .v0) (.fst (.snd .v1))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))).2.1
    have hvgEq : _root_.CryptoGames.SM.Construction.validGuessBucketParE (O' := OO_cka) 4 tL par
        (Γ' := Γ0) (.fst (.snd .v0)) =
        _root_.CryptoGames.SM.Construction.validGuessBucketParPaperE (O' := OO_cka) 4 tL par
        (Γ' := Γ0) (.fst (.snd .v0)) := rfl
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_op, Nat.reduceAdd] at hvg hlk hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartRecvC, hvgEq,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_op, exprExcessUB_tget,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.reduceAdd]
    omega
  fsSend_le {Γ'} hE ctxE pE tE ssvE hdrE mE pairE := by
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cGsLeaks,
      _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      BundlesMultiFsBase.fsMultiQueryC_cs, BundlesMultiFsBase.fsMultiQueryC_tr,
      BundlesMultiFsBase.fsMultiQueryC_ch,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
      exprExcessUB_nil, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_not, exprExcessUB_and,
      exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
      exprExcessUB_inr, exprExcessUB_some, exprExcessUB_cons, exprExcessUB_caseOpt,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
    omega
  fsRecv_le {Γ'} hE ctxE pE tE rsvE hdrE eE recE := by
    let mBookTy := _root_.CryptoGames.SM.Construction.fsMultiDFSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
    let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod (.sum (.base .rs) .nat)
        (.prod (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E)
          (.prod (.base .ct) (.opt _root_.CryptoGames.SM.Engine.cRecTy)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .nat :: Γ0
    let Γ2 : List (Ty S_cka) :=
      .prod .nat (.opt (.base .msg)) :: .sum .unit (.prod .nat (.opt (.base .msg))) ::
        .opt (.sum .unit (.prod .nat (.opt (.base .msg)))) :: Γ1
    have htf1 := (fsTransFindB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v1) .v0)))
      (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))).2
    have htf2 := (fsTransFindB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v4) .v3)))
      (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4)))))).2
    have hfl2 := (fsTransFilterB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v4) .v3)))
      (.caseOpt
        (_root_.CryptoGames.SM.Construction.fsTransFindE L
          (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v4) .v3)))
          (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))))
        (.fst .v0) (.fst .v0))).2.1
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_nil, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_tget,
      Nat.reduceAdd] at htf1 htf2 hfl2
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      BundlesMultiFsBase.fsMultiQueryC_dl, BundlesMultiFsBase.fsMultiQueryC_ij,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
      exprExcessUB_lt, exprExcessUB_not, exprExcessUB_and, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_op, exprExcessUB_tget,
      exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite,
      compExcessUB_caseOpt, compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
    omega
  commit_le {Γ'} hE ctxE pE oldE newE := by
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketCommitC,
      compExcessUB_ret, exprExcessUB_pair, exprExcessUB_some, Nat.reduceAdd]
    omega
  reveal_le {Γ'} hE ctxE pE vpE := by
    let Γ0 : List (Ty S_cka) := .prod mbHsTy mVpTy :: Γ'
    let Γ1 : List (Ty S_cka) :=
      .list .nat :: .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) mbHsTy :: Γ0
    have hvr := revealVRB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
      (_root_.CryptoGames.SM.Engine.vpVR (.snd .v3)) .v0
    rcases hvr with ⟨_, haE, _, _, huE, _⟩
    simp only [_root_.CryptoGames.SM.Engine.vpVR, exprExcessUB_v0, exprExcessUB_v3,
      exprExcessUB_fst, exprExcessUB_snd, Nat.reduceAdd] at haE huE
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketRevealC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk,
      _root_.CryptoGames.SM.Engine.vpId, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
      _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
      _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
      BundlesMultiFsBase.fsMultiQueryC_cs, rangeListC_excessUB,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
      exprExcessUB_nil, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_tget,
      exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
    omega

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem hooksFSMultiDFBucketC_sizeBounded (L B0 qep qR : ℕ) (tL : Option ℕ)
    (par la : Bool) :
    HooksSizeBounded B0 ckaSampS (fsMultiQueryS qep qR B0)
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep tL par la)
      (86 * bits L + 31 * bits (healEpoch tL) + 8 * bits (tL.getD 0) +
        bits (qep + 1) + 16 * bits (qep + qR + B0 + 1) + 30000)
      (48 * bits (qep + qR + B0 + 1) + 40000)
      (4 * bits L + 5 * bits B0 + 32 * bits (qep + qR + B0 + 1) + 30000) where
  startSend_le {Γ'} hE ctxE pE tE γE σE rE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.opt (.base .ccoins))))) :: Γ'
    let Γ1 : List (Ty S_cka) := .base .ccoins :: Γ0
    let Γ2 : List (Ty S_cka) :=
      .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy :: Γ1
    have hrt := (rootFSMultiDFBucketC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fun _ => 0) (qS := fsMultiQueryS qep qR B0) B0 L qep tL par (Γ' := Γ1)
      (.fst .v1) (.fst (.snd .v1))
      (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1))))).2.2
    have hrg := (regSessOptMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ2)
      (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0)))).2.2
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_op, Nat.reduceAdd] at hrt hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_unit, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_caseOpt, compSizeW_sample, Nat.reduceAdd]
    omega
  startRecv_le {Γ'} hE ctxE pE tE γE σE tnE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) mbHsTy :: Γ0
    have hvg := (validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))).2.2
    have hlk := (lookupMultiDFBucketFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fun _ => 0) (qS := fsMultiQueryS qep qR B0) B0 L (Γ' := Γ0)
      (.fst .v0) (.fst (.snd .v0))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))).2.2
    have hrg := (regSessMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ1)
      (.snd .v0) (.fst (.snd .v1))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))).2.2
    have hvgEq : _root_.CryptoGames.SM.Construction.validGuessBucketParE (O' := OO_cka) 4 tL par
        (Γ' := Γ0) (.fst (.snd .v0)) =
        _root_.CryptoGames.SM.Construction.validGuessBucketParPaperE (O' := OO_cka) 4 tL par
        (Γ' := Γ0) (.fst (.snd .v0)) := rfl
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_op, Nat.reduceAdd] at hvg hlk hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartRecvC, hvgEq,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tget,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, Nat.reduceAdd]
    omega
  fsSend_le {Γ'} hE ctxE pE tE ssvE hdrE mE pairE := by
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cGsLeaks,
      _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, BundlesMultiFsBase.fsMultiQueryS_apply,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
      exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_nil, exprSizeW_add, exprSizeW_lt, exprSizeW_not, exprSizeW_and,
      exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl,
      exprSizeW_inr, exprSizeW_some, exprSizeW_cons, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tget, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
      compSizeW_caseSum, compSizeW_query, bits_zero, bits_one, bits_three, Nat.reduceAdd]
    omega
  fsRecv_le {Γ'} hE ctxE pE tE rsvE hdrE eE recE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod (.sum (.base .rs) .nat)
        (.prod (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E)
          (.prod (.base .ct) (.opt _root_.CryptoGames.SM.Engine.cRecTy)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .nat :: Γ0
    let Γ2 : List (Ty S_cka) :=
      .prod .nat (.opt (.base .msg)) :: .sum .unit (.prod .nat (.opt (.base .msg))) ::
        .opt (.sum .unit (.prod .nat (.opt (.base .msg)))) :: Γ1
    have htf1 := fsTransFindE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v1) .v0)))
      (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    have htf2 := fsTransFindE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v4) .v3)))
      (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4)))))
    have hfl2 := (fsTransFilterB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v4) .v3)))
      (.caseOpt
        (_root_.CryptoGames.SM.Construction.fsTransFindE L
          (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v4) .v3)))
          (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))))
        (.fst .v0) (.fst .v0))).2.2
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
      exprSizeW_bool, exprSizeW_nat, exprSizeW_nil, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_tget,
      bits_zero, Nat.reduceAdd] at htf1 htf2 hfl2
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      BundlesMultiFsBase.fsMultiQueryS_apply,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
      exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
      exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tget,
      exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite,
      compSizeW_caseOpt, compSizeW_caseSum, compSizeW_query, bits_zero, Nat.reduceAdd]
    omega
  commit_le {Γ'} hE ctxE pE oldE newE := by
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketCommitC,
      compSizeW_ret, exprSizeW_pair, exprSizeW_some, Nat.reduceAdd]
    omega
  reveal_le {Γ'} hE ctxE pE vpE := by
    let Γ0 : List (Ty S_cka) := .prod mbHsTy mVpTy :: Γ'
    let Γ1 : List (Ty S_cka) :=
      .list .nat :: .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) mbHsTy :: Γ0
    have hvr := revealVRB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
      (_root_.CryptoGames.SM.Engine.vpVR (.snd .v3)) .v0
    rcases hvr with ⟨_, _, haS, _, _, huS⟩
    simp only [_root_.CryptoGames.SM.Engine.vpVR, exprSizeW_v0, exprSizeW_v3, exprSizeW_var,
      exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at haS huS
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketRevealC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk,
      _root_.CryptoGames.SM.Engine.vpId, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
      _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
      _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
      BundlesMultiFsBase.fsMultiQueryS_apply, rangeListC_sizeW,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_nil, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_tget, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
      compSizeW_caseSum, compSizeW_query, bits_zero, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem corrAllowedChoiceE_bounds {vpT : Ty S_cka} (B0 : ℕ) (paper : Bool) (L : ℕ) {Γ'}
    (s0 : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) (p0 : Expr OO_cka Γ' .bool) :
    (DFProgBucketBounds.corrAllowedChoiceE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) paper L s0 p0).cost ≤
      s0.cost + p0.cost + 300 * L + 150 ∧
    exprExcessUB (ckaOpC B0)
      (DFProgBucketBounds.corrAllowedChoiceE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) paper L s0 p0) ≤
      2 * (exprExcessUB (ckaOpC B0) s0 + exprExcessUB (ckaOpC B0) p0) := by
  refine ⟨?_, ?_⟩
  · cases paper
    · exact DFProgBucketBounds.cCorrAllowedE_cost_le (O' := OO_cka) L s0 p0
    · exact DFProgBucketBounds.cCorrAllowedPaperE_cost_le (O' := OO_cka) L s0 p0
  · cases paper <;> ·
      simp only [DFProgBucketBounds.corrAllowedChoiceE, _root_.CryptoGames.SM.Engine.cCorrAllowedPaperE,
        _root_.CryptoGames.SM.Engine.cCorrAllowedE, _root_.CryptoGames.SM.Engine.cCompContainsE,
        _root_.CryptoGames.SM.Engine.cGsChall, _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsComp,
        _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.posSender,
        _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var, exprExcessUB_bool,
        exprExcessUB_nat, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
        exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_letE, exprExcessUB_anyB,
        exprExcessUB_tget, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
      omega

set_option linter.unusedSimpArgs false in
private theorem postLeakDFBucketE_bounds (B0 : ℕ) (tL : Option ℕ)
    {vpT : Ty S_cka} {Γ'} (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) :
    (_root_.CryptoGames.SM.Construction.postLeakDFBucketE (O' := OO_cka) tL ctxE).cost ≤
      ctxE.cost + 2 * bits (tL.getD 0) + 50 ∧
    exprExcessUB (ckaOpC B0)
      (_root_.CryptoGames.SM.Construction.postLeakDFBucketE (O' := OO_cka) tL ctxE) ≤
      exprExcessUB (ckaOpC B0) ctxE ∧
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.Construction.postLeakDFBucketE (O' := OO_cka) tL ctxE) ≤
      exprSizeW (ckaOpS B0) ctxE + 2 * bits (tL.getD 0) + 50 := by
  refine ⟨?_, ?_, ?_⟩
  · cases tL <;> ·
      simp only [_root_.CryptoGames.SM.Construction.postLeakDFBucketE, _root_.CryptoGames.SM.Engine.optNatLit,
        _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.ltOptE, Option.getD,
        Expr.cost, v0_cost, v1_cost, bits_zero, dsl_cost,
        Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
      omega
  · cases tL <;> ·
      simp only [_root_.CryptoGames.SM.Construction.postLeakDFBucketE, _root_.CryptoGames.SM.Engine.optNatLit,
        _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.ltOptE,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat,
        exprExcessUB_none, exprExcessUB_some, exprExcessUB_lt, exprExcessUB_not, exprExcessUB_and,
        exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
        exprExcessUB_caseOpt, exprExcessUB_letE, Nat.max_def, Nat.add_zero, Nat.zero_add,
        Nat.reduceAdd]
      omega
  · cases tL <;> ·
      simp only [_root_.CryptoGames.SM.Construction.postLeakDFBucketE, _root_.CryptoGames.SM.Engine.optNatLit,
        _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.ltOptE, Option.getD,
        exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
        exprSizeW_none, exprSizeW_some, exprSizeW_lt, exprSizeW_not, exprSizeW_and,
        exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
        exprSizeW_caseOpt, exprSizeW_letE, bits_zero, Nat.add_zero, Nat.zero_add, Nat.reduceAdd]
      omega

set_option linter.unusedSimpArgs false in
private theorem rootFSMultiDFBucketPaperC_bounds (B0 L qep : ℕ) (tL : Option ℕ) (par : Bool)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {Γ'}
    (hE : Expr OO_cka Γ' mbHsTy) (tE : Expr OO_cka Γ' .nat)
    (plE : Expr OO_cka Γ' .bool)
    (ikE : Expr OO_cka Γ' (.base .i)) (σE : Expr OO_cka Γ' (.base .sig)) :
    (_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketPaperC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L 4 qep tL par hE tE plE ikE σE).cost ≤
      hE.cost + tE.cost + plE.cost + ikE.cost + σE.cost + 30 * L + bits (qep + 1) +
        3 * bits (healEpoch tL) + 2 * bits (tL.getD 0) + 700 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L 4 qep tL par hE tE plE ikE σE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) tE +
        exprExcessUB (ckaOpC B0) plE + exprExcessUB (ckaOpC B0) ikE +
        exprExcessUB (ckaOpC B0) σE + 20 * L + 2500 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L 4 qep tL par hE tE plE ikE σE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) plE +
        exprSizeW (ckaOpS B0) ikE + exprSizeW (ckaOpS B0) σE + 2 * bits L + bits (qep + 1) +
        3 * bits (healEpoch tL) + 4 * bits (tL.getD 0) + 4600 := by
  let Γ0 : List (Ty S_cka) :=
    .prod mbHsTy (.prod .nat (.prod (.base .i) (.prod (.base .sig) .bool))) :: Γ'
  have hvg := validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))
  have hlk := lookupMultiDFBucketFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (qC := qC) (qS := qS)
    B0 L (Γ' := Γ0) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
  rcases hvg with ⟨hvgC, hvgE, hvgS⟩
  rcases hlk with ⟨hlkC, hlkE, hlkS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, Nat.reduceAdd] at hvgC hlkC
    simp only [_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketPaperC, _root_.CryptoGames.SM.orE,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  · simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_fst, exprExcessUB_snd, Nat.reduceAdd] at hvgE hlkE
    simp only [_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketPaperC, _root_.CryptoGames.SM.orE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_unit,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_some, exprExcessUB_op,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_sample, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at hvgS hlkS
    simp only [_root_.CryptoGames.SM.Construction.rootFSMultiDFBucketPaperC, _root_.CryptoGames.SM.orE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_op,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_sample, Nat.reduceAdd]
    omega

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem hooksFSMultiDFBucketPaperC_costBounded (L B0 qep : ℕ) (tL : Option ℕ)
    (par la : Bool) :
    HooksCostBounded
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep tL par la)
      (2500 * L + 4 * bits (qep + 1) + 35 * bits (healEpoch tL) +
        10 * bits (tL.getD 0) + (B0 + 1) + 15000) where
  startSend_le {Γ'} hE ctxE pE tE γE σE rE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ)
        (.prod (.base .sig) (.prod (.opt (.base .ccoins)) .bool)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .base .ccoins :: Γ0
    let Γ2 : List (Ty S_cka) :=
      .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy :: Γ1
    have hpl := (postLeakDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL ctxE).1
    have hrt := (rootFSMultiDFBucketPaperC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fun _ => 0) (qS := fun _ => 0) B0 L qep tL par (Γ' := Γ1)
      (.fst .v1) (.fst (.snd .v1)) (.snd (.snd (.snd (.snd (.snd .v1)))))
      (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1))))).1
    have hrg := (regSessOptMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ2)
      (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0)))).1
    simp only [_root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, v2_cost, Nat.reduceAdd] at hpl hrt hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  startRecv_le {Γ'} hE ctxE pE tE γE σE tnE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ)
        (.prod (.base .sig) (.prod (.base .t) .bool)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) mbHsTy :: Γ0
    have hpl := (postLeakDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL ctxE).1
    have hvg := (validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))).1
    have hlk := (lookupMultiDFBucketFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fun _ => 0) (qS := fun _ => 0) B0 L (Γ' := Γ0)
      (.fst .v0) (.fst (.snd .v0))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0))))))))).1
    have hrg := (regSessMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ1)
      (.snd .v0) (.fst (.snd .v1))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1))))))))).1
    simp only [_root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, Nat.reduceAdd] at hpl hvg hlk hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    split_ifs <;> omega
  fsSend_le {Γ'} hE ctxE pE tE ssvE hdrE mE pairE :=
    ((hooksFSMultiDFBucketC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL par la).fsSend_le
      hE ctxE pE tE ssvE hdrE mE pairE).trans (by omega)
  fsRecv_le {Γ'} hE ctxE pE tE rsvE hdrE eE recE := by
    have hbB := bits_le_succ B0
    dsimp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperFsRecvC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Construction.fsTransFindE, _root_.CryptoGames.SM.Construction.fsTransFilterE,
      _root_.CryptoGames.SM.Engine.hdrCtEqE, _root_.CryptoGames.SM.Engine.optTEqE,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
      bits_zero, bits_one, bits_two, bits_three, dsl_cost, Nat.reduceAdd]
    omega
  commit_le {Γ'} hE ctxE pE oldE newE :=
    ((hooksFSMultiDFBucketC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL par la).commit_le
      hE ctxE pE oldE newE).trans (by omega)
  reveal_le {Γ'} hE ctxE pE vpE :=
    ((hooksFSMultiDFBucketC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL par la).reveal_le
      hE ctxE pE vpE).trans (by omega)

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem hooksFSMultiDFBucketPaperC_excessBounded (L B0 qep qR : ℕ) (tL : Option ℕ)
    (par la : Bool) :
    HooksExcessBounded B0 ckaSampC (fsMultiQueryC qep qR B0)
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep tL par la)
      (350 * L + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 + 55000)
      (4900000 + 18 * bits (qep + 1) + 4500 * qR + 30 * B0)
      (9880000 + 18 * bits (qep + 1) + 6500 * qR + 50 * B0 + 3 * bits B0 + 700 * L) where
  startSend_le {Γ'} hE ctxE pE tE γE σE rE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ)
        (.prod (.base .sig) (.prod (.opt (.base .ccoins)) .bool)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .base .ccoins :: Γ0
    let Γ2 : List (Ty S_cka) :=
      .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy :: Γ1
    have hpl := (postLeakDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL ctxE).2.1
    have hrt := (rootFSMultiDFBucketPaperC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fsMultiQueryC qep qR B0) (qS := fun _ => 0) B0 L qep tL par (Γ' := Γ1)
      (.fst .v1) (.fst (.snd .v1)) (.snd (.snd (.snd (.snd (.snd .v1)))))
      (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1))))).2.1
    have hrg := (regSessOptMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ2)
      (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0)))).2.1
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_op, Nat.reduceAdd] at hpl hrt hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_unit, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_op, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_caseOpt, compExcessUB_sample, Nat.reduceAdd]
    omega
  startRecv_le {Γ'} hE ctxE pE tE γE σE tnE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ)
        (.prod (.base .sig) (.prod (.base .t) .bool)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) mbHsTy :: Γ0
    have hpl := (postLeakDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL ctxE).2.1
    have hvg := (validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))).2.1
    have hlk := (lookupMultiDFBucketFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fsMultiQueryC qep qR B0) (qS := fun _ => 0) B0 L (Γ' := Γ0)
      (.fst .v0) (.fst (.snd .v0))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0))))))))).2.1
    have hrg := (regSessMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ1)
      (.snd .v0) (.fst (.snd .v1))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1))))))))).2.1
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_op, Nat.reduceAdd] at hpl hvg hlk hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_op, exprExcessUB_tget,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.reduceAdd]
    omega
  fsSend_le {Γ'} hE ctxE pE tE ssvE hdrE mE pairE :=
    (hooksFSMultiDFBucketC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).fsSend_le
      hE ctxE pE tE ssvE hdrE mE pairE
  fsRecv_le {Γ'} hE ctxE pE tE rsvE hdrE eE recE := by
    let tupT : Ty S_cka :=
      .prod mbHsTy (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpTy) (.prod .nat
        (.prod (.sum (.base .rs) .nat)
          (.prod (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E)
            (.prod (.base .ct) (.opt _root_.CryptoGames.SM.Engine.cRecTy))))))
    let Γ0 : List (Ty S_cka) := tupT :: Γ'
    let Γ1 : List (Ty S_cka) := .nat :: Γ0
    let Γ_ok : List (Ty S_cka) := .prod .bool mbHsTy :: Γ1
    let Γ2 : List (Ty S_cka) :=
      .prod .nat (.opt (.base .msg)) :: .sum .unit (.prod .nat (.opt (.base .msg))) ::
        .opt (.sum .unit (.prod .nat (.opt (.base .msg)))) :: Γ_ok
    have htf1 := (fsTransFindB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v1) .v0)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))))).2
    have htfOk := (fsTransFindB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_ok)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v2) .v1)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v2))))) (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))).2
    have htf2 := (fsTransFindB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v5) .v4)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5)))))))).2
    have hfl2 := (fsTransFilterB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.snd .v3) .v4)))
      (.caseOpt
        (_root_.CryptoGames.SM.Construction.fsTransFindE L
          (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v5) .v4)))
          (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
        (.fst .v0) (.fst .v0))).2.1
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_nil, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_tget,
      Nat.reduceAdd] at htf1 htfOk htf2 hfl2
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      BundlesMultiFsBase.fsMultiQueryC_cs, BundlesMultiFsBase.fsMultiQueryC_dl,
      BundlesMultiFsBase.fsMultiQueryC_ij,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
      exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_not,
      exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE,
      exprExcessUB_op, exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_caseSum, compExcessUB_query, Nat.reduceAdd]
    omega
  commit_le {Γ'} hE ctxE pE oldE newE :=
    (hooksFSMultiDFBucketC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).commit_le
      hE ctxE pE oldE newE
  reveal_le {Γ'} hE ctxE pE vpE :=
    (hooksFSMultiDFBucketC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).reveal_le
      hE ctxE pE vpE

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem hooksFSMultiDFBucketPaperC_sizeBounded (L B0 qep qR : ℕ) (tL : Option ℕ)
    (par la : Bool) :
    HooksSizeBounded B0 ckaSampS (fsMultiQueryS qep qR B0)
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep tL par la)
      (86 * bits L + 31 * bits (healEpoch tL) + 8 * bits (tL.getD 0) +
        bits (qep + 1) + 16 * bits (qep + qR + B0 + 1) + 30000)
      (48 * bits (qep + qR + B0 + 1) + 40000)
      (8 * bits L + 5 * bits B0 + 48 * bits (qep + qR + B0 + 1) + 45000) where
  startSend_le {Γ'} hE ctxE pE tE γE σE rE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ)
        (.prod (.base .sig) (.prod (.opt (.base .ccoins)) .bool)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .base .ccoins :: Γ0
    let Γ2 : List (Ty S_cka) :=
      .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy :: Γ1
    have hpl := (postLeakDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL ctxE).2.2
    have hrt := (rootFSMultiDFBucketPaperC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fun _ => 0) (qS := fsMultiQueryS qep qR B0) B0 L qep tL par (Γ' := Γ1)
      (.fst .v1) (.fst (.snd .v1)) (.snd (.snd (.snd (.snd (.snd .v1)))))
      (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1))))).2.2
    have hrg := (regSessOptMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ2)
      (.snd .v0) (.fst (.snd .v2)) (.snd (.snd (.fst .v0)))).2.2
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_op, Nat.reduceAdd] at hpl hrt hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_unit, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_caseOpt, compSizeW_sample, Nat.reduceAdd]
    omega
  startRecv_le {Γ'} hE ctxE pE tE γE σE tnE := by
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ)
        (.prod (.base .sig) (.prod (.base .t) .bool)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) mbHsTy :: Γ0
    have hpl := (postLeakDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL ctxE).2.2
    have hvg := (validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))).2.2
    have hlk := (lookupMultiDFBucketFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fun _ => 0) (qS := fsMultiQueryS qep qR B0) B0 L (Γ' := Γ0)
      (.fst .v0) (.fst (.snd .v0))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0))))))))).2.2
    have hrg := (regSessMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ1)
      (.snd .v0) (.fst (.snd .v1))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1))))))))).2.2
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_op, Nat.reduceAdd] at hpl hvg hlk hrg
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tget,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, Nat.reduceAdd]
    omega
  fsSend_le {Γ'} hE ctxE pE tE ssvE hdrE mE pairE :=
    ((hooksFSMultiDFBucketC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).fsSend_le
      hE ctxE pE tE ssvE hdrE mE pairE).trans (by omega)
  fsRecv_le {Γ'} hE ctxE pE tE rsvE hdrE eE recE := by
    let tupT : Ty S_cka :=
      .prod mbHsTy (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpTy) (.prod .nat
        (.prod (.sum (.base .rs) .nat)
          (.prod (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E)
            (.prod (.base .ct) (.opt _root_.CryptoGames.SM.Engine.cRecTy))))))
    let Γ0 : List (Ty S_cka) := tupT :: Γ'
    let Γ1 : List (Ty S_cka) := .nat :: Γ0
    let Γ_ok : List (Ty S_cka) := .prod .bool mbHsTy :: Γ1
    let Γ2 : List (Ty S_cka) :=
      .prod .nat (.opt (.base .msg)) :: .sum .unit (.prod .nat (.opt (.base .msg))) ::
        .opt (.sum .unit (.prod .nat (.opt (.base .msg)))) :: Γ_ok
    have htf1 := fsTransFindE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v1) .v0)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))))
    have htfOk := fsTransFindE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_ok)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v2) .v1)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v2))))) (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))
    have htf2 := fsTransFindE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v5) .v4)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5)))))))
    have hfl2 := (fsTransFilterB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ2)
      (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.snd .v3) .v4)))
      (.caseOpt
        (_root_.CryptoGames.SM.Construction.fsTransFindE L
          (.snd (.snd (_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt (.fst .v5) .v4)))
          (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
        (.fst .v0) (.fst .v0))).2.2
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
      exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_nil, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_tget,
      bits_zero, Nat.reduceAdd] at htf1 htfOk htf2 hfl2
    simp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetLfWin,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.cRecMsg, _root_.CryptoGames.SM.Engine.cGsTL,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      BundlesMultiFsBase.fsMultiQueryS_apply,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
      exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
      exprSizeW_add, exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
      exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_tget, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
      compSizeW_query, bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
    omega
  commit_le {Γ'} hE ctxE pE oldE newE :=
    ((hooksFSMultiDFBucketC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).commit_le
      hE ctxE pE oldE newE).trans (by omega)
  reveal_le {Γ'} hE ctxE pE vpE :=
    ((hooksFSMultiDFBucketC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).reveal_le
      hE ctxE pE vpE).trans (by omega)

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem initFSMultiDFBucketEStateC_bounds (B0 L qep : ℕ) (tL : Option ℕ) (par : Bool)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} :
    (_root_.CryptoGames.SM.Construction.initFSMultiDFBucketEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L 4 qep tL par (Γ' := [.unit]) (.bool false)).cost ≤
      2000 * L + bits (qep + 1) + 25 * bits (healEpoch tL) + 2 * bits (tL.getD 0) + 12000 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.initFSMultiDFBucketEStateC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 4 qep tL par (Γ' := [.unit]) (.bool false)) ≤
      300 * L + 6000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.initFSMultiDFBucketEStateC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 4 qep tL par (Γ' := [.unit]) (.bool false)) ≤
      70 * bits L + bits (qep + 1) + 25 * bits (healEpoch tL) + 4 * bits (tL.getD 0) + 20000 := by
  let Γ3 : List (Ty S_cka) := .base .kc :: .base .kr :: .bool :: [.unit]
  let Γ4 : List (Ty S_cka) :=
    .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy :: Γ3
  have hrt := rootFSMultiDFBucketC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    (qC := qC) (qS := qS) B0 L qep tL par (Γ' := Γ3)
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE (.nat 0)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.lamI .unit)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.prngInit .v1)
  have hrg := regSessOptMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ4)
    (.snd .v0) (.nat 0) (.snd (.snd (.fst .v0)))
  rcases hrt with ⟨hrtC, hrtE, hrtS⟩
  rcases hrg with ⟨hrgC, hrgE, hrgS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, bits_zero, Nat.reduceAdd] at hrtC hrgC
    simp only [_root_.CryptoGames.SM.Construction.initFSMultiDFBucketEStateC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Engine.mkPartiesE, _root_.CryptoGames.SM.Engine.vpMk,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk,
      _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, bits_zero,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_unit, exprExcessUB_bool,
      exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_op, exprExcessUB_tconst, Nat.reduceAdd] at hrtE hrgE
    simp only [_root_.CryptoGames.SM.Construction.initFSMultiDFBucketEStateC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Engine.mkPartiesE, _root_.CryptoGames.SM.Engine.vpMk,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk,
      _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
      exprExcessUB_nil, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tconst, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_sample,
      Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_unit, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_op, exprSizeW_tconst, bits_zero, Nat.reduceAdd] at hrtS hrgS
    simp only [_root_.CryptoGames.SM.Construction.initFSMultiDFBucketEStateC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Engine.mkPartiesE, _root_.CryptoGames.SM.Engine.vpMk,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk,
      _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_nil, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tconst, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_sample,
      bits_zero, Nat.reduceAdd]
    omega

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem initFSMultiDFBucketPaperEStateC_bounds (B0 L qep : ℕ) (tL : Option ℕ) (par : Bool)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} :
    (_root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L 4 qep tL par (Γ' := [.unit]) (.bool false)).cost ≤
      2000 * L + bits (qep + 1) + 25 * bits (healEpoch tL) + 2 * bits (tL.getD 0) + 12000 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC
      (_root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 4 qep tL par (Γ' := [.unit]) (.bool false)) ≤
      300 * L + 6000 ∧
    compSizeW (ckaOpS B0) ckaSampS qS
      (_root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 4 qep tL par (Γ' := [.unit]) (.bool false)) ≤
      70 * bits L + bits (qep + 1) + 25 * bits (healEpoch tL) + 4 * bits (tL.getD 0) + 20000 := by
  let Γ3 : List (Ty S_cka) := .base .kc :: .base .kr :: .bool :: [.unit]
  let Γ4 : List (Ty S_cka) :=
    .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy :: Γ3
  have hrt := rootFSMultiDFBucketPaperC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    (qC := qC) (qS := qS) B0 L qep tL par (Γ' := Γ3)
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE (.nat 0) (.bool false)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.lamI .unit)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.prngInit .v1)
  have hrg := regSessOptMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ4)
    (.snd .v0) (.nat 0) (.snd (.snd (.fst .v0)))
  rcases hrt with ⟨hrtC, hrtE, hrtS⟩
  rcases hrg with ⟨hrgC, hrgE, hrgS⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Expr.cost, v0_cost, v1_cost, bits_zero, Nat.reduceAdd] at hrtC hrgC
    simp only [_root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Engine.mkPartiesE, _root_.CryptoGames.SM.Engine.vpMk,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk,
      _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
      _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
      Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, bits_zero,
      Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_unit, exprExcessUB_bool,
      exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_op, exprExcessUB_tconst, Nat.reduceAdd] at hrtE hrgE
    simp only [_root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Engine.mkPartiesE, _root_.CryptoGames.SM.Engine.vpMk,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk,
      _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC, ckaSampC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
      exprExcessUB_nil, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tconst, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_sample,
      Nat.reduceAdd]
    omega
  · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_unit, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_op, exprSizeW_tconst, bits_zero, Nat.reduceAdd] at hrtS hrgS
    simp only [_root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsEmptyE,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
      _root_.CryptoGames.SM.Engine.mkPartiesE, _root_.CryptoGames.SM.Engine.vpMk,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk,
      _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdDFIface,
      _root_.CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS, ckaSampS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_nil, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tconst, exprSizeW_tset,
      compSizeW_ret, compSizeW_bind, compSizeW_sample,
      bits_zero, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
private theorem bucketMultiFinish_bounds (L B0 qep maxSkip : ℕ) (la : Bool)
    (tL : Option ℕ) (par : Bool)
    {qC : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} {qS : _root_.CryptoGames.PRFPRNG.FSHdrTag → ℕ} :
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketProgGen
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qep maxSkip la tL par
    R.finish.cost ≤ 240 * L + 2 * bits (tL.getD 0) + 400 ∧
    compExcessUB (ckaOpC B0) ckaSampC qC R.finish ≤ 30 ∧
    compSizeW (ckaOpS B0) ckaSampS qS R.finish ≤ 10 * bits L + 4 * bits (tL.getD 0) + 700 := by
  let Γf : List (Ty S_cka) := .nat :: .prod mbEsTy (.opt .nat) :: [.prod mbEsTy (.opt .nat), .bool]
  have hAuth := DFProgBucketBounds.cAuthOKE_any_cost_le (O' := OO_cka) (vpT := mVpTy) L 3 (by omega)
    (Γ' := Γf) (_root_.CryptoGames.SM.Engine.optNatLit tL) .v0
    (_root_.CryptoGames.SM.Engine.esG (hsT := mbHsTy) (.fst .v1))
  have hOpt : (_root_.CryptoGames.SM.Engine.optNatLit (O' := OO_cka) (Γ' := Γf) tL).cost ≤
      bits (tL.getD 0) + 2 := by
    cases tL <;> simp only [_root_.CryptoGames.SM.Engine.optNatLit, Option.getD, Expr.cost, bits_zero] <;> omega
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketProgGen]
    rw [show (2 : ℕ) + 1 = 3 from rfl]
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      esG_cost, esH_cost, esAbort_cost, _root_.CryptoGames.SM.Engine.cGsWin,
      Comp.cost, Expr.cost, dsl_cost, v0_cost, v1_cost, Nat.reduceAdd] at hAuth ⊢
    omega
  · dsimp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketProgGen]
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
      _root_.CryptoGames.SM.Engine.cAuthOKE, _root_.CryptoGames.SM.Engine.cCanonE,
      _root_.CryptoGames.SM.validGuessE, _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.optNatEqE,
      _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq,
      _root_.CryptoGames.SM.receiverOfE, _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsWin,
      _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.cGsLeaks,
      _root_.CryptoGames.SM.Engine.cGsCorrs, optNatLit_excessUB,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add, exprExcessUB_modK,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_foldrB, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
    omega
  · dsimp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketProgGen]
    rw [show (2 : ℕ) + 1 = 3 from rfl]
    cases tL <;> ·
      simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
        _root_.CryptoGames.SM.Engine.cAuthOKE, _root_.CryptoGames.SM.Engine.cCanonE,
        _root_.CryptoGames.SM.validGuessE, _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.optNatEqE,
        _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq,
        _root_.CryptoGames.SM.receiverOfE, Option.getD, _root_.CryptoGames.SM.Engine.optNatLit,
        _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsWin,
        _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.cGsLeaks,
        _root_.CryptoGames.SM.Engine.cGsCorrs,
        exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_bool,
        exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN,
        exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
        exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_anyB, exprSizeW_foldrB,
        compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
        bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
      omega

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem bucketHandleC_fsMulti_compCostW_le {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S_cka (unifSpec + TSpec)}
    {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (paper : Bool) (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (H Ho Hs Hr L Δ qep maxSkip C_inj : ℕ) (hΔ : Δ ≤ 4)
    (cfg : _root_.CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfgC : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), (cfg.injectFullE e).cost ≤ 3 * e.cost + C_inj)
    (hcfgE : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      exprExcessUB (ckaOpC B0) (cfg.injectFullE e) ≤ 4 * exprExcessUB (ckaOpC B0) e)
    (hhkC : HooksCostBounded hk H)
    (hhkE : HooksExcessBounded B0 sC qC hk Ho Hs Hr) :
    compCostW (ckaOpC B0) sC qC
      (DFProgBucketBounds.bucketHandleC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) paper hk L Δ qep maxSkip cfg) ≤
      3 * H + 2 * Ho + Hs + Hr + 6000 * L + 5 * bits qep + 2 * (maxSkip + 1) + C_inj + 45000 := by
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let psT := _root_.CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let ckaHdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let qT := (_root_.CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT
  let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0
  let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_cr2 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ_cr
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) :=
    dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) :=
    txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ ::
      .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  let Γ_tx2 : List (Ty S_cka) := .prod vpT ckaHdrCtT :: .prod (.opt (.prod vpT ckaHdrCtT)) hsT :: Γ_tx1
  let M := 3 * H + 2 * Ho + Hs + Hr + 6000 * L + 5 * bits qep + 2 * (maxSkip + 1) + C_inj + 44000
  have hep := DFProgBucketBounds.cEpMgmtE_any_cost_le (O' := OO_cka) (vpT := vpT) Δ qep hΔ (Γ' := Γ_tx0)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v6)) (.fst .v0) (_root_.CryptoGames.SM.isSomeE (.snd (.snd .v0)))
  have hvsC := DFProgBucketBounds.vSendC_any_cost_le hk H hhkC (Γ' := Γ_tx1)
    (_root_.CryptoGames.SM.Engine.esH (.fst .v7)) .v0 (.fst .v1)
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
    (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hvsE := vSendC_excessUB_le hk Ho Hs Hr hhkE (Γ' := Γ_tx1)
    (_root_.CryptoGames.SM.Engine.esH (.fst .v7)) .v0 (.fst .v1)
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
    (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hrec := DFProgBucketBounds.cRecordE_any_cost_le (O' := OO_cka) (vpT := vpT) L Δ hΔ (Γ' := Γ_tx2)
    .v2 (.fst .v3) (.fst .v0)
    (.pair (.pair (.fst .v3) (.pair (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
      (.add (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
      (.pair (.fst (.snd .v3)) (.snd .v0))) (.bool false)
  have hdlC := DFProgBucketBounds.deliverEC_any_cost_le hk H L maxSkip cfg hhkC (Γ' := Γ_dl) (.fst .v4) .v0
  have hdlE := DFProgBucketBounds.deliverEC_any_excessUB_le hk Ho Hs Hr L maxSkip cfg hhkE (Γ' := Γ_dl) (.fst .v4) .v0
  have hijC := DFProgBucketBounds.injectEC_anyCfg_cost_le hk H L Δ qep C_inj hΔ cfg hcfgC hhkC (Γ' := Γ_ij) (.fst .v3) .v0
  have hijE := DFProgBucketBounds.injectEC_anyCfg_excessUB_le hk Ho Hs Hr L Δ qep cfg hcfgE hhkE (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 paper L (Γ' := Γ_cr)
    (_root_.CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  rcases hca with ⟨hcaC, hcaE⟩
  have hac := DFProgBucketBounds.cAfterCorrE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ_cr2)
    (_root_.CryptoGames.SM.Engine.esG (hsT := hsT) (.fst .v4)) .v2
  have hrvC := hhkC.reveal_le (Γ' := Γ_cr) (_root_.CryptoGames.SM.Engine.esH (.fst .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hrvE := hhkE.reveal_le (Γ' := Γ_cr) (_root_.CryptoGames.SM.Engine.esH (.fst .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hdfC := DFProgBucketBounds.deliverForgeEC_anyCfg_cost_le hk H L Δ qep C_inj hΔ cfg hcfgC hhkC (Γ' := Γ_df) (.fst .v1) .v0
  have hdfE := DFProgBucketBounds.deliverForgeEC_anyCfg_excessUB_le hk Ho Hs Hr L Δ qep cfg hcfgE hhkE (Γ' := Γ_df) (.fst .v1) .v0
  simp only [esG_cost, esH_cost, pGet_cost, cGsSt_cost, cGsEpoch_cost, _root_.CryptoGames.SM.Engine.cGsIdx,
    isSomeE_cost, Expr.cost, dsl_cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v6_cost,
    Expr.v7, bits_one, Nat.reduceAdd] at hep hvsC hrec hdlC hijC hcaC hac hrvC hdfC
  simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.pGet, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
    exprExcessUB_v4, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_none, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hvsE hdlE hijE hcaE hrvE hdfE
  dsimp only [DFProgBucketBounds.bucketHandleC]
  refine (compCostW_bind_ret_le _ _ (ce := 10) (ck := M + 50) ?_ ?_).trans (by dsimp only [M]; omega)
  · simp [exprCostW, Expr.v0, Expr.v1]
  refine (compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 40) ?_ ?_ ?_).trans (by omega)
  · simp [exprCostW, Expr.v0, Expr.v1]
  · refine (compCostW_caseSum_le _ _ _ (cs := 2) (m := M + 30) ?_ ?_ ?_).trans (by omega)
    · simp [exprCostW, Expr.v0]
    · refine (compCostW_caseSum_le _ _ _ (cs := 2) (m := M + 20) ?_ ?_ ?_).trans (by omega)
      · simp [exprCostW, Expr.v0]
      · refine (compCostW_caseSum_le _ _ _ (cs := 2) (m := M + 10) ?_ ?_ ?_).trans (by omega)
        · simp [exprCostW, Expr.v0]
        · refine (compCostW_caseSum_le _ _ _ (cs := 2) (m := M) ?_ ?_ ?_).trans (by omega)
          · simp [exprCostW, Expr.v0]
          · refine compCostW_le_of_parts
                (a := 2 * H + 800 * L + 5 * bits qep + 3000) (b := Ho + Hs + 100) ?_ ?_
                (by dsimp only [M]; omega)
            · simp only [_root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.Engine.cGsIdx,
                _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.esMk,
                esG_cost, esH_cost, esAbort_cost, Comp.cost, Expr.cost, dsl_cost,
                v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, v6_cost, Expr.v7,
                bits_zero, bits_one, Nat.reduceAdd]
              omega
            · simp only [_root_.CryptoGames.SM.Engine.cEpMgmtE, _root_.CryptoGames.SM.Engine.cRecordE,
                _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cLeakE,
                _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
                _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
                _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSt,
                _root_.CryptoGames.SM.Engine.cGsB, _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
                _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cGsTrans,
                _root_.CryptoGames.SM.Engine.cGsChall, _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
                _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cRecPos,
                _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN,
                _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.pSet, _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.orE,
                _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
                _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
                exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
                exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_unit,
                exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add,
                exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and,
                exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
                exprExcessUB_inr, exprExcessUB_some, exprExcessUB_cons, exprExcessUB_caseOpt, exprExcessUB_letE,
                exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset,
                compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
                Nat.add_zero, Nat.zero_add, Nat.mul_zero]
              omega
          · refine compCostW_le_of_parts (a := 50) (b := 0) ?_ ?_ (by dsimp only [M]; omega)
            · simp only [Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, Nat.reduceAdd]; omega
            · simp only [compExcessUB_ret, exprExcessUB_pair, exprExcessUB_inl, exprExcessUB_inr,
                exprExcessUB_none, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v5, Nat.add_zero]; omega
        · refine compCostW_le_of_parts
              (a := 3 * H + 800 * L + 2 * maxSkip + 5600)
              (b := 2 * Ho + Hr + 150 * L + 32100) ?_ ?_ (by dsimp only [M]; omega)
          · simp only [Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, Nat.reduceAdd]
            omega
          · simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_inl,
              exprExcessUB_inr, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v5, Nat.add_zero]
            omega
      · refine compCostW_le_of_parts
            (a := 3 * H + 800 * L + bits qep + C_inj + 4800)
            (b := 2 * Ho + Hr + 150 * L + 600) ?_ ?_ (by dsimp only [M]; omega)
        · simp only [_root_.CryptoGames.SM.Engine.cGsWin, esG_cost, Comp.cost, Expr.cost, dsl_cost,
            v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Nat.reduceAdd]
          omega
        · simp only [_root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.esG,
            compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_inl, exprExcessUB_inr,
            exprExcessUB_ite, exprExcessUB_and, exprExcessUB_not, exprExcessUB_some,
            exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v4, Nat.add_zero]
          omega
    · refine compCostW_le_of_parts
          (a := H + 5900 * L + 5000) (b := Ho + Hr + 1000) ?_ ?_ (by dsimp only [M]; omega)
      · simp only [_root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.esMk,
          esG_cost, esH_cost, esAbort_cost, Comp.cost, Expr.cost, dsl_cost,
          v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, bits_zero, bits_one, Nat.reduceAdd]
        omega
      · simp only [_root_.CryptoGames.SM.Engine.cAfterCorrE, _root_.CryptoGames.SM.Engine.cSafeChE,
          _root_.CryptoGames.SM.Engine.cLeakE, _root_.CryptoGames.SM.Engine.cCompInsertE,
          _root_.CryptoGames.SM.Engine.cCompSetE, _root_.CryptoGames.SM.Engine.esMk,
          _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.esAbort,
          _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
          _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
          _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
          _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
          _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
          _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
          _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.healedByE,
          _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN,
          _root_.CryptoGames.SM.pSet, _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.orE,
          _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
          _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
          exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
          exprExcessUB_v4, exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7,
          exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
          exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add, exprExcessUB_modK,
          exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and,
          exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
          exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_cons,
          exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_foldrB,
          exprExcessUB_tget, exprExcessUB_tset,
          compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
          compExcessUB_caseSum, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
        omega
  · refine compCostW_le_of_parts
        (a := 3 * H + 800 * L + bits qep + C_inj + 5300)
        (b := 2 * Ho + Hr + 300 * L + 1200) ?_ ?_ (by dsimp only [M]; omega)
    · simp only [_root_.CryptoGames.SM.Engine.cGsWin, esG_cost, Comp.cost, Expr.cost, dsl_cost,
        v0_cost, v1_cost, v2_cost, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.esG,
        compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_inr,
        exprExcessUB_ite, exprExcessUB_and, exprExcessUB_not, exprExcessUB_some,
        exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, Nat.add_zero]
      omega

private theorem le_fig8AtomicStepBound_linear_B0 (q qepC B0 X : ℕ)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (h : X ≤ 25000000 + 100000 * q + 200 * bits qepC + 120 * B0) :
    X ≤ fig8AtomicStepBound q qepC := by
  have h1 : 25000000 + 100000 * q + 200 * bits qepC + 120 * B0 ≤
      100000 * (q + 1) + (q + 1) * (3 * bits qepC + 60) + 120 * B0 + 200 * bits qepC + 25000000 := by
    have : 0 ≤ (q + 1) * (3 * bits qepC + 60) := Nat.zero_le _
    omega
  subst hB0
  exact h.trans h1

private theorem le_size_bound_of_bR {X q qepC : ℕ}
    (h : ∀ bR, 2 * bits (q + 1) + 25 ≤ bR → X ≤ 1400000 + 810 * bR) :
    X ≤ 1400000 + 810 * bits (ratchetCostBudget q qepC) :=
  h (bits (ratchetCostBudget q qepC)) (two_mul_bits_succ_add25_le_ratchet q qepC)

set_option linter.unusedSimpArgs false in
private theorem corrAllowedChoiceE_sizeW_le_priv {vpT : Ty S_cka} (B0 : ℕ) (paper : Bool) (L : ℕ) {Γ'}
    (s0 : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) (p0 : Expr OO_cka Γ' .bool) :
    exprSizeW (ckaOpS B0) (DFProgBucketBounds.corrAllowedChoiceE paper L s0 p0) ≤
      2 * (exprSizeW (ckaOpS B0) s0 + exprSizeW (ckaOpS B0) p0) +
        4 * bits L + 200 := by
  cases paper <;> ·
    simp only [DFProgBucketBounds.corrAllowedChoiceE, _root_.CryptoGames.SM.Engine.cCorrAllowedPaperE,
      _root_.CryptoGames.SM.Engine.cCorrAllowedE, _root_.CryptoGames.SM.Engine.cCompContainsE,
      _root_.CryptoGames.SM.Engine.cGsChall, _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsComp,
      _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.posSender,
      _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_letE, exprSizeW_anyB, exprSizeW_tget, bits_zero, bits_one, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
private theorem bucketHandleC_sizeW_le_tight {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (paper : Bool) (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L Δ qep maxSkip S_inj : ℕ) (hΔ : Δ ≤ 4) (cfg : _root_.CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      exprSizeW (ckaOpS B0) (cfg.injectFullE e) ≤
        4 * exprSizeW (ckaOpS B0) e + S_inj)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr) :
    compSizeW (ckaOpS B0) sS qS
      (DFProgBucketBounds.bucketHandleC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) paper hk L Δ qep maxSkip cfg) ≤
      8 * Ho + Hs + 3 * Hr + 60 * bits L + 20 * bits qep + 10 * bits maxSkip + 8 * S_inj + 40000 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  have hbΔ : bits Δ ≤ 4 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hb1Δ : bits (Δ + 1) ≤ 4 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hb2Δ : bits (2 + Δ) ≤ 4 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hqep1 := bits_succ_le qep
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let ckaHdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let qT := (_root_.CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT
  let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0
  let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) := dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) := txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  have hvs := Computational.Proofs.SessionCostedFig8.ProgSizeBounds.vSendC_sizeW_le hk Ho Hs Hr hhk
    (Γ' := Γ_tx1) (_root_.CryptoGames.SM.Engine.esH (.fst .v7)) .v0 (.fst .v1)
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
    (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hdl := DFProgBucketBounds.deliverEC_any_sizeW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    hk Ho Hs Hr L maxSkip cfg hhk (Γ' := Γ_dl) (.fst .v4) .v0
  have hij := DFProgBucketBounds.injectEC_anyCfg_sizeW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    hk Ho Hs Hr L Δ qep S_inj hΔ cfg hcfg hhk (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_sizeW_le_priv (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 paper L (Γ' := Γ_cr)
    (_root_.CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  have hrv := hhk.reveal_le (Γ' := Γ_cr) (_root_.CryptoGames.SM.Engine.esH (.fst .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hdf := DFProgBucketBounds.deliverForgeEC_anyCfg_sizeW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    hk Ho Hs Hr L Δ qep S_inj hΔ cfg hcfg hhk (Γ' := Γ_df) (.fst .v1) .v0
  simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.pGet, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v7, exprSizeW_var, exprSizeW_none, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_letE, Nat.reduceAdd] at hvs hdl hij hca hrv hdf
  dsimp only [DFProgBucketBounds.bucketHandleC]
  simp only [_root_.CryptoGames.SM.Engine.cEpMgmtE, _root_.CryptoGames.SM.Engine.cRecordE,
    _root_.CryptoGames.SM.Engine.cAfterCorrE, _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cLeakE,
    _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
    _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
    _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.Engine.cGsB, _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cGsTrans,
    _root_.CryptoGames.SM.Engine.cGsChall, _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cRecPos,
    _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.pSet, _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.orE,
    _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.otherE, _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt,
    exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_cons, exprSizeW_caseOpt,
    exprSizeW_caseSum, exprSizeW_letE, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget,
    exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
  omega

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFBucketMulti_all_bounds (paper : Bool)
    (q qepC qR : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool)
    (hqepC : qepC ≤ q + 11)
    (htL : ∀ x, tL = some x → x ≤ qepC + 3)
    (hqR : qR ≤ 2 * q + 2) :
    let L := q + 1
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R := cond paper
      (_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketProg (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxForwardJumps la tL par)
      (_root_.CryptoGames.SM.Construction.redFSAuthDFMultiBucketProg (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxForwardJumps la tL par)
    (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.init +
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.finish + 100000 ≤
        fig8AtomicStepBound q qepC ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.handle + 200000 ≤
        fig8AtomicStepBound q qepC) ∧
    (compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.finish + 400 ≤
        1400000 + 810 * bits (ratchetCostBudget q qepC)) ∧
    R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  dsimp only
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  have htL0 : tL.getD 0 ≤ qepC + 3 := by
    cases tL with
    | none => simp
    | some x => exact htL x rfl
  have hhe0 : healEpoch tL ≤ qepC + 5 := by
    cases tL with
    | none => simp [healEpoch]
    | some x => have hx := htL x rfl; simp only [healEpoch]; omega
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbq1 := bits_succ_le qepC
  have hbtL_qep : bits (tL.getD 0) ≤ bits qepC + 3 := by
    have h1 := ReductionDsl.bits_mono htL0
    have h2 := bits_add_le_bits_add qepC 3
    omega
  have hbhe_qep : bits (healEpoch tL) ≤ bits qepC + 5 := by
    have h1 := ReductionDsl.bits_mono hhe0
    have h2 := bits_add_le_bits_add qepC 5
    omega
  have hbB0_lin := bits_le_add_one B0
  let init0 := cond paper
    (_root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L 4 qepC tL par (Γ' := [.unit]) (.bool false))
    (_root_.CryptoGames.SM.Construction.initFSMultiDFBucketEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L 4 qepC tL par (Γ' := [.unit]) (.bool false))
  let hk := cond paper
    (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qepC tL par la)
    (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qepC tL par la)
  have hinit0 : init0.cost ≤
      2000 * L + bits (qepC + 1) + 25 * bits (healEpoch tL) + 2 * bits (tL.getD 0) + 12000 ∧
      compExcessUB (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) init0 ≤ 300 * L + 6000 ∧
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) init0 ≤
        70 * bits L + bits (qepC + 1) + 25 * bits (healEpoch tL) + 4 * bits (tL.getD 0) + 20000 := by
    cases paper
    · exact initFSMultiDFBucketEStateC_bounds (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        (qC := fsMultiQueryC qepC qR B0) (qS := fsMultiQueryS qepC qR B0)
        B0 L qepC tL par
    · exact initFSMultiDFBucketPaperEStateC_bounds (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        (qC := fsMultiQueryC qepC qR B0) (qS := fsMultiQueryS qepC qR B0)
        B0 L qepC tL par
  rcases hinit0 with ⟨hi0C, hi0E, hi0S⟩
  have hfin := bucketMultiFinish_bounds (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    (qC := fsMultiQueryC qepC qR B0) (qS := fsMultiQueryS qepC qR B0)
    L B0 qepC maxForwardJumps la tL par
  rcases hfin with ⟨hfC, hfE, hfS⟩
  have hhkC : HooksCostBounded hk
      (2500 * L + 4 * bits (qepC + 1) + 35 * bits (healEpoch tL) +
        10 * bits (tL.getD 0) + (B0 + 1) + 15000) := by
    cases paper
    · exact hooksFSMultiDFBucketC_costBounded (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 qepC tL par la
    · exact hooksFSMultiDFBucketPaperC_costBounded (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 qepC tL par la
  have hhkE : HooksExcessBounded B0 ckaSampC (fsMultiQueryC qepC qR B0) hk
      (350 * L + 6 * bits (qepC + 1) + 1500 * qR + 10 * B0 + 55000)
      (4900000 + 18 * bits (qepC + 1) + 4500 * qR + 30 * B0)
      (9880000 + 18 * bits (qepC + 1) + 6500 * qR + 50 * B0 + 3 * bits B0 + 700 * L) := by
    cases paper
    · exact (hooksFSMultiDFBucketC_excessBounded (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 qepC qR tL par la).mono
        (by omega) (by omega) (by omega)
    · exact hooksFSMultiDFBucketPaperC_excessBounded (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 qepC qR tL par la
  have hhkS : HooksSizeBounded B0 ckaSampS (fsMultiQueryS qepC qR B0) hk
      (86 * bits L + 31 * bits (healEpoch tL) + 8 * bits (tL.getD 0) +
        bits (qepC + 1) + 16 * bits (qepC + qR + B0 + 1) + 30000)
      (48 * bits (qepC + qR + B0 + 1) + 40000)
      (8 * bits L + 5 * bits B0 + 48 * bits (qepC + qR + B0 + 1) + 45000) := by
    cases paper
    · exact (hooksFSMultiDFBucketC_sizeBounded (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 qepC qR tL par la).mono
        (by omega) (by omega) (by omega)
    · exact hooksFSMultiDFBucketPaperC_sizeBounded (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 qepC qR tL par la
  have hvg := fun {Γ'} (e : Expr OO_cka Γ' .nat) =>
    validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ') e
  have hhdW := bucketHandleC_fsMulti_compCostW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (B0 := B0) (sC := ckaSampC) (qC := fsMultiQueryC qepC qR B0) paper hk
    (2500 * L + 4 * bits (qepC + 1) + 35 * bits (healEpoch tL) + 10 * bits (tL.getD 0) + (B0 + 1) + 15000)
    (350 * L + 6 * bits (qepC + 1) + 1500 * qR + 10 * B0 + 55000)
    (4900000 + 18 * bits (qepC + 1) + 4500 * qR + 30 * B0)
    (9880000 + 18 * bits (qepC + 1) + 6500 * qR + 50 * B0 + 3 * bits B0 + 700 * L)
    L 3 qepC maxForwardJumps (2 * bits (tL.getD 0) + 80) (by omega)
    (_root_.CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)
    (fun e => (hvg e).1) (fun e => (hvg e).2.1) hhkC hhkE
  have hhdS := bucketHandleC_sizeW_le_tight (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (B0 := B0) (sS := ckaSampS) (qS := fsMultiQueryS qepC qR B0) paper hk
    (86 * bits L + 31 * bits (healEpoch tL) + 8 * bits (tL.getD 0) +
      bits (qepC + 1) + 16 * bits (qepC + qR + B0 + 1) + 30000)
    (48 * bits (qepC + qR + B0 + 1) + 40000)
    (8 * bits L + 5 * bits B0 + 48 * bits (qepC + qR + B0 + 1) + 45000)
    L 3 qepC maxForwardJumps (4 * bits (tL.getD 0) + 150) (by omega)
    (_root_.CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)
    (fun e => (hvg e).2.2) hhkS
  let initComp := Comp.bind init0
    (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))
  have hiC := (bind_ret_bucketInit_cost_le _).trans (Nat.add_le_add_right hi0C 8)
  have hiE := (bind_ret_bucketInit_excessUB_le _).trans hi0E
  have hiS := (bind_ret_bucketInit_sizeW_le _).trans (Nat.add_le_add_right hi0S 10)
  have hiW := compCostW_le_cost_add_excessUB (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) initComp
  let Rfin := _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketProgGen
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxForwardJumps la tL par
  have hfW := compCostW_le_cost_add_excessUB (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) Rfin.finish
  have hbL : bits L = bits (q + 1) := rfl
  have hbL_lin := bits_le_add_one (q + 1)
  have hbB0_bL : bits B0 ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add_15 (by dsimp only [B0]; unfold maxForwardJumps; omega)
  have hbcomb_bL : bits (qepC + qR + B0 + 1) ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add_15 (by dsimp only [B0]; unfold maxForwardJumps; omega)
  have hbm_const : bits maxForwardJumps = 15 := rfl
  have hbqep1_bL : bits (qepC + 1) ≤ bits (q + 1) + 11 := by
    have h1 : qepC + 1 ≤ (q + 1) + 11 := by omega
    exact (ReductionDsl.bits_mono h1).trans (bits_add_le_bits_add (q + 1) 11)
  have hbtL_bL : bits (tL.getD 0) ≤ bits (q + 1) + 13 := by
    have h1 : tL.getD 0 ≤ (q + 1) + 13 := by omega
    exact (ReductionDsl.bits_mono h1).trans (bits_add_le_bits_add (q + 1) 13)
  have hbhe_bL : bits (healEpoch tL) ≤ bits (q + 1) + 16 := by
    have h1 : healEpoch tL ≤ (q + 1) + 16 := by
      have := healEpoch_le_add3 htL0
      omega
    exact (ReductionDsl.bits_mono h1).trans (bits_add_le_bits_add (q + 1) 16)
  have hbqep_bL : bits qepC ≤ bits (q + 1) + 11 := by
    have hle : bits qepC ≤ bits (qepC + 1) := ReductionDsl.bits_mono (by omega)
    omega
  have hiW' := hiW.trans (Nat.add_le_add hiC hiE)
  have hfW' := hfW.trans (Nat.add_le_add hfC hfE)
  have hifW : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) initComp +
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) Rfin.finish + 100000 ≤
      fig8AtomicStepBound q qepC := by
    refine (Nat.add_le_add (Nat.add_le_add hiW' hfW') (Nat.le_refl 100000)).trans ?_
    refine le_fig8AtomicStepBound_linear_B0 q qepC B0 _ rfl ?_
    omega
  have hhdW' : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0)
      (DFProgBucketBounds.bucketHandleC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        paper hk L 3 qepC maxForwardJumps
        (_root_.CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)) + 200000 ≤
      fig8AtomicStepBound q qepC := by
    refine (Nat.add_le_add hhdW (Nat.le_refl 200000)).trans ?_
    refine le_fig8AtomicStepBound_linear_B0 q qepC B0 _ rfl ?_
    omega
  have hS' : compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) initComp +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0)
        (DFProgBucketBounds.bucketHandleC (ckaInitA := ckaInitA)
          (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
          (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
          (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
          (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          paper hk L 3 qepC maxForwardJumps
          (_root_.CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)) +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) Rfin.finish + 400 ≤
      1400000 + 810 * bits (ratchetCostBudget q qepC) := by
    refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hiS hhdS) hfS) (Nat.le_refl 400)).trans ?_
    refine le_size_bound_of_bR fun bR h2bL_bR => ?_
    clear hifW hhdW' hiW' hfW' hiW hfW initComp Rfin hhkC hhkE hhkS hvg hhdW
    omega
  cases paper
  · dsimp only [cond, initComp, init0, hk] at hifW hhdW' hS' ⊢
    exact ⟨⟨hifW, hhdW'⟩, hS',
      (_root_.CryptoGames.SM.Construction.redFSAuthDFMultiBucketProg_totalQueries
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4
        qepC maxForwardJumps la tL par q).trans (Nat.mul_comm q 2).le⟩
  · dsimp only [cond, initComp, init0, hk] at hifW hhdW' hS' ⊢
    exact ⟨⟨hifW, hhdW'⟩, hS',
      (_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketProg_totalQueries
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4
        qepC maxForwardJumps la tL par q).trans (Nat.mul_comm q 2).le⟩

private theorem redFSAuthDFMultiBucketProg_bounds
    (q qepC qR : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool)
    (hqepC : qepC ≤ q + 11)
    (htL : ∀ x, tL = some x → x ≤ qepC + 3)
    (hqR : qR ≤ 2 * q + 2) :
    let L := q + 1
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFMultiBucketProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxForwardJumps la tL par
    (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.init +
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.finish + 100000 ≤
        fig8AtomicStepBound q qepC ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.handle + 200000 ≤
        fig8AtomicStepBound q qepC) ∧
    (compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.finish + 400 ≤
        1400000 + 810 * bits (ratchetCostBudget q qepC)) ∧
    R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q :=
  redFSAuthDFBucketMulti_all_bounds (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) false q qepC qR la tL par hqepC htL hqR



set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem fsMultiDFBucketRevealC_tight_sizeW_le (L B0 qep qR : ℕ) (la : Bool) {Γ'}
    (hE : Expr OO_cka Γ' mbHsTy)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool)
    (vpE : Expr OO_cka Γ' mVpTy) :
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (_root_.CryptoGames.SM.Construction.fsMultiDFBucketRevealC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L la hE ctxE pE vpE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE +
        exprSizeW (ckaOpS B0) pE + exprSizeW (ckaOpS B0) vpE) +
        10 * bits L + 16 * bits (qep + qR + B0 + 1) + 13000 := by
  let Γ0 : List (Ty S_cka) := .prod mbHsTy mVpTy :: Γ'
  let Γ1 : List (Ty S_cka) :=
    .list .nat :: .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) mbHsTy :: Γ0
  have hvr := revealVRB_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
    (_root_.CryptoGames.SM.Engine.vpVR (.snd .v3)) .v0
  rcases hvr with ⟨_, _, haS, _, _, huS⟩
  simp only [_root_.CryptoGames.SM.Engine.vpVR, exprSizeW_v0, exprSizeW_v3, exprSizeW_var,
    exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at haS huS
  simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketRevealC,
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsGetBookAt,
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSetBookAt,
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsMk,
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsTableTbl,
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsSessionsTbl,
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsBook,
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsLfWin,
    _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk,
    _root_.CryptoGames.SM.Engine.vpId, _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
    _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
    _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
    BundlesMultiFsBase.fsMultiQueryS_apply, rangeListC_sizeW,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
    exprSizeW_nil, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, compSizeW_query, bits_zero, Nat.reduceAdd]
  omega

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem fsMultiDFBucketModeRevealC_bounds (L B0 qep qR : ℕ) (gMain la : Bool)
    (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsTy)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool)
    (vpE : Expr OO_cka Γ' mVpTy) :
    (_root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L gMain la tL hE ctxE pE vpE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + vpE.cost) +
        (2500 * L + 4 * bits (qep + 1) + 37 * bits (healEpoch tL) +
          10 * bits (tL.getD 0) + (B0 + 1) + 15200) ∧
    compExcessUB (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (_root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L gMain la tL hE ctxE pE vpE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE +
        exprExcessUB (ckaOpC B0) pE + exprExcessUB (ckaOpC B0) vpE) +
        (350 * L + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 + 55200) ∧
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (_root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L gMain la tL hE ctxE pE vpE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE +
        exprSizeW (ckaOpS B0) pE + exprSizeW (ckaOpS B0) vpE) +
        (10 * bits L + 2 * bits (healEpoch tL) + 16 * bits (qep + qR + B0 + 1) + 13200) := by
  cases gMain with
  | true =>
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC, ↓reduceIte]
    have hC := (hooksFSMultiDFBucketC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL false la).reveal_le
      hE ctxE pE vpE
    have hEx := (hooksFSMultiDFBucketC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL false la).reveal_le
      hE ctxE pE vpE
    have hS := fsMultiDFBucketRevealC_tight_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR la hE ctxE pE vpE
    dsimp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC] at hC hEx
    exact ⟨hC.trans (by omega), hEx.trans (by omega), hS.trans (by omega)⟩
  | false =>
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpTy) (.prod .bool mVpTy)) :: Γ'
    have hC0 := (hooksFSMultiDFBucketC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL false la).reveal_le
      (Γ' := Γ0) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
    have hE0 := (hooksFSMultiDFBucketC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL false la).reveal_le
      (Γ' := Γ0) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
    have hS0 := fsMultiDFBucketRevealC_tight_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR la
      (Γ' := Γ0) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
    dsimp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC] at hC0 hE0
    simp only [Expr.cost, v0_cost, Nat.reduceAdd] at hC0
    simp only [exprExcessUB_v0, exprExcessUB_fst, exprExcessUB_snd, Nat.reduceAdd] at hE0
    simp only [exprSizeW_v0, exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at hS0
    refine ⟨?_, ?_, ?_⟩
    · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC,
        _root_.CryptoGames.SM.Construction.fsMultiDFBucketForgedHdrRevealC,
        _root_.CryptoGames.SM.Engine.vpTcurNat, cGsEpoch_cost, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
        Comp.cost, Expr.cost, v0_cost, dsl_cost,
        Bool.false_eq_true, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC,
        _root_.CryptoGames.SM.Construction.fsMultiDFBucketForgedHdrRevealC,
        _root_.CryptoGames.SM.Engine.vpTcurNat, _root_.CryptoGames.SM.Engine.cGsEpoch,
        _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
        exprExcessUB_v0, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
        exprExcessUB_lt, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair,
        exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_letE,
        compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC,
        _root_.CryptoGames.SM.Construction.fsMultiDFBucketForgedHdrRevealC,
        _root_.CryptoGames.SM.Engine.vpTcurNat, _root_.CryptoGames.SM.Engine.cGsEpoch,
        _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
        exprSizeW_v0, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
        exprSizeW_lt, exprSizeW_not, exprSizeW_ite, exprSizeW_pair,
        exprSizeW_fst, exprSizeW_snd, exprSizeW_letE,
        compSizeW_ret, compSizeW_bind, compSizeW_ite, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
      omega

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem fsMultiDFBucketPaperModeStartRecvC_bounds (L B0 qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO_cka Γ' mbHsTy)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
    (pE : Expr OO_cka Γ' .bool)
    (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ))
    (σE : Expr OO_cka Γ' (.base .sig))
    (tnE : Expr OO_cka Γ' (.base .t)) :
    (_root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperModeStartRecvC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L 4 qep gMain tL par hE ctxE pE tE γE σE tnE).cost ≤
      2 * (hE.cost + ctxE.cost + pE.cost + tE.cost + γE.cost + σE.cost + tnE.cost) +
        (2500 * L + 4 * bits (qep + 1) + 37 * bits (healEpoch tL) +
          10 * bits (tL.getD 0) + (B0 + 1) + 15200) ∧
    compExcessUB (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (_root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperModeStartRecvC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 4 qep gMain tL par hE ctxE pE tE γE σE tnE) ≤
      4 * (exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ctxE +
        exprExcessUB (ckaOpC B0) pE + exprExcessUB (ckaOpC B0) tE +
        exprExcessUB (ckaOpC B0) γE + exprExcessUB (ckaOpC B0) σE +
        exprExcessUB (ckaOpC B0) tnE) +
        (350 * L + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 + 55200) ∧
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (_root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperModeStartRecvC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 4 qep gMain tL par hE ctxE pE tE γE σE tnE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE +
        exprSizeW (ckaOpS B0) pE + exprSizeW (ckaOpS B0) tE +
        exprSizeW (ckaOpS B0) γE + exprSizeW (ckaOpS B0) σE +
        exprSizeW (ckaOpS B0) tnE) +
        (13 * bits L + 5 * bits (healEpoch tL) + 6 * bits (tL.getD 0) + bits (qep + 1) + 12000) := by
  cases gMain with
  | true =>
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ) (.base .t))) :: Γ'
    have hvg := validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))
    rcases hvg with ⟨hvgC, hvgE, hvgS⟩
    simp only [Expr.cost, v0_cost, Nat.reduceAdd] at hvgC
    simp only [exprExcessUB_v0, exprExcessUB_fst, exprExcessUB_snd, Nat.reduceAdd] at hvgE
    simp only [exprSizeW_v0, exprSizeW_fst, exprSizeW_snd, Nat.reduceAdd] at hvgS
    refine ⟨?_, ?_, ?_⟩
    · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperModeStartRecvC,
        _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperMainStartRecvC,
        _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
        _root_.CryptoGames.PRFPRNG.prngSamplers, _root_.CryptoGames.PRFPRNG.prngOps,
        _root_.CryptoGames.CKA.ckaSamplers, _root_.CryptoGames.CKA.ckaOps,
        Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, dsl_cost,
        Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
      split_ifs <;> omega
    · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperModeStartRecvC,
        _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperMainStartRecvC,
        _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
        _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var,
        exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_lt,
        exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
        exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
        exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_op,
        exprExcessUB_tget, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite,
        compExcessUB_caseOpt, ↓reduceIte, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperModeStartRecvC,
        _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperMainStartRecvC,
        _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
        _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
        exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
        exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_lt,
        exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
        exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl,
        exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_op,
        exprSizeW_tget, compSizeW_ret, compSizeW_bind, compSizeW_ite,
        compSizeW_caseOpt, ↓reduceIte, Nat.reduceAdd]
      omega
  | false =>
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperModeStartRecvC, Bool.false_eq_true, ↓reduceIte]
    have hC := (hooksFSMultiDFBucketPaperC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL par false).startRecv_le
      hE ctxE pE tE γE σE tnE
    have hE := (hooksFSMultiDFBucketPaperC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par false).startRecv_le
      hE ctxE pE tE γE σE tnE
    dsimp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC] at hC hE
    refine ⟨hC.trans (by omega), hE.trans (by omega), ?_⟩
    let Γ0 : List (Ty S_cka) :=
      .prod mbHsTy (.prod .nat (.prod (.base .γ)
        (.prod (.base .sig) (.prod (.base .t) .bool)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) mbHsTy :: Γ0
    have hpl := (postLeakDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL ctxE).2.2
    have hvg := (validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))).2.2
    have hlk := (lookupMultiDFBucketFC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (qC := fun _ => 0) (qS := fsMultiQueryS qep qR B0) B0 L (Γ' := Γ0)
      (.fst .v0) (.fst (.snd .v0))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0))))))))).2.2
    have hrg := (regSessMultiDFBucketE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L tL (Γ' := Γ1)
      (.snd .v0) (.fst (.snd .v1))
      (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1))))))))).2.2
    simp only [_root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_op, Nat.reduceAdd] at hpl hvg hlk hrg
    simp only [_root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
      _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_op, exprSizeW_tget,
      compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, Nat.reduceAdd]
    omega
private theorem hooksFSMultiDFBucketPaperModeC_costBounded (L B0 qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool) :
    HooksCostBounded
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep gMain tL par la)
      (2500 * L + 4 * bits (qep + 1) + 37 * bits (healEpoch tL) +
        10 * bits (tL.getD 0) + (B0 + 1) + 15200) where
  startSend_le hE ctxE pE tE γE σE rE :=
    ((hooksFSMultiDFBucketPaperC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL par la).startSend_le
      hE ctxE pE tE γE σE rE).trans (by omega)
  startRecv_le hE ctxE pE tE γE σE tnE :=
    (fsMultiDFBucketPaperModeStartRecvC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B0 qep 0 gMain tL par hE ctxE pE tE γE σE tnE).1
  fsSend_le hE ctxE pE tE ssvE hdrE mE pairE :=
    ((hooksFSMultiDFBucketPaperC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL par la).fsSend_le
      hE ctxE pE tE ssvE hdrE mE pairE).trans (by omega)
  fsRecv_le hE ctxE pE tE rsvE hdrE eE recE :=
    ((hooksFSMultiDFBucketPaperC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL par la).fsRecv_le
      hE ctxE pE tE rsvE hdrE eE recE).trans (by omega)
  commit_le hE ctxE pE oldE newE :=
    ((hooksFSMultiDFBucketPaperC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep tL par la).commit_le
      hE ctxE pE oldE newE).trans (by omega)
  reveal_le hE ctxE pE vpE :=
    (fsMultiDFBucketModeRevealC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B0 qep 0 gMain la tL hE ctxE pE vpE).1

private theorem hooksFSMultiDFBucketPaperModeC_excessBounded (L B0 qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool) :
    HooksExcessBounded B0 ckaSampC (fsMultiQueryC qep qR B0)
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep gMain tL par la)
      (350 * L + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 + 55200)
      (4900000 + 18 * bits (qep + 1) + 4500 * qR + 30 * B0)
      (9880000 + 18 * bits (qep + 1) + 6500 * qR + 50 * B0 + 3 * bits B0 + 700 * L) where
  startSend_le hE ctxE pE tE γE σE rE :=
    ((hooksFSMultiDFBucketPaperC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).startSend_le
      hE ctxE pE tE γE σE rE).trans (by omega)
  startRecv_le hE ctxE pE tE γE σE tnE :=
    (fsMultiDFBucketPaperModeStartRecvC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B0 qep qR gMain tL par hE ctxE pE tE γE σE tnE).2.1
  fsSend_le hE ctxE pE tE ssvE hdrE mE pairE :=
    (hooksFSMultiDFBucketPaperC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).fsSend_le
      hE ctxE pE tE ssvE hdrE mE pairE
  fsRecv_le hE ctxE pE tE rsvE hdrE eE recE :=
    (hooksFSMultiDFBucketPaperC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).fsRecv_le
      hE ctxE pE tE rsvE hdrE eE recE
  commit_le hE ctxE pE oldE newE :=
    ((hooksFSMultiDFBucketPaperC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).commit_le
      hE ctxE pE oldE newE).trans (by omega)
  reveal_le hE ctxE pE vpE :=
    (fsMultiDFBucketModeRevealC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B0 qep qR gMain la tL hE ctxE pE vpE).2.1

private def hooksFSMultiDFBucketPaperModeRecvOnlyC (L B0 qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool) :=
  { _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qep gMain tL par la with
    startSend := fun h _ _ _ _ _ _ => .ret (.pair .none h)
    reveal := fun h _ _ _ => .ret (.pair .none h) }

private theorem hooksFSMultiDFBucketPaperModeRecvOnlyC_sizeBounded (L B0 qep qR : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    HooksSizeBounded B0 ckaSampS (fsMultiQueryS qep qR B0)
      (hooksFSMultiDFBucketPaperModeRecvOnlyC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 qep gMain tL par la)
      (13 * bits L + 5 * bits (healEpoch tL) + 6 * bits (tL.getD 0) + bits (qep + 1) + 12000)
      (48 * bits (qep + qR + B0 + 1) + 40000)
      (8 * bits L + 5 * bits B0 + 48 * bits (qep + qR + B0 + 1) + 45000) where
  startSend_le hE ctxE pE tE γE σE rE := by
    simp only [hooksFSMultiDFBucketPaperModeRecvOnlyC, compSizeW_ret, exprSizeW_pair, exprSizeW_none]
    omega
  startRecv_le hE ctxE pE tE γE σE tnE :=
    (fsMultiDFBucketPaperModeStartRecvC_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B0 qep qR gMain tL par hE ctxE pE tE γE σE tnE).2.2
  fsSend_le hE ctxE pE tE ssvE hdrE mE pairE :=
    (hooksFSMultiDFBucketPaperC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).fsSend_le
      hE ctxE pE tE ssvE hdrE mE pairE
  fsRecv_le hE ctxE pE tE rsvE hdrE eE recE :=
    (hooksFSMultiDFBucketPaperC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la).fsRecv_le
      hE ctxE pE tE rsvE hdrE eE recE
  commit_le hE ctxE pE oldE newE := by
    simp only [hooksFSMultiDFBucketPaperModeRecvOnlyC,
      _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketCommitC,
      compSizeW_ret, exprSizeW_pair, exprSizeW_some]
    omega
  reveal_le hE ctxE pE vpE := by
    simp only [hooksFSMultiDFBucketPaperModeRecvOnlyC, compSizeW_ret, exprSizeW_pair, exprSizeW_none]
    omega


set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem bucketModeHandleDFPaperC_compCostW_le_gen
    (L B0 qep qR maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (H Ho Hs Hr C_inj : ℕ)
    {hk : _}
    (hhk_eq : hk = _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qep gMain tL par la)
    (cfg : _root_.CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg_eq : cfg = _root_.CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)
    (hcfgC : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), (cfg.injectFullE e).cost ≤ 3 * e.cost + C_inj)
    (hcfgE : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      exprExcessUB (ckaOpC B0) (cfg.injectFullE e) ≤ 4 * exprExcessUB (ckaOpC B0) e)
    (hhkC : HooksCostBounded hk H)
    (hhkE : HooksExcessBounded B0 ckaSampC (fsMultiQueryC qep qR B0) hk Ho Hs Hr) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep maxSkip gMain la tL par).handle ≤
      3 * H + 2 * Ho + Hs + Hr + 6000 * L + 5 * bits qep + 2 * (maxSkip + 1) + C_inj + 45000 := by

  have hΔ : (3 : ℕ) ≤ 4 := by omega
  let vpT := mVpTy
  let psT := _root_.CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let ckaHdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := mbEsTy
  let qT := (_root_.CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT
  let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0
  let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_cr2 : List (Ty S_cka) := psT :: .prod (.opt psT) mbHsTy :: Γ_cr
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) :=
    dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) :=
    txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ ::
      .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  let Γ_tx2 : List (Ty S_cka) := .prod vpT ckaHdrCtT :: .prod (.opt (.prod vpT ckaHdrCtT)) mbHsTy :: Γ_tx1
  let M := 3 * H + 2 * Ho + Hs + Hr + 6000 * L + 5 * bits qep + 2 * (maxSkip + 1) + C_inj + 44000
  have hep := DFProgBucketBounds.cEpMgmtE_any_cost_le (O' := OO_cka) (vpT := vpT) 3 qep hΔ (Γ' := Γ_tx0)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v6)) (.fst .v0) (_root_.CryptoGames.SM.isSomeE (.snd (.snd .v0)))
  have hvsC := DFProgBucketBounds.vSendC_any_cost_le hk H hhkC (Γ' := Γ_tx1)
    (_root_.CryptoGames.SM.Engine.esH (.fst .v7)) .v0 (.fst .v1)
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
    (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hvsE := vSendC_excessUB_le hk Ho Hs Hr hhkE (Γ' := Γ_tx1)
    (_root_.CryptoGames.SM.Engine.esH (.fst .v7)) .v0 (.fst .v1)
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
    (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hrec := DFProgBucketBounds.cRecordE_any_cost_le (O' := OO_cka) (vpT := vpT) L 3 hΔ (Γ' := Γ_tx2)
    .v2 (.fst .v3) (.fst .v0)
    (.pair (.pair (.fst .v3) (.pair (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
      (.add (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
      (.pair (.fst (.snd .v3)) (.snd .v0))) (.bool false)
  have hdlC := DFProgBucketBounds.deliverEC_any_cost_le hk H L maxSkip cfg hhkC (Γ' := Γ_dl) (.fst .v4) .v0
  have hdlE := DFProgBucketBounds.deliverEC_any_excessUB_le hk Ho Hs Hr L maxSkip cfg hhkE (Γ' := Γ_dl) (.fst .v4) .v0
  have hijC := DFProgBucketBounds.injectEC_anyCfg_cost_le hk H L 3 qep C_inj hΔ cfg hcfgC hhkC (Γ' := Γ_ij) (.fst .v3) .v0
  have hijE := DFProgBucketBounds.injectEC_anyCfg_excessUB_le hk Ho Hs Hr L 3 qep cfg hcfgE hhkE (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 true L (Γ' := Γ_cr)
    (_root_.CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  rcases hca with ⟨hcaC, hcaE⟩
  dsimp only [DFProgBucketBounds.corrAllowedChoiceE, cond] at hcaC hcaE
  have hac := DFProgBucketBounds.cAfterCorrE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ_cr2)
    (_root_.CryptoGames.SM.Engine.esG (hsT := mbHsTy) (.fst .v4)) .v2
  have hrvC := hhkC.reveal_le (Γ' := Γ_cr) (_root_.CryptoGames.SM.Engine.esH (.fst .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hrvE := hhkE.reveal_le (Γ' := Γ_cr) (_root_.CryptoGames.SM.Engine.esH (.fst .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  rw [hhk_eq] at hrvC hrvE
  dsimp only [_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC] at hrvC hrvE
  have hdfC := DFProgBucketBounds.deliverForgeEC_anyCfg_cost_le hk H L 3 qep C_inj hΔ cfg hcfgC hhkC (Γ' := Γ_df) (.fst .v1) .v0
  have hdfE := DFProgBucketBounds.deliverForgeEC_anyCfg_excessUB_le hk Ho Hs Hr L 3 qep cfg hcfgE hhkE (Γ' := Γ_df) (.fst .v1) .v0
  simp only [esG_cost, esH_cost, pGet_cost, cGsSt_cost, cGsEpoch_cost, _root_.CryptoGames.SM.Engine.cGsIdx,
    isSomeE_cost, Expr.cost, dsl_cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v6_cost,
    Expr.v7, bits_one, Nat.reduceAdd] at hep hvsC hrec hdlC hijC hcaC hac hrvC hdfC
  simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.pGet, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
    exprExcessUB_v4, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_none, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hvsE hdlE hijE hcaE hrvE hdfE
  dsimp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen,
    _root_.CryptoGames.SM.Construction.bucketModeHandleDFPaperC]
  rw [← hhk_eq, ← hcfg_eq]
  clear hhk_eq hcfg_eq
  change compCostW _ _ _ _ ≤ _
  refine (compCostW_bind_ret_le _ _ (ce := 10) (ck := M + 50) ?_ ?_).trans (by dsimp only [M]; omega)
  · simp [exprCostW, Expr.v0, Expr.v1]
  refine (compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 40) ?_ ?_ ?_).trans (by omega)
  · simp [exprCostW, Expr.v0, Expr.v1]
  · refine (compCostW_caseSum_le _ _ _ (cs := 2) (m := M + 30) ?_ ?_ ?_).trans (by omega)
    · simp [exprCostW, Expr.v0]
    · refine (compCostW_caseSum_le _ _ _ (cs := 2) (m := M + 20) ?_ ?_ ?_).trans (by omega)
      · simp [exprCostW, Expr.v0]
      · refine (compCostW_caseSum_le _ _ _ (cs := 2) (m := M + 10) ?_ ?_ ?_).trans (by omega)
        · simp [exprCostW, Expr.v0]
        · refine (compCostW_caseSum_le _ _ _ (cs := 2) (m := M) ?_ ?_ ?_).trans (by omega)
          · simp [exprCostW, Expr.v0]
          · refine compCostW_le_of_parts
                (a := 2 * H + 800 * L + 5 * bits qep + 3000) (b := Ho + Hs + 100) ?_ ?_
                (by dsimp only [M]; omega)
            · simp only [_root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.Engine.cGsIdx,
                _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.esMk,
                esG_cost, esH_cost, esAbort_cost, Comp.cost, Expr.cost, dsl_cost,
                v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, v6_cost, Expr.v7,
                bits_zero, bits_one, Nat.reduceAdd]
              omega
            · simp only [_root_.CryptoGames.SM.Engine.cEpMgmtE, _root_.CryptoGames.SM.Engine.cRecordE,
                _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cLeakE,
                _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
                _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
                _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSt,
                _root_.CryptoGames.SM.Engine.cGsB, _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
                _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cGsTrans,
                _root_.CryptoGames.SM.Engine.cGsChall, _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
                _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cRecPos,
                _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN,
                _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.pSet, _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.orE,
                _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
                _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
                exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
                exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_unit,
                exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add,
                exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and,
                exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
                exprExcessUB_inr, exprExcessUB_some, exprExcessUB_cons, exprExcessUB_caseOpt, exprExcessUB_letE,
                exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset,
                compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
                Nat.add_zero, Nat.zero_add, Nat.mul_zero]
              omega
          · refine compCostW_le_of_parts (a := 50) (b := 0) ?_ ?_ (by dsimp only [M]; omega)
            · simp only [Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, Nat.reduceAdd]; omega
            · simp only [compExcessUB_ret, exprExcessUB_pair, exprExcessUB_inl, exprExcessUB_inr,
                exprExcessUB_none, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v5, Nat.add_zero]; omega
        · refine compCostW_le_of_parts
              (a := 3 * H + 800 * L + 2 * maxSkip + 5600)
              (b := 2 * Ho + Hr + 150 * L + 32100) ?_ ?_ (by dsimp only [M]; omega)
          · simp only [Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, Nat.reduceAdd]
            omega
          · simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_inl,
              exprExcessUB_inr, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v5, Nat.add_zero]
            omega
      · refine compCostW_le_of_parts
            (a := 3 * H + 800 * L + bits qep + C_inj + 5200)
            (b := 2 * Ho + Hr + 150 * L + 700) ?_ ?_ (by dsimp only [M]; omega)
        · simp only [_root_.CryptoGames.SM.Construction.isHonestHdrMultiDFBucketE,
            _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
            _root_.CryptoGames.SM.Engine.vpTcurNat, _root_.CryptoGames.SM.Engine.vpTcur,
            _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.pGet,
            _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsWin,
            _root_.CryptoGames.SM.Engine.esH, esG_cost,
            _root_.CryptoGames.PRFPRNG.prngOps, _root_.CryptoGames.CKA.ckaOps,
            Comp.cost, Expr.cost, dsl_cost, bits_one,
            v0_cost, v1_cost, v2_cost, v3_cost, v4_cost,
            Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
          omega
        · simp only [_root_.CryptoGames.SM.Construction.isHonestHdrMultiDFBucketE,
            _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
            _root_.CryptoGames.SM.Engine.vpTcurNat, _root_.CryptoGames.SM.Engine.vpTcur,
            _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.pGet,
            _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsWin,
            _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
            _root_.CryptoGames.PRFPRNG.prngOps, ckaOpC,
            compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_inl, exprExcessUB_inr,
            exprExcessUB_ite, exprExcessUB_and, exprExcessUB_not, exprExcessUB_some, exprExcessUB_none,
            exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_add, exprExcessUB_eqN,
            exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_tget, exprExcessUB_op,
            exprExcessUB_fst, exprExcessUB_snd,
            exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
            exprExcessUB_var, Nat.add_zero, Nat.reduceAdd]
          omega
    · refine compCostW_le_of_parts
          (a := H + 5900 * L + 5000) (b := Ho + Hr + 1000) ?_ ?_ (by dsimp only [M]; omega)
      · simp only [_root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.esMk,
          esG_cost, esH_cost, esAbort_cost, Comp.cost, Expr.cost, dsl_cost,
          v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, bits_zero, bits_one, Nat.reduceAdd]
        omega
      · simp only [_root_.CryptoGames.SM.Engine.cAfterCorrE, _root_.CryptoGames.SM.Engine.cSafeChE,
          _root_.CryptoGames.SM.Engine.cLeakE, _root_.CryptoGames.SM.Engine.cCompInsertE,
          _root_.CryptoGames.SM.Engine.cCompSetE, _root_.CryptoGames.SM.Engine.esMk,
          _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.esAbort,
          _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
          _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
          _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
          _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
          _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
          _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
          _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.healedByE,
          _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN,
          _root_.CryptoGames.SM.pSet, _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.orE,
          _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
          _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
          exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
          exprExcessUB_v4, exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7,
          exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
          exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add, exprExcessUB_modK,
          exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and,
          exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
          exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_cons,
          exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_foldrB,
          exprExcessUB_tget, exprExcessUB_tset,
          compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
          compExcessUB_caseSum, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
        omega
  · refine compCostW_le_of_parts
        (a := 3 * H + 800 * L + bits qep + C_inj + 5400)
        (b := 2 * Ho + Hr + 300 * L + 1200) ?_ ?_ (by dsimp only [M]; omega)
    · simp only [_root_.CryptoGames.SM.Engine.cGsWin, esG_cost, Comp.cost, Expr.cost, dsl_cost,
        v0_cost, v1_cost, v2_cost, Nat.reduceAdd]
      omega
    · simp only [_root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.esG,
        compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_inr,
        exprExcessUB_ite, exprExcessUB_and, exprExcessUB_not, exprExcessUB_some, exprExcessUB_bool,
        exprExcessUB_letE, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_var, Nat.add_zero, Nat.reduceAdd]
      omega

set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem bucketModeHandleDFPaperC_compCostW_le (L B0 qep qR maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    let H := 2500 * L + 4 * bits (qep + 1) + 37 * bits (healEpoch tL) +
      10 * bits (tL.getD 0) + (B0 + 1) + 15200
    let Ho := 350 * L + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 + 55200
    let Hs := 4900000 + 18 * bits (qep + 1) + 4500 * qR + 30 * B0
    let Hr := 9880000 + 18 * bits (qep + 1) + 6500 * qR + 50 * B0 + 3 * bits B0 + 700 * L
    let C_inj := 2 * bits (tL.getD 0) + 80
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (_root_.CryptoGames.SM.Construction.bucketModeHandleDFPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep maxSkip gMain la tL par
        (Γ' := [.prod (_root_.CryptoGames.SM.Engine.esTy mVpTy mbHsTy) (.opt .nat),
          (_root_.CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q])
        .v0 .v1) ≤
      3 * H + 2 * Ho + Hs + Hr + 6000 * L + 5 * bits qep + 2 * (maxSkip + 1) + C_inj + 52000 := by
  dsimp only
  have hvg := fun {Γ'} (e : Expr OO_cka Γ' .nat) =>
    validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ') e
  have hgen := bucketModeHandleDFPaperC_compCostW_le_gen (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B0 qep qR maxSkip gMain la tL par
    (2500 * L + 4 * bits (qep + 1) + 37 * bits (healEpoch tL) + 10 * bits (tL.getD 0) + (B0 + 1) + 15200)
    (350 * L + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 + 55200)
    (4900000 + 18 * bits (qep + 1) + 4500 * qR + 30 * B0)
    (9880000 + 18 * bits (qep + 1) + 6500 * qR + 50 * B0 + 3 * bits B0 + 700 * L)
    (2 * bits (tL.getD 0) + 80)
    rfl
    (_root_.CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par) rfl
    (fun e => (hvg e).1) (fun e => (hvg e).2.1)
    (hooksFSMultiDFBucketPaperModeC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep gMain tL par la)
    (hooksFSMultiDFBucketPaperModeC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR gMain tL par la)
  dsimp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen] at hgen
  exact hgen.trans (by omega)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
private theorem bucketModeHandleDFPaperC_sizeW_le_tight
    (L B0 qep qR maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (Ho_send Ho_recv Hs Hr Hrev S_inj : ℕ)
    {hkMode : _}
    (hhk_eq : hkMode = _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qep gMain tL par la)
    (cfg : _root_.CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg_eq : cfg = _root_.CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      exprSizeW (ckaOpS B0) (cfg.injectFullE e) ≤ 4 * exprSizeW (ckaOpS B0) e + S_inj)
    (hhk_send : HooksSizeBounded B0 ckaSampS (fsMultiQueryS qep qR B0)
      (_root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep tL par la) Ho_send Hs Hr)
    (hhk_recv : HooksSizeBounded B0 ckaSampS (fsMultiQueryS qep qR B0)
      (hooksFSMultiDFBucketPaperModeRecvOnlyC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 qep gMain tL par la) Ho_recv Hs Hr)
    (hrev_fn : ∀ {Γ'} (hE : Expr OO_cka Γ' mbHsTy)
        (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpTy))
        (pE : Expr OO_cka Γ' .bool) (vpE : Expr OO_cka Γ' mVpTy),
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
        (_root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC (ckaInitA := ckaInitA)
          (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
          (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
          (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
          (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L gMain la tL hE ctxE pE vpE) ≤
        4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE +
          exprSizeW (ckaOpS B0) pE + exprSizeW (ckaOpS B0) vpE) + Hrev) :
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep maxSkip gMain la tL par).handle ≤
      Ho_send + 6 * Ho_recv + Hrev + Hs + 3 * Hr +
        60 * bits L + 20 * bits qep + 10 * bits maxSkip + 8 * S_inj + 41000 := by
  let hkSend := _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperC (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B0 1 4 qep tL par la
  let hkRecv := hooksFSMultiDFBucketPaperModeRecvOnlyC (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B0 qep gMain tL par la
  have hΔ : (3 : ℕ) ≤ 4 := by omega
  have hqep1 := bits_succ_le qep
  let vpT := mVpTy
  let ckaHdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := mbEsTy
  let qT := (_root_.CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT
  let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0
  let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) := dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) := txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  have hvs := Computational.Proofs.SessionCostedFig8.ProgSizeBounds.vSendC_sizeW_le hkSend Ho_send Hs Hr hhk_send
    (Γ' := Γ_tx1) (_root_.CryptoGames.SM.Engine.esH (.fst .v7)) .v0 (.fst .v1)
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
    (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hdl := DFProgBucketBounds.deliverEC_any_sizeW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    hkRecv Ho_recv Hs Hr L maxSkip cfg hhk_recv (Γ' := Γ_dl) (.fst .v4) .v0
  have hij := DFProgBucketBounds.injectEC_anyCfg_sizeW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    hkRecv Ho_recv Hs Hr L 3 qep S_inj hΔ cfg hcfg hhk_recv (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_sizeW_le_priv (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 true L (Γ' := Γ_cr)
    (_root_.CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  dsimp only [DFProgBucketBounds.corrAllowedChoiceE, cond] at hca
  have hrv := hrev_fn (Γ' := Γ_cr) (_root_.CryptoGames.SM.Engine.esH (.fst .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hdf := DFProgBucketBounds.deliverForgeEC_anyCfg_sizeW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    hkRecv Ho_recv Hs Hr L 3 qep S_inj hΔ cfg hcfg hhk_recv (Γ' := Γ_df) (.fst .v1) .v0
  let hkMode0 := _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B0 1 4 qep gMain tL par la
  change compSizeW _ _ _ (_root_.CryptoGames.SM.Engine.vSendC hkMode0 _ _ _ _ _ _ _) ≤ _ at hvs
  change compSizeW _ _ _ (_root_.CryptoGames.SM.Engine.deliverEC hkMode0 _ _ _ _ _) ≤ _ at hdl
  change compSizeW _ _ _ (_root_.CryptoGames.SM.Engine.injectEC hkMode0 _ _ _ _ _ _) ≤ _ at hij
  change compSizeW _ _ _ (_root_.CryptoGames.SM.Engine.deliverForgeEC hkMode0 _ _ _ _ _ _) ≤ _ at hdf
  have hhk_eq0 : hkMode = hkMode0 := hhk_eq
  rw [← hhk_eq0] at hvs hdl hij hdf
  clear hhk_eq0 hkMode0 hhk_send hhk_recv hkSend hkRecv
  simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.pGet, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v7, exprSizeW_var, exprSizeW_none, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_letE, Nat.reduceAdd] at hvs hdl hij hca hrv hdf
  dsimp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen,
    _root_.CryptoGames.SM.Construction.bucketModeHandleDFPaperC]
  rw [← hhk_eq, ← hcfg_eq]
  clear hhk_eq hcfg_eq
  simp only [_root_.CryptoGames.SM.Construction.isHonestHdrMultiDFBucketE,
    _root_.CryptoGames.SM.Construction.fsMultiDFBucketHsCache,
    _root_.CryptoGames.SM.Engine.vpTcurNat, _root_.CryptoGames.SM.Engine.vpTcur,
    _root_.CryptoGames.SM.Engine.cEpMgmtE, _root_.CryptoGames.SM.Engine.cRecordE,
    _root_.CryptoGames.SM.Engine.cAfterCorrE, _root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.Engine.cLeakE,
    _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
    _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
    _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.Engine.cGsB, _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cGsTrans,
    _root_.CryptoGames.SM.Engine.cGsChall, _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.cRecPos,
    _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.pSet, _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.orE,
    _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.otherE, _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    _root_.CryptoGames.PRFPRNG.prngOps, ckaOpS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt,
    exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_cons, exprSizeW_caseOpt,
    exprSizeW_caseSum, exprSizeW_letE, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget,
    exprSizeW_tset, exprSizeW_op, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
private theorem bucketModeHandleDFPaperC_sizeW_le (L B0 qep qR maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    let Ho := 86 * bits L + 31 * bits (healEpoch tL) + 8 * bits (tL.getD 0) +
      bits (qep + 1) + 16 * bits (qep + qR + B0 + 1) + 30000
    let Hoc := 13 * bits L + 5 * bits (healEpoch tL) + 6 * bits (tL.getD 0) + bits (qep + 1) + 12000
    let Hrev := 10 * bits L + 2 * bits (healEpoch tL) + 16 * bits (qep + qR + B0 + 1) + 13200
    let Hs := 48 * bits (qep + qR + B0 + 1) + 40000
    let Hr := 8 * bits L + 5 * bits B0 + 48 * bits (qep + qR + B0 + 1) + 45000
    let S_inj := 4 * bits (tL.getD 0) + 150
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0)
      (_root_.CryptoGames.SM.Construction.bucketModeHandleDFPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qep maxSkip gMain la tL par
        (Γ' := [.prod (_root_.CryptoGames.SM.Engine.esTy mVpTy mbHsTy) (.opt .nat),
          (_root_.CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q])
        .v0 .v1) ≤
      Ho + 6 * Hoc + Hrev + Hs + 3 * Hr + 60 * bits L + 20 * bits qep + 10 * bits maxSkip +
        8 * S_inj + 42000 := by
  dsimp only
  have hvg := fun {Γ'} (e : Expr OO_cka Γ' .nat) =>
    validGuessBucketParPaperE_bounds (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ') e
  have hgen := bucketModeHandleDFPaperC_sizeW_le_tight (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B0 qep qR maxSkip gMain la tL par
    (86 * bits L + 31 * bits (healEpoch tL) + 8 * bits (tL.getD 0) +
      bits (qep + 1) + 16 * bits (qep + qR + B0 + 1) + 30000)
    (13 * bits L + 5 * bits (healEpoch tL) + 6 * bits (tL.getD 0) + bits (qep + 1) + 12000)
    (48 * bits (qep + qR + B0 + 1) + 40000)
    (8 * bits L + 5 * bits B0 + 48 * bits (qep + qR + B0 + 1) + 45000)
    (10 * bits L + 2 * bits (healEpoch tL) + 16 * bits (qep + qR + B0 + 1) + 13200)
    (4 * bits (tL.getD 0) + 150)
    rfl
    (_root_.CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par) rfl
    (fun e => (hvg e).2.2)
    (hooksFSMultiDFBucketPaperC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR tL par la)
    (hooksFSMultiDFBucketPaperModeRecvOnlyC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B0 qep qR gMain tL par la)
    (fun hE ctxE pE vpE => (fsMultiDFBucketModeRevealC_bounds (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 qep qR gMain la tL hE ctxE pE vpE).2.2)
  dsimp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen] at hgen
  exact hgen.trans (by omega)

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFPaperMultiBucketModeProg_bounds
    (q qepC qR : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hqepC : qepC ≤ q + 11)
    (htL : ∀ x, tL = some x → x ≤ qepC + 3)
    (hqR : qR ≤ 2 * q + 2) :
    let L := q + 1
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxForwardJumps gMain la tL par
    (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.init +
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.finish + 100500 ≤
        fig8AtomicStepBound q qepC ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R.handle + 200100 ≤
        fig8AtomicStepBound q qepC) ∧
    (compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R.finish ≤
        690000 + 400 * bits (ratchetCostBudget q qepC)) ∧
    R.init.queries (fun _ => 1) (fun _ => 0) = 0 ∧
    R.finish.queries (fun _ => 1) (fun _ => 0) = 0 ∧
    R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  dsimp only
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  have htL0 : tL.getD 0 ≤ qepC + 3 := by
    cases tL with
    | none => simp
    | some x => exact htL x rfl
  have hhe0 : healEpoch tL ≤ qepC + 5 := by
    cases tL with
    | none => simp [healEpoch]
    | some x => have hx := htL x rfl; simp only [healEpoch]; omega
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbq1 := bits_succ_le qepC
  have hbtL_qep : bits (tL.getD 0) ≤ bits qepC + 3 := by
    have h1 := ReductionDsl.bits_mono htL0
    have h2 := bits_add_le_bits_add qepC 3
    omega
  have hbhe_qep : bits (healEpoch tL) ≤ bits qepC + 5 := by
    have h1 := ReductionDsl.bits_mono hhe0
    have h2 := bits_add_le_bits_add qepC 5
    omega
  have hbB0_lin := bits_le_add_one B0
  have hinit0 := initFSMultiDFBucketPaperEStateC_bounds (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    (qC := fsMultiQueryC qepC qR B0) (qS := fsMultiQueryS qepC qR B0)
    B0 L qepC tL par
  rcases hinit0 with ⟨hi0C, hi0E, hi0S⟩
  have hfin := bucketMultiFinish_bounds (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    (qC := fsMultiQueryC qepC qR B0) (qS := fsMultiQueryS qepC qR B0)
    L B0 qepC maxForwardJumps la tL par
  rcases hfin with ⟨hfC, hfE, hfS⟩
  have hhdW := bucketModeHandleDFPaperC_compCostW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B0 qepC qR maxForwardJumps gMain la tL par
  have hhdS := bucketModeHandleDFPaperC_sizeW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B0 qepC qR maxForwardJumps gMain la tL par
  dsimp only at hhdW hhdS
  let init0 := _root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L 4 qepC tL par (Γ' := [.unit]) (.bool false)
  let initComp := Comp.bind init0
    (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))
  have hiC := (bind_ret_bucketInit_cost_le _).trans (Nat.add_le_add_right hi0C 8)
  have hiE := (bind_ret_bucketInit_excessUB_le _).trans hi0E
  have hiS := (bind_ret_bucketInit_sizeW_le _).trans (Nat.add_le_add_right hi0S 10)
  have hiW := compCostW_le_cost_add_excessUB (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) initComp
  let Rfin := _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketProgGen
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxForwardJumps la tL par
  have hfW := compCostW_le_cost_add_excessUB (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) Rfin.finish
  have h2bL := two_mul_bits_succ_add25_le_ratchet q qepC
  have hbL : bits L = bits (q + 1) := rfl
  have hbL_lin := bits_le_add_one (q + 1)
  have hbB0_bL : bits B0 ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add_15 (by dsimp only [B0]; unfold maxForwardJumps; omega)
  have hbcomb_bL : bits (qepC + qR + B0 + 1) ≤ bits (q + 1) + 15 :=
    bits_le_bits_succ_add_15 (by dsimp only [B0]; unfold maxForwardJumps; omega)
  have hbm_const : bits maxForwardJumps = 15 := rfl
  have hbqep1_bL : bits (qepC + 1) ≤ bits (q + 1) + 11 := by
    have h1 : qepC + 1 ≤ (q + 1) + 11 := by omega
    exact (ReductionDsl.bits_mono h1).trans (bits_add_le_bits_add (q + 1) 11)
  have hbtL_bL : bits (tL.getD 0) ≤ bits (q + 1) + 13 := by
    have h1 : tL.getD 0 ≤ (q + 1) + 13 := by omega
    exact (ReductionDsl.bits_mono h1).trans (bits_add_le_bits_add (q + 1) 13)
  have hbhe_bL : bits (healEpoch tL) ≤ bits (q + 1) + 16 := by
    have h1 : healEpoch tL ≤ (q + 1) + 16 := by
      have := healEpoch_le_add3 htL0
      omega
    exact (ReductionDsl.bits_mono h1).trans (bits_add_le_bits_add (q + 1) 16)
  have hbqep_bL : bits qepC ≤ bits (q + 1) + 11 := by
    have hle : bits qepC ≤ bits (qepC + 1) := ReductionDsl.bits_mono (by omega)
    omega
  have hiW' := hiW.trans (Nat.add_le_add hiC hiE)
  have hfW' := hfW.trans (Nat.add_le_add hfC hfE)
  have hifW : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) initComp +
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) Rfin.finish + 100500 ≤
      fig8AtomicStepBound q qepC := by
    refine (Nat.add_le_add (Nat.add_le_add hiW' hfW') (Nat.le_refl 100500)).trans ?_
    refine le_fig8AtomicStepBound_linear_B0 q qepC B0 _ rfl ?_
    omega
  have hhdW' : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0)
      (_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxForwardJumps gMain la tL par).handle + 200100 ≤
      fig8AtomicStepBound q qepC := by
    dsimp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen]
    refine (Nat.add_le_add hhdW (Nat.le_refl 200100)).trans ?_
    refine le_fig8AtomicStepBound_linear_B0 q qepC B0 _ rfl ?_
    omega
  have hS' : compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) initComp +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0)
        (_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen
          (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
          (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
          (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
          (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxForwardJumps gMain la tL par).handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) Rfin.finish ≤
      690000 + 400 * bits (ratchetCostBudget q qepC) := by
    dsimp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen]
    refine (Nat.add_le_add (Nat.add_le_add hiS hhdS) hfS).trans ?_
    clear hifW hhdW' hiW' hfW' hiW hfW initComp Rfin hhdW
    omega
  refine ⟨⟨hifW, hhdW'⟩, hS', ?_, ?_,
    (_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProg_totalQueries
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4
      qepC maxForwardJumps gMain la tL par q).trans (Nat.mul_comm q 2).le⟩
  · simp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProg,
      _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen,
      _root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC_queries,
      Comp.queries, Nat.add_zero]
  · cases la <;>
      simp only [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProg,
        _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen,
        Comp.queries, Nat.add_zero, ↓reduceIte, Bool.false_eq_true, max_self]
set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFPaperMultiBucketModeProg_listM
    (L B0 qepC maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxSkip gMain la tL par
    compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish ≤ 20 := by
  dsimp only
  cases gMain <;> cases la <;>
    simp [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProg,
      _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen,
      _root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC,
      _root_.CryptoGames.SM.Construction.rootFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.bucketModeHandleDFPaperC,
      _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperModeStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperMainStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartRecvC,
      _root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketCommitC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketForgedHdrRevealC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketRevealC,
      _root_.CryptoGames.SM.Construction.rangeListC,
      _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
      _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
      _root_.CryptoGames.SM.Engine.commitEC, _root_.CryptoGames.SM.Engine.deliverEC,
      _root_.CryptoGames.SM.Engine.injectEC, _root_.CryptoGames.SM.Engine.deliverForgeEC,
      compListMNodes]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFPaperMultiBucketModeProg_qCount
    (L B0 qepC maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxSkip gMain la tL par
    compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish ≤ 25 := by
  dsimp only
  cases gMain <;> cases la <;>
    simp [_root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProg,
      _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiBucketModeProgGen,
      _root_.CryptoGames.SM.Construction.initFSMultiDFBucketPaperEStateC,
      _root_.CryptoGames.SM.Construction.rootFSMultiDFBucketPaperC,
      _root_.CryptoGames.SM.Construction.bucketModeHandleDFPaperC,
      _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketPaperModeC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperModeStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperMainStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperStartRecvC,
      _root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketPaperFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketCommitC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketModeRevealC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketForgedHdrRevealC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketRevealC,
      _root_.CryptoGames.SM.Construction.rangeListC,
      _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
      _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
      _root_.CryptoGames.SM.Engine.commitEC, _root_.CryptoGames.SM.Engine.deliverEC,
      _root_.CryptoGames.SM.Engine.injectEC, _root_.CryptoGames.SM.Engine.deliverForgeEC,
      compQueryCount]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFMultiProg_listM
    (L B0 qepC maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (t : ℕ) :
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qepC maxSkip la tL t
    compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish ≤ 50 := by
  dsimp only
  cases la <;>
    simp [_root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
      _root_.CryptoGames.SM.Construction.initFSMultiDFEStateC,
      _root_.CryptoGames.SM.Construction.rootFSMultiDFC,
      _root_.CryptoGames.SM.Construction.lookupMultiDFFC,
      _root_.CryptoGames.SM.Construction.finishFSMultiDFE,
      _root_.CryptoGames.SM.Construction.hooksFSMultiDFC,
      _root_.CryptoGames.SM.Construction.fsMultiDFStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFFsSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFCommitC,
      _root_.CryptoGames.SM.Construction.fsMultiDFRevealC,
      _root_.CryptoGames.SM.Construction.rangeListC,
      _root_.CryptoGames.SM.Engine.implECDF, _root_.CryptoGames.SM.Engine.implEC,
      _root_.CryptoGames.SM.Engine.transmitEC, _root_.CryptoGames.SM.Engine.challEC,
      _root_.CryptoGames.SM.Engine.corrEC,
      _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
      _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
      _root_.CryptoGames.SM.Engine.commitEC, _root_.CryptoGames.SM.Engine.deliverEC,
      _root_.CryptoGames.SM.Engine.injectEC, _root_.CryptoGames.SM.Engine.deliverForgeEC,
      compListMNodes]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFMultiProg_qCount
    (L B0 qepC maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (t : ℕ) :
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qepC maxSkip la tL t
    compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish ≤ 60 := by
  dsimp only
  cases la <;>
    simp [_root_.CryptoGames.SM.Construction.redFSAuthDFMultiProg,
      _root_.CryptoGames.SM.Construction.initFSMultiDFEStateC,
      _root_.CryptoGames.SM.Construction.rootFSMultiDFC,
      _root_.CryptoGames.SM.Construction.lookupMultiDFFC,
      _root_.CryptoGames.SM.Construction.finishFSMultiDFE,
      _root_.CryptoGames.SM.Construction.hooksFSMultiDFC,
      _root_.CryptoGames.SM.Construction.fsMultiDFStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFStartRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFFsSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFCommitC,
      _root_.CryptoGames.SM.Construction.fsMultiDFRevealC,
      _root_.CryptoGames.SM.Construction.rangeListC,
      _root_.CryptoGames.SM.Engine.implECDF, _root_.CryptoGames.SM.Engine.implEC,
      _root_.CryptoGames.SM.Engine.transmitEC, _root_.CryptoGames.SM.Engine.challEC,
      _root_.CryptoGames.SM.Engine.corrEC,
      _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
      _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
      _root_.CryptoGames.SM.Engine.commitEC, _root_.CryptoGames.SM.Engine.deliverEC,
      _root_.CryptoGames.SM.Engine.injectEC, _root_.CryptoGames.SM.Engine.deliverForgeEC,
      compQueryCount]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFMultiBucketProg_listM
    (L B0 qepC maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool) :
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFMultiBucketProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxSkip la tL par
    compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish ≤ 50 := by
  dsimp only
  cases la <;>
    simp [_root_.CryptoGames.SM.Construction.redFSAuthDFMultiBucketProg,
      _root_.CryptoGames.SM.Construction.initFSMultiDFBucketEStateC,
      _root_.CryptoGames.SM.Construction.rootFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartRecvC,
      _root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketCommitC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketRevealC,
      _root_.CryptoGames.SM.Construction.rangeListC,
      _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
      _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
      _root_.CryptoGames.SM.Engine.commitEC, _root_.CryptoGames.SM.Engine.deliverEC,
      _root_.CryptoGames.SM.Engine.injectEC, _root_.CryptoGames.SM.Engine.deliverForgeEC,
      compListMNodes]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
private theorem redFSAuthDFMultiBucketProg_qCount
    (L B0 qepC maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool) :
    let R := _root_.CryptoGames.SM.Construction.redFSAuthDFMultiBucketProg (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 4 qepC maxSkip la tL par
    compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish ≤ 60 := by
  dsimp only
  cases la <;>
    simp [_root_.CryptoGames.SM.Construction.redFSAuthDFMultiBucketProg,
      _root_.CryptoGames.SM.Construction.initFSMultiDFBucketEStateC,
      _root_.CryptoGames.SM.Construction.rootFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.hooksFSMultiDFBucketC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketStartRecvC,
      _root_.CryptoGames.SM.Construction.lookupMultiDFBucketFC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsSendC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketFsRecvC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketCommitC,
      _root_.CryptoGames.SM.Construction.fsMultiDFBucketRevealC,
      _root_.CryptoGames.SM.Construction.rangeListC,
      _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
      _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
      _root_.CryptoGames.SM.Engine.commitEC, _root_.CryptoGames.SM.Engine.deliverEC,
      _root_.CryptoGames.SM.Engine.injectEC, _root_.CryptoGames.SM.Engine.deliverForgeEC,
      compQueryCount]

end MultiFsBucketBounds

section CoinBranchCombinator

private theorem gRedBounded_mono_budget {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    {R : CostedReduction O I G C rIn aIn aOut out}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)
    (h : GRedBounded R wTag wSamp q qOut B₁) :
    GRedBounded R wTag wSamp q qOut B₂ := by
  rcases h with ⟨hCost, hSize, hQ, hOps, hSmp, hFits⟩
  refine ⟨hCost.trans hB, ?_, hQ, hOps, hSmp, ?_⟩
  · exact hSize.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (bits_mono hB)) _)
  · intro B hv A hAq hAf x hx
    have hW : 2 * (B₁ + q + 1) * (B + 1) ≤ 2 * (B₂ + q + 1) * (B + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by omega))
    obtain ⟨hy, hr⟩ := hFits B hv A hAq hAf x hx
    exact ⟨fun y hy' => ReductionDsl.Ty.fits_mono hW out y (hy y hy'),
      fun r0 hr0 r1 hr1 => ReductionDsl.Ty.fits_mono hW R.σ r1.2 (hr r0 hr0 r1 hr1)⟩

private theorem ratchetCostBudget_mono_qep {q qep₁ qep₂ : ℕ} (h : qep₁ ≤ qep₂) :
    ratchetCostBudget q qep₁ ≤ ratchetCostBudget q qep₂ :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_left (bits_mono h) _)

end CoinBranchCombinator

section Stage2FsMultiAtomicProgs

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey)
  (idOf : Party → IdentityKey) (lam : Pt)

local instance : Nonempty Pt := ⟨0⟩
local notation "atomicFig8Ops" => _root_.ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam

private theorem aux_ckaOpS_eq (B0 : ℕ) :
    Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaOpS B0 = ckaOpS B0 := by
  funext o; cases o <;> rfl

private theorem aux_exprSizeW_eq {S' : Sig} {O' : Ops S'} (opS : O'.Op → ℕ)
    {Γ' : List (Ty S')} {t' : Ty S'} (e : Expr O' Γ' t') :
    Computational.Proofs.SessionCostedFig8.BundlesAuxSize.exprSizeW opS e = exprSizeW opS e := by
  induction e <;>
    simp [Computational.Proofs.SessionCostedFig8.BundlesAuxSize.exprSizeW, exprSizeW, *]

private theorem aux_compSizeW_eq {S' : Sig} {O' : Ops S'} {ι : Type} {TSp : OracleSpec ι}
    {I' : Iface S' TSp} (opS : O'.Op → ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    {Γ' : List (Ty S')} {t' : Ty S'} (c : Comp O' I' Γ' t') :
    Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS c =
      compSizeW opS sS qS c := by
  induction c <;>
    simp [Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW, compSizeW,
      aux_exprSizeW_eq, *]

private theorem aux_size_of_bundles_size {S' : Sig} {O' : Ops S'} {ι : Type} {TSp : OracleSpec ι}
    {I' : Iface S' TSp} {opS₁ opS₂ : O'.Op → ℕ} {sS₁ sS₂ : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {Γ₁ Γ₂ Γ₃ : List (Ty S')} {t₁ t₂ t₃ : Ty S'}
    {c₁ : Comp O' I' Γ₁ t₁} {c₂ : Comp O' I' Γ₂ t₂} {c₃ : Comp O' I' Γ₃ t₃} {bound : ℕ}
    (hop : opS₁ = opS₂) (hsS : sS₁ = sS₂)
    (hs : compSizeW opS₂ sS₂ qS c₁ +
      compSizeW opS₂ sS₂ qS c₂ +
      compSizeW opS₂ sS₂ qS c₃ + 400 ≤ bound) :
    Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS₁ sS₁ qS c₁ +
      Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS₁ sS₁ qS c₂ +
      Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS₁ sS₁ qS c₃ + 400 ≤
        bound := by
  subst hop; subst hsS
  simpa only [aux_compSizeW_eq] using hs

set_option maxRecDepth 200000 in
theorem redFSAuthDFMultiAtomicProg_gRedBounded
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hqep : qep ≤ q + 11 := by omega) :
    GRedBounded
      (redFSAuthDFMultiAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  unfold redFSAuthDFMultiAtomicProg
  dsimp only
  split_ifs with h
  · obtain ⟨hp, hs, hq⟩ := redFSAuthDFMultiProg_bounds q qep qR la tL t hqep h.1 h.2.1 h.2.2
    exact compileFsMultiDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam stage la j
      qep qR ((q + 1) * (maxForwardJumps + 1))
      (redFSAuthDFMultiProg (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1
        qep maxForwardJumps la tL t)
      q (2 * q)
      (hB0 := Nat.mul_le_mul_right _ (by omega)) (hparts := hp)
      (hSize := aux_size_of_bundles_size (aux_ckaOpS_eq _) rfl hs) (hQ := hq)
      (hqOut := le_rfl)
      (hListM := redFSAuthDFMultiProg_listM (q + 1) ((q + 1) * (maxForwardJumps + 1)) qep maxForwardJumps la tL t)
      (hqCount := redFSAuthDFMultiProg_qCount (q + 1) ((q + 1) * (maxForwardJumps + 1)) qep maxForwardJumps la tL t)
  · exact dummyFsStage2AtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q (2 * q)

set_option maxRecDepth 200000 in
theorem redFSAuthDFMultiBucketAtomicProg_gRedBounded
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hqep : qep ≤ q + 11 := by omega) :
    GRedBounded
      (redFSAuthDFMultiBucketAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL par)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  unfold redFSAuthDFMultiBucketAtomicProg
  dsimp only
  split_ifs with h
  · obtain ⟨hp, hs, hq⟩ := redFSAuthDFMultiBucketProg_bounds q qep qR la tL par hqep h.1 h.2
    exact compileFsMultiDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam stage la j
      qep qR ((q + 1) * (maxForwardJumps + 1))
      (redFSAuthDFMultiBucketProg (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4
        qep maxForwardJumps la tL par)
      q (2 * q)
      (hB0 := Nat.mul_le_mul_right _ (by omega)) (hparts := hp)
      (hSize := aux_size_of_bundles_size (aux_ckaOpS_eq _) rfl hs) (hQ := hq)
      (hqOut := le_rfl)
      (hListM := redFSAuthDFMultiBucketProg_listM (q + 1) ((q + 1) * (maxForwardJumps + 1)) qep maxForwardJumps la tL par)
      (hqCount := redFSAuthDFMultiBucketProg_qCount (q + 1) ((q + 1) * (maxForwardJumps + 1)) qep maxForwardJumps la tL par)
  · exact dummyFsStage2AtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q (2 * q)

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
theorem redFSAuthDFPaperMultiAtomicProg_gRedBounded
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hqep : qep ≤ q + 11 := by omega) :
    GRedBounded
      (redFSAuthDFPaperMultiAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  unfold redFSAuthDFPaperMultiAtomicProg
  dsimp only
  split_ifs with h
  · obtain ⟨hp, hs, hq⟩ := redFSAuthDFPaperMultiProg_bounds q qep qR la tL t hqep h.1 h.2.1 h.2.2
    exact compileFsMultiDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam stage la j
      qep qR ((q + 1) * (maxForwardJumps + 1))
      (redFSAuthDFPaperMultiProg (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1
        qep maxForwardJumps la tL t)
      q (2 * q)
      (hB0 := Nat.mul_le_mul_right _ (by omega)) (hparts := hp)
      (hSize := aux_size_of_bundles_size (aux_ckaOpS_eq _) rfl hs) (hQ := hq)
      (hqOut := le_rfl)
      (hListM := by
        cases la <;>
          simp [redFSAuthDFPaperMultiProg, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
            _root_.CryptoGames.SM.Construction.initFSMultiEStateC,
            _root_.CryptoGames.SM.Construction.rootFSMultiC, _root_.CryptoGames.SM.Construction.finishFSMultiE,
            _root_.CryptoGames.SM.Construction.hooksFSMultiC, _root_.CryptoGames.SM.Construction.fsMultiStartSendC,
            _root_.CryptoGames.SM.Construction.fsMultiStartRecvC, _root_.CryptoGames.SM.Construction.lookupMultiFC,
            _root_.CryptoGames.SM.Construction.fsMultiFsSendC, _root_.CryptoGames.SM.Construction.fsMultiFsRecvC,
            _root_.CryptoGames.SM.Construction.fsMultiCommitC, _root_.CryptoGames.SM.Construction.fsMultiRevealC,
            _root_.CryptoGames.SM.Construction.rangeListC,
            _root_.CryptoGames.SM.Engine.implECDFPaper, _root_.CryptoGames.SM.Engine.implECPaper,
            _root_.CryptoGames.SM.Engine.challEC, _root_.CryptoGames.SM.Engine.corrECPaper,
            _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
            _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
            _root_.CryptoGames.SM.Engine.transmitEC, _root_.CryptoGames.SM.Engine.commitEC,
            _root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.injectEC,
            _root_.CryptoGames.SM.Engine.deliverForgeEC, compListMNodes])
      (hqCount := by
        cases la <;>
          simp [redFSAuthDFPaperMultiProg, _root_.CryptoGames.SM.Construction.redFSAuthDFPaperMultiProg,
            _root_.CryptoGames.SM.Construction.initFSMultiEStateC,
            _root_.CryptoGames.SM.Construction.rootFSMultiC, _root_.CryptoGames.SM.Construction.finishFSMultiE,
            _root_.CryptoGames.SM.Construction.hooksFSMultiC, _root_.CryptoGames.SM.Construction.fsMultiStartSendC,
            _root_.CryptoGames.SM.Construction.fsMultiStartRecvC, _root_.CryptoGames.SM.Construction.lookupMultiFC,
            _root_.CryptoGames.SM.Construction.fsMultiFsSendC, _root_.CryptoGames.SM.Construction.fsMultiFsRecvC,
            _root_.CryptoGames.SM.Construction.fsMultiCommitC, _root_.CryptoGames.SM.Construction.fsMultiRevealC,
            _root_.CryptoGames.SM.Construction.rangeListC,
            _root_.CryptoGames.SM.Engine.implECDFPaper, _root_.CryptoGames.SM.Engine.implECPaper,
            _root_.CryptoGames.SM.Engine.challEC, _root_.CryptoGames.SM.Engine.corrECPaper,
            _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
            _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
            _root_.CryptoGames.SM.Engine.transmitEC, _root_.CryptoGames.SM.Engine.commitEC,
            _root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.injectEC,
            _root_.CryptoGames.SM.Engine.deliverForgeEC, compQueryCount])
  · exact dummyFsStage2AtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q (2 * q)

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
theorem redFSAuthDFShiftedPaperMultiAtomicProg_gRedBounded
    (stage la : Bool) (j qR q qep t : ℕ)
    (hqep : qep ≤ q + 11 := by omega) :
    GRedBounded
      (redFSAuthDFShiftedPaperMultiAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  unfold redFSAuthDFShiftedPaperMultiAtomicProg
  dsimp only
  split_ifs with h
  · obtain ⟨hp, hs, hq⟩ := redFSAuthDFShiftedPaperMultiGenProg_bounds
      q qep qR 1 (t - 2) t true la (Or.inl ⟨rfl, rfl⟩) hqep (by omega) h.1 h.2
    exact compileFsMultiDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam stage la j
      qep qR ((q + 1) * (maxForwardJumps + 1))
      (redFSAuthDFShiftedPaperMultiProg (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1
        qep maxForwardJumps (t - 2) t la)
      q (2 * q)
      (hB0 := Nat.mul_le_mul_right _ (by omega)) (hparts := hp)
      (hSize := aux_size_of_bundles_size (aux_ckaOpS_eq _) rfl hs) (hQ := hq)
      (hqOut := le_rfl)
      (hListM := by
        cases la <;>
          simp [redFSAuthDFShiftedPaperMultiProg, redFSAuthDFShiftedPaperMultiGenProg,
            _root_.CryptoGames.SM.Construction.initFSMultiEStateC, _root_.CryptoGames.SM.Construction.rootFSMultiC,
            _root_.CryptoGames.SM.Construction.finishFSMultiE, _root_.CryptoGames.SM.Construction.hooksFSMultiC,
            _root_.CryptoGames.SM.Construction.fsMultiStartSendC, _root_.CryptoGames.SM.Construction.fsMultiStartRecvC,
            _root_.CryptoGames.SM.Construction.lookupMultiFC, _root_.CryptoGames.SM.Construction.fsMultiFsSendC,
            _root_.CryptoGames.SM.Construction.fsMultiFsRecvC, _root_.CryptoGames.SM.Construction.fsMultiCommitC,
            _root_.CryptoGames.SM.Construction.fsMultiRevealC, _root_.CryptoGames.SM.Construction.rangeListC,
            _root_.CryptoGames.SM.Engine.implECDFShiftedPaperGen,
            _root_.CryptoGames.SM.Engine.implECShiftedPaperGen,
            _root_.CryptoGames.SM.Engine.challEC, _root_.CryptoGames.SM.Engine.corrECShiftedPaper,
            _root_.CryptoGames.SM.Engine.injectECGen, _root_.CryptoGames.SM.Engine.injectECB1,
            _root_.CryptoGames.SM.Engine.deliverForgeECGen, _root_.CryptoGames.SM.Engine.deliverForgeECB1,
            _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
            _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
            _root_.CryptoGames.SM.Engine.transmitEC, _root_.CryptoGames.SM.Engine.commitEC,
            _root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.injectEC,
            _root_.CryptoGames.SM.Engine.deliverForgeEC, compListMNodes])
      (hqCount := by
        cases la <;>
          simp [redFSAuthDFShiftedPaperMultiProg, redFSAuthDFShiftedPaperMultiGenProg,
            _root_.CryptoGames.SM.Construction.initFSMultiEStateC, _root_.CryptoGames.SM.Construction.rootFSMultiC,
            _root_.CryptoGames.SM.Construction.finishFSMultiE, _root_.CryptoGames.SM.Construction.hooksFSMultiC,
            _root_.CryptoGames.SM.Construction.fsMultiStartSendC, _root_.CryptoGames.SM.Construction.fsMultiStartRecvC,
            _root_.CryptoGames.SM.Construction.lookupMultiFC, _root_.CryptoGames.SM.Construction.fsMultiFsSendC,
            _root_.CryptoGames.SM.Construction.fsMultiFsRecvC, _root_.CryptoGames.SM.Construction.fsMultiCommitC,
            _root_.CryptoGames.SM.Construction.fsMultiRevealC, _root_.CryptoGames.SM.Construction.rangeListC,
            _root_.CryptoGames.SM.Engine.implECDFShiftedPaperGen,
            _root_.CryptoGames.SM.Engine.implECShiftedPaperGen,
            _root_.CryptoGames.SM.Engine.challEC, _root_.CryptoGames.SM.Engine.corrECShiftedPaper,
            _root_.CryptoGames.SM.Engine.injectECGen, _root_.CryptoGames.SM.Engine.injectECB1,
            _root_.CryptoGames.SM.Engine.deliverForgeECGen, _root_.CryptoGames.SM.Engine.deliverForgeECB1,
            _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
            _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
            _root_.CryptoGames.SM.Engine.transmitEC, _root_.CryptoGames.SM.Engine.commitEC,
            _root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.injectEC,
            _root_.CryptoGames.SM.Engine.deliverForgeEC, compQueryCount])
  · exact dummyFsStage2AtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q (2 * q)

set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
set_option linter.unusedSimpArgs false in
theorem redFSAuthDFShiftedDir2PaperMultiAtomicProg_gRedBounded
    (stage la : Bool) (j qR q qep t : ℕ)
    (hqep : qep ≤ q + 11 := by omega) :
    GRedBounded
      (redFSAuthDFShiftedDir2PaperMultiAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  unfold redFSAuthDFShiftedDir2PaperMultiAtomicProg
  dsimp only
  split_ifs with h
  · obtain ⟨hp, hs, hq⟩ := redFSAuthDFShiftedPaperMultiGenProg_bounds
      q qep qR 0 (t - 1) t false la (Or.inr ⟨rfl, rfl⟩) hqep (by omega) h.1 h.2
    exact compileFsMultiDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam stage la j
      qep qR ((q + 1) * (maxForwardJumps + 1))
      (redFSAuthDFShiftedDir2PaperMultiProg (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps (t - 1) t la)
      q (2 * q)
      (hB0 := Nat.mul_le_mul_right _ (by omega)) (hparts := hp)
      (hSize := aux_size_of_bundles_size (aux_ckaOpS_eq _) rfl hs) (hQ := hq)
      (hqOut := le_rfl)
      (hListM := by
        cases la <;>
          simp [redFSAuthDFShiftedDir2PaperMultiProg, redFSAuthDFShiftedPaperMultiGenProg,
            _root_.CryptoGames.SM.Construction.initFSMultiEStateC, _root_.CryptoGames.SM.Construction.rootFSMultiC,
            _root_.CryptoGames.SM.Construction.finishFSMultiE, _root_.CryptoGames.SM.Construction.hooksFSMultiC,
            _root_.CryptoGames.SM.Construction.fsMultiStartSendC, _root_.CryptoGames.SM.Construction.fsMultiStartRecvC,
            _root_.CryptoGames.SM.Construction.lookupMultiFC, _root_.CryptoGames.SM.Construction.fsMultiFsSendC,
            _root_.CryptoGames.SM.Construction.fsMultiFsRecvC, _root_.CryptoGames.SM.Construction.fsMultiCommitC,
            _root_.CryptoGames.SM.Construction.fsMultiRevealC, _root_.CryptoGames.SM.Construction.rangeListC,
            _root_.CryptoGames.SM.Engine.implECDFShiftedPaperGen,
            _root_.CryptoGames.SM.Engine.implECShiftedPaperGen,
            _root_.CryptoGames.SM.Engine.challEC, _root_.CryptoGames.SM.Engine.corrECShiftedPaper,
            _root_.CryptoGames.SM.Engine.injectECGen, _root_.CryptoGames.SM.Engine.injectECB1,
            _root_.CryptoGames.SM.Engine.deliverForgeECGen, _root_.CryptoGames.SM.Engine.deliverForgeECB1,
            _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
            _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
            _root_.CryptoGames.SM.Engine.transmitEC, _root_.CryptoGames.SM.Engine.commitEC,
            _root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.injectEC,
            _root_.CryptoGames.SM.Engine.deliverForgeEC, compListMNodes])
      (hqCount := by
        cases la <;>
          simp [redFSAuthDFShiftedDir2PaperMultiProg, redFSAuthDFShiftedPaperMultiGenProg,
            _root_.CryptoGames.SM.Construction.initFSMultiEStateC, _root_.CryptoGames.SM.Construction.rootFSMultiC,
            _root_.CryptoGames.SM.Construction.finishFSMultiE, _root_.CryptoGames.SM.Construction.hooksFSMultiC,
            _root_.CryptoGames.SM.Construction.fsMultiStartSendC, _root_.CryptoGames.SM.Construction.fsMultiStartRecvC,
            _root_.CryptoGames.SM.Construction.lookupMultiFC, _root_.CryptoGames.SM.Construction.fsMultiFsSendC,
            _root_.CryptoGames.SM.Construction.fsMultiFsRecvC, _root_.CryptoGames.SM.Construction.fsMultiCommitC,
            _root_.CryptoGames.SM.Construction.fsMultiRevealC, _root_.CryptoGames.SM.Construction.rangeListC,
            _root_.CryptoGames.SM.Engine.implECDFShiftedPaperGen,
            _root_.CryptoGames.SM.Engine.implECShiftedPaperGen,
            _root_.CryptoGames.SM.Engine.challEC, _root_.CryptoGames.SM.Engine.corrECShiftedPaper,
            _root_.CryptoGames.SM.Engine.injectECGen, _root_.CryptoGames.SM.Engine.injectECB1,
            _root_.CryptoGames.SM.Engine.deliverForgeECGen, _root_.CryptoGames.SM.Engine.deliverForgeECB1,
            _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
            _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
            _root_.CryptoGames.SM.Engine.transmitEC, _root_.CryptoGames.SM.Engine.commitEC,
            _root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.injectEC,
            _root_.CryptoGames.SM.Engine.deliverForgeEC, compQueryCount])
  · exact dummyFsStage2AtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q (2 * q)

theorem redFSAuthDFCasePaperMultiAtomicProg_gRedBounded
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hqep : qep ≤ q + 11 := by omega) :
    GRedBounded
      (redFSAuthDFCasePaperMultiAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  unfold redFSAuthDFCasePaperMultiAtomicProg
  split_ifs
  · exact redFSAuthDFShiftedDir2PaperMultiAtomicProg_gRedBounded ℓ Pt C Dh encPt encT idOf lam
      stage la j qR q qep t hqep
  · exact redFSAuthDFShiftedPaperMultiAtomicProg_gRedBounded ℓ Pt C Dh encPt encT idOf lam
      stage la j qR q qep t hqep
  · exact redFSAuthDFPaperMultiAtomicProg_gRedBounded ℓ Pt C Dh encPt encT idOf lam
      stage la j qR q qep tL t hqep

set_option maxRecDepth 200000 in
theorem redFSAuthDFPaperMultiBucketAtomicProg_gRedBounded
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (par : Bool) :
    GRedBounded
      (redFSAuthDFPaperMultiBucketAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL par)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  unfold redFSAuthDFPaperMultiBucketAtomicProg
  dsimp only
  split_ifs with h
  · refine gRedBounded_mono_budget (ratchetCostBudget_mono_qep (Nat.min_le_left qep (q + 11))) ?_
    let qepC := min qep (q + 11)
    let L := q + 1
    let B0 := (q + 1) * (maxForwardJumps + 1)
    have hqepC : qepC ≤ q + 11 := Nat.min_le_right qep (q + 11)
    let R₁ : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (fsaeadMultiHeaderAdIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (_root_.CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
        (prngSMCodecDF (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        .unit .unit .bool .bool :=
      redFSAuthDFPaperMultiBucketModeProg L B0 1 4 qepC maxForwardJumps true la tL par
    let R₂ : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (fsaeadMultiHeaderAdIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (_root_.CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
        (prngSMCodecDF (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        .unit .unit .bool .bool :=
      redFSAuthDFPaperMultiBucketModeProg L B0 1 4 qepC maxForwardJumps false la tL par
    let Rbranch := ckaCoinBranchDFRed ℓ Pt C Dh encPt encT idOf lam B0 R₁ R₂
    let cCoin := Comp.sample
      (O := fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (I := fsaeadMultiHeaderAdIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (Γ := [.unit]) CKASamp.bit .unit
    have hBounds₁ :
        (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₁.init +
          compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₁.finish + 100500 ≤
            fig8AtomicStepBound q qepC ∧
          compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₁.handle + 200100 ≤
            fig8AtomicStepBound q qepC) ∧
        (compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R₁.init +
          compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R₁.handle +
          compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R₁.finish ≤
            690000 + 400 * bits (ratchetCostBudget q qepC)) ∧
        R₁.init.queries (fun _ => 1) (fun _ => 0) = 0 ∧
        R₁.finish.queries (fun _ => 1) (fun _ => 0) = 0 ∧
        R₁.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q :=
      redFSAuthDFPaperMultiBucketModeProg_bounds q qepC qR true la tL par hqepC h.1 h.2
    obtain ⟨⟨hif₁, hhd₁⟩, hs₁, hiQ₁, hfQ₁, htQ₁⟩ := hBounds₁
    have hBounds₂ :
        (compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₂.init +
          compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₂.finish + 100500 ≤
            fig8AtomicStepBound q qepC ∧
          compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₂.handle + 200100 ≤
            fig8AtomicStepBound q qepC) ∧
        (compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R₂.init +
          compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R₂.handle +
          compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qepC qR B0) R₂.finish ≤
            690000 + 400 * bits (ratchetCostBudget q qepC)) ∧
        R₂.init.queries (fun _ => 1) (fun _ => 0) = 0 ∧
        R₂.finish.queries (fun _ => 1) (fun _ => 0) = 0 ∧
        R₂.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q :=
      redFSAuthDFPaperMultiBucketModeProg_bounds q qepC qR false la tL par hqepC h.1 h.2
    obtain ⟨⟨hif₂, hhd₂⟩, hs₂, hiQ₂, hfQ₂, htQ₂⟩ := hBounds₂
    have hLM₁ : compListMNodes R₁.init + compListMNodes R₁.handle + compListMNodes R₁.finish ≤ 20 :=
      redFSAuthDFPaperMultiBucketModeProg_listM L B0 qepC maxForwardJumps true la tL par
    have hQC₁ : compQueryCount R₁.init + compQueryCount R₁.handle + compQueryCount R₁.finish ≤ 25 :=
      redFSAuthDFPaperMultiBucketModeProg_qCount L B0 qepC maxForwardJumps true la tL par
    have hLM₂ : compListMNodes R₂.init + compListMNodes R₂.handle + compListMNodes R₂.finish ≤ 20 :=
      redFSAuthDFPaperMultiBucketModeProg_listM L B0 qepC maxForwardJumps false la tL par
    have hQC₂ : compQueryCount R₂.init + compQueryCount R₂.handle + compQueryCount R₂.finish ≤ 25 :=
      redFSAuthDFPaperMultiBucketModeProg_qCount L B0 qepC maxForwardJumps false la tL par
    have hQ : Rbranch.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q :=
      coinBranchRed_totalQueries_le (fun _ => 1) (fun _ => 0) cCoin R₁ R₂ q (2 * q)
        rfl hiQ₁ hiQ₂ hfQ₁ hfQ₂ htQ₁ htQ₂
    have hinit_cost : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₂.init =
        compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₁.init := rfl
    have hfin_cost : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₂.finish =
        compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) R₁.finish := rfl
    have hcW := coinBranchRed_compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) cCoin R₁ R₂
    have hcCoinW : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) cCoin ≤ 210 := by
      simp [cCoin, compCostW, exprCostW, ckaSampC]
    have hparts : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) Rbranch.init +
        compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) Rbranch.finish + 100000 ≤
          fig8AtomicStepBound q qepC ∧
        compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) Rbranch.handle + 200000 ≤
          fig8AtomicStepBound q qepC := by
      change compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) (coinBranchRed cCoin R₁ R₂).init +
          compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) (coinBranchRed cCoin R₁ R₂).finish + 100000 ≤
            fig8AtomicStepBound q qepC ∧
          compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qepC qR B0) (coinBranchRed cCoin R₁ R₂).handle + 200000 ≤
            fig8AtomicStepBound q qepC
      rcases hcW with ⟨hciW, hchW, hcfW⟩
      simp only [Nat.max_def] at hciW hchW hcfW
      split_ifs at hciW hchW hcfW <;> omega
    have hcS := coinBranchRed_compSizeW
      (Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaOpS B0)
      Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaSampS
      (fsMultiQueryS qepC qR B0) cCoin R₁ R₂
    have hcCoinS :
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW
          (Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaOpS B0)
          Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaSampS
          (fsMultiQueryS qepC qR B0) cCoin ≤ 20 := by
      simp [cCoin, Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW,
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.exprSizeW,
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaSampS]
    have hsS_eq : Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaSampS = ckaSampS := rfl
    have hSize :
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW
          (Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaOpS B0)
          Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaSampS
          (fsMultiQueryS qepC qR B0) Rbranch.init +
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW
          (Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaOpS B0)
          Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaSampS
          (fsMultiQueryS qepC qR B0) Rbranch.handle +
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW
          (Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaOpS B0)
          Computational.Proofs.SessionCostedFig8.BundlesAuxSize.ckaSampS
          (fsMultiQueryS qepC qR B0) Rbranch.finish + 400 ≤
          1400000 + 810 * bits (ratchetCostBudget q qepC) := by
      dsimp only [Rbranch, ckaCoinBranchDFRed]
      rcases hcS with ⟨hciS, hchS, hcfS⟩
      rw [hciS, hchS, hcfS]
      simp only [aux_compSizeW_eq, aux_ckaOpS_eq, hsS_eq] at hcCoinS ⊢
      omega
    have hLM : compListMNodes Rbranch.init + compListMNodes Rbranch.handle +
        compListMNodes Rbranch.finish ≤ 50 := by
      change compListMNodes (coinBranchRed cCoin R₁ R₂).init +
          compListMNodes (coinBranchRed cCoin R₁ R₂).handle +
          compListMNodes (coinBranchRed cCoin R₁ R₂).finish ≤ 50
      rcases coinBranchRed_compListMNodes cCoin R₁ R₂ with ⟨h1, h2, h3⟩
      have h0 : compListMNodes cCoin = 0 := rfl
      rw [h1, h2, h3, h0]
      omega
    have hQC : compQueryCount Rbranch.init + compQueryCount Rbranch.handle +
        compQueryCount Rbranch.finish ≤ 60 := by
      change compQueryCount (coinBranchRed cCoin R₁ R₂).init +
          compQueryCount (coinBranchRed cCoin R₁ R₂).handle +
          compQueryCount (coinBranchRed cCoin R₁ R₂).finish ≤ 60
      rcases coinBranchRed_compQueryCount cCoin R₁ R₂ with ⟨h1, h2, h3⟩
      have h0 : compQueryCount cCoin = 0 := rfl
      rw [h1, h2, h3, h0]
      omega
    exact compileFsMultiDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam stage la j
      qepC qR B0 Rbranch q (2 * q)
      (hB0 := Nat.mul_le_mul_right _ (by omega)) (hparts := hparts)
      (hSize := hSize) (hQ := hQ) (hqOut := le_rfl)
      (hListM := hLM) (hqCount := hQC)
  · exact dummyFsStage2AtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q (2 * q)

end Stage2FsMultiAtomicProgs

end

end Computational.Proofs.SessionCostedFig8.DFProgFsStage2Bounds

-- AUTO-BRIDGE BEGIN
export Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs (
  coinBranchRed
  coinBranchRed_eval
  ckaCoinBranchDFRed
  ckaCoinBranchDFRed_eval
  ckaCoinBranchDFRed_eval_sampleT
  ckaCoinBranchDFRed_isQueryBoundP
  redFSAuthDFMultiAtomicProg
  redFSAuthDFMultiBucketAtomicProg
  redFSAuthDFPaperMultiAtomicProg
  redFSAuthDFShiftedPaperMultiAtomicProg
  redFSAuthDFShiftedDir2PaperMultiAtomicProg
  redFSAuthDFCasePaperMultiAtomicProg
  redFSAuthDFPaperMultiBucketAtomicProg
  redFSAuthDFPaperMultiBucketAtomicProg_eq_compile
)
-- AUTO-BRIDGE END

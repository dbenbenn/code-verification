/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BundlesAdapters -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesCompilers -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesAuxSize -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8WeightedParts -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.FsAtomicBundles
import Computational.Proofs.ReductionDsl.FsAtomicOps
import Computational.Proofs.ReductionDsl.FSAEAD.HybridCosted
import Computational.Proofs.ReductionDsl.FSAEAD.HybridInv
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRed
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWireCosted
import Computational.Proofs.E2E.SessionAuthQueries
import Computational.Proofs.HeadlineV1.Stage2RouterHelpers
import VCVio.OracleComp.EvalDist.Measure
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Specifications.Reductions.ReductionDsl.Core
import Computational.Proofs.GameHop.Rnd

/-!
# Multi-Session to Single-Session Atomic FS-AEAD Router Compiler

Lowers multi-session `fsaeadMultiHeaderAdIface` reductions (`redFSAuthMultiStage2Prog`,
`redFSAuthDFMultiBucketProg`, `redFSAuthDFPaperMultiBucketProg`,
`redFSAuthDFShiftedPaperMultiProg`, `redFSAuthDFShiftedDir2PaperMultiProg`) over
`Bundles.fig8CkaOpsShallow` into single-session `ReductionDsl.fsaeadHeaderIface ℓ Pt` reductions
over `ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam`:
- Session `sIdx = j` is forwarded directly to external `fsaeadHeaderIface ℓ Pt`.
- When `stage = false` (`lSessAdv`), sessions `sIdx < j` are simulated lazily on the `slotSaltImpl`
  side (`hp N 0 la` + `slotSaltImpl false`) and sessions `sIdx > j` on the real side (`hp 0 0 la`),
  where `N = authHopCutoff maxForwardJumps qR la`.
- When `stage = true` (`lWireSessAdv`), sessions `sIdx < j` are simulated lazily at `hp N N la` and
  sessions `sIdx > j` on the `slotSaltImplNF` side (`hp N 0 la` + `slotSaltImplNF false`).-/

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

namespace Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase

/-! ## 1. Weighted Per-Query Cost and Size Functions (`fsMultiQueryC`, `fsMultiQueryS`) -/

/-- Weighted per-query cost bound for `compileFsMultiAtomic` and `compileFsMultiDFAtomic` on each
`FSHdrTag` oracle tag (linear in `bits qep`, `qR`, and `B0`). -/
@[expose] def fsMultiQueryC (qep qR B0 : ℕ) : FSHdrTag → ℕ
  | .tr => 2000000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0
  | .ch => 2000000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0
  | .cs => 50000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0
  | .cr => 50000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0
  | .dl => 3500000 + 6 * bits (qep + 1) + 2500 * qR + 10 * B0
  | .ij => 3500000 + 6 * bits (qep + 1) + 2500 * qR + 10 * B0

@[simp] theorem fsMultiQueryC_tr (qep qR B0 : ℕ) :
    fsMultiQueryC qep qR B0 .tr = 2000000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 := rfl

@[simp] theorem fsMultiQueryC_ch (qep qR B0 : ℕ) :
    fsMultiQueryC qep qR B0 .ch = 2000000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 := rfl

@[simp] theorem fsMultiQueryC_cs (qep qR B0 : ℕ) :
    fsMultiQueryC qep qR B0 .cs = 50000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 := rfl

@[simp] theorem fsMultiQueryC_cr (qep qR B0 : ℕ) :
    fsMultiQueryC qep qR B0 .cr = 50000 + 6 * bits (qep + 1) + 1500 * qR + 10 * B0 := rfl

@[simp] theorem fsMultiQueryC_dl (qep qR B0 : ℕ) :
    fsMultiQueryC qep qR B0 .dl = 3500000 + 6 * bits (qep + 1) + 2500 * qR + 10 * B0 := rfl

@[simp] theorem fsMultiQueryC_ij (qep qR B0 : ℕ) :
    fsMultiQueryC qep qR B0 .ij = 3500000 + 6 * bits (qep + 1) + 2500 * qR + 10 * B0 := rfl

/-- Weighted per-query AST size bound for `compileFsMultiAtomic` and `compileFsMultiDFAtomic`. -/
@[expose] def fsMultiQueryS (qep qR B0 : ℕ) : FSHdrTag → ℕ
  | _ => 12000 + 16 * bits (qep + qR + B0 + 1)

@[simp] theorem fsMultiQueryS_apply (qep qR B0 : ℕ) (g : FSHdrTag) :
    fsMultiQueryS qep qR B0 g = 12000 + 16 * bits (qep + qR + B0 + 1) := rfl

/-! ## 2. Per-Session Projection of a Multi-Session Public-Part FS-AEAD Adversary -/

/-- Project a multi-session public-part `MultiSessPubFsAdv Pt ℓ` onto session `j` by answering all
sessions `s ≠ j` with inert dummy replies (`none`) while forwarding session `j` and uniform coins.
Used for `QuerySubsumes` transfer of single-session query bounds and well-formedness predicates
from session `j` of `R.eval` to `(compileFsMulti{,DF}Atomic ... j ... R).eval`. -/
@[expose] def projSessPubFsAdv {Pt : Type} {ℓ : ℕ} (j : ℕ)
    (AdvPub : MultiSessPubFsAdv Pt ℓ) : FsAdv Pt ℓ :=
  let fsS := CryptoGames.FSAEAD.spec
    (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
    (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt)
  let impl : QueryImpl (unifSpec + multiSessSpec fsS) (OracleComp (unifSpec + fsS))
    | .inl n => (query (spec := unifSpec + fsS) (Sum.inl n) : OracleComp (unifSpec + fsS) _)
    | .inr ⟨s, q⟩ =>
      if s = j then
        (query (spec := unifSpec + fsS) (Sum.inr q) : OracleComp (unifSpec + fsS) _)
      else
        match q with
        | .inl (.inl (.inl (.inl (.inl _)))) => pure none
        | .inl (.inl (.inl (.inl (.inr _)))) => pure none
        | .inl (.inl (.inl (.inr _))) => pure none
        | .inl (.inl (.inr _)) => pure none
        | .inl (.inr _) => pure none
        | .inr _ => pure none
  simulateQ impl AdvPub

/-! ## 3. Generic Same-Signature State-Threading Query Substitution (`substQueryRed`) -/

@[expose] def exprWk1 {S : Sig} {O : Ops S} {a t : Ty S} {Γ : List (Ty S)}
    (e : Expr O Γ t) : Expr O (a :: Γ) t :=
  e.renameM fun ⦃_⦄ v => .succ v

@[expose] def liftEnv1 {S : Sig} {O : Ops S} {a : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) :
    ∀ ⦃u⦄, Var (a :: Γ) u → Expr O (a :: Δ) u
  | _, .zero => .var .zero
  | _, .succ w => exprWk1 (envMap w)

@[expose] def liftEnv2 {S : Sig} {O : Ops S} {a b : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) :
    ∀ ⦃u⦄, Var (a :: b :: Γ) u → Expr O (a :: b :: Δ) u
  | _, .zero => .var .zero
  | _, .succ .zero => .var (.succ .zero)
  | _, .succ (.succ w) => exprWk1 (exprWk1 (envMap w))

@[expose] def liftEnvFst {S : Sig} {O : Ops S} {a rStTy : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) :
    ∀ ⦃u⦄, Var (a :: Γ) u → Expr O (.prod a rStTy :: Δ) u
  | _, .zero => .fst (.var .zero)
  | _, .succ w => exprWk1 (envMap w)

@[expose] def liftEnvFold {S : Sig} {O : Ops S} {a b rStTy : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) :
    ∀ ⦃u⦄, Var (a :: b :: Γ) u → Expr O (a :: .prod b rStTy :: Δ) u
  | _, .zero => .var .zero
  | _, .succ .zero => .fst (.var (.succ .zero))
  | _, .succ (.succ w) => exprWk1 (exprWk1 (envMap w))

@[expose] def liftEnvPred2 {S : Sig} {O : Ops S} {a x : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) :
    ∀ ⦃u⦄, Var (a :: Γ) u → Expr O (a :: x :: Δ) u
  | _, .zero => .var .zero
  | _, .succ w => exprWk1 (exprWk1 (envMap w))

@[expose] def liftEnvMk3 {S : Sig} {O : Ops S} {a y x : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) :
    ∀ ⦃u⦄, Var (a :: Γ) u → Expr O (y :: a :: x :: Δ) u
  | _, .zero => .var (.succ .zero)
  | _, .succ w => exprWk1 (exprWk1 (exprWk1 (envMap w)))

@[expose] def substExpr {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) :
    {t : Ty S} → Expr O Γ t → Expr O Δ t
  | _, .var v => envMap v
  | _, .unit => .unit
  | _, .bool b => .bool b
  | _, .nat n => .nat n
  | _, .add a b => .add (substExpr envMap a) (substExpr envMap b)
  | _, .sub a b => .sub (substExpr envMap a) (substExpr envMap b)
  | _, .mulK k a => .mulK k (substExpr envMap a)
  | _, .divK k a => .divK k (substExpr envMap a)
  | _, .modK k a => .modK k (substExpr envMap a)
  | _, .lt a b => .lt (substExpr envMap a) (substExpr envMap b)
  | _, .eqN a b => .eqN (substExpr envMap a) (substExpr envMap b)
  | _, .not a => .not (substExpr envMap a)
  | _, .and a b => .and (substExpr envMap a) (substExpr envMap b)
  | _, .ite c a b => .ite (substExpr envMap c) (substExpr envMap a) (substExpr envMap b)
  | _, .pair a b => .pair (substExpr envMap a) (substExpr envMap b)
  | _, .fst a => .fst (substExpr envMap a)
  | _, .snd a => .snd (substExpr envMap a)
  | _, .inl a => .inl (substExpr envMap a)
  | _, .inr a => .inr (substExpr envMap a)
  | _, .none => .none
  | _, .some a => .some (substExpr envMap a)
  | _, .caseOpt e n s =>
    .caseOpt (substExpr envMap e) (substExpr envMap n) (substExpr (liftEnv1 envMap) s)
  | _, .caseSum e l r =>
    .caseSum (substExpr envMap e) (substExpr (liftEnv1 envMap) l) (substExpr (liftEnv1 envMap) r)
  | _, .letE e b =>
    .letE (substExpr envMap e) (substExpr (liftEnv1 envMap) b)
  | _, .op o a => .op o (substExpr envMap a)
  | _, .nil => .nil
  | _, .cons x l => .cons (substExpr envMap x) (substExpr envMap l)
  | _, .len l => .len (substExpr envMap l)
  | _, .take n l => .take (substExpr envMap n) (substExpr envMap l)
  | _, .appendL K a b => .appendL K (substExpr envMap a) (substExpr envMap b)
  | _, .findB K l p => .findB K (substExpr envMap l) (substExpr (liftEnv1 envMap) p)
  | _, .anyB K l p => .anyB K (substExpr envMap l) (substExpr (liftEnv1 envMap) p)
  | _, .mapB K l f => .mapB K (substExpr envMap l) (substExpr (liftEnv1 envMap) f)
  | _, .foldrB K l z f =>
    .foldrB K (substExpr envMap l) (substExpr envMap z) (substExpr (liftEnv2 envMap) f)
  | _, .tconst a => .tconst (substExpr envMap a)
  | _, .tget m i => .tget (substExpr envMap m) (substExpr envMap i)
  | _, .tset m i a => .tset (substExpr envMap m) (substExpr envMap i) (substExpr envMap a)

theorem expr_renameM_cost {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) (e : Expr O Γ t) :
    (e.renameM f).cost = e.cost := by
  induction e generalizing Δ <;> simp [Expr.renameM, Expr.cost, *]

theorem exprWk1_cost {S : Sig} {O : Ops S} {a t : Ty S} {Γ : List (Ty S)}
    (e : Expr O Γ t) : (exprWk1 (a := a) e).cost = e.cost :=
  expr_renameM_cost _ e

theorem expr_cost_pos {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) : 1 ≤ e.cost :=
  CryptoVerification.E2E.Costed.Expr.one_le_cost e

theorem envMap_liftEnv1_cost {S : Sig} {O : Ops S} {a : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (h : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: Γ) u), (liftEnv1 envMap v).cost ≤ 2
  | _, .zero => by simp [liftEnv1, Expr.cost]
  | _, .succ w => by simp [liftEnv1, exprWk1_cost]; exact h w

theorem envMap_liftEnv2_cost {S : Sig} {O : Ops S} {a b : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (h : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: b :: Γ) u), (liftEnv2 envMap v).cost ≤ 2
  | _, .zero => by simp [liftEnv2, Expr.cost]
  | _, .succ .zero => by simp [liftEnv2, Expr.cost]
  | _, .succ (.succ w) => by simp [liftEnv2, exprWk1_cost]; exact h w

theorem substExpr_cost_le {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2)
    (e : Expr O Γ t) :
    (substExpr envMap e).cost ≤ 2 * e.cost := by
  induction e generalizing Δ with
  | var v => simpa [substExpr, Expr.cost] using hEnv v
  | caseOpt e n s ihe ihn ihs =>
    have h1 := ihe envMap hEnv
    have h2 := ihn envMap hEnv
    have h3 := ihs (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv)
    simp only [substExpr, Expr.cost]; omega
  | caseSum e l r ihe ihl ihr =>
    have h1 := ihe envMap hEnv
    have h2 := ihl (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv)
    have h3 := ihr (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv)
    simp only [substExpr, Expr.cost]; omega
  | letE e b ihe ihb =>
    have h1 := ihe envMap hEnv
    have h2 := ihb (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv)
    simp only [substExpr, Expr.cost]; omega
  | findB K l p ihl ihp =>
    have h1 := ihl envMap hEnv
    have h2 := ihp (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv)
    simp only [substExpr, Expr.cost]
    calc (substExpr envMap l).cost + K * ((substExpr (liftEnv1 envMap) p).cost + 1) + 1
        ≤ 2 * l.cost + K * (2 * p.cost + 1) + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add h1 (Nat.mul_le_mul_left K (by omega))) 1
      _ ≤ 2 * l.cost + K * (2 * (p.cost + 1)) + 2 := by
          have : K * (2 * p.cost + 1) ≤ K * (2 * (p.cost + 1)) := Nat.mul_le_mul_left K (by omega)
          omega
      _ = 2 * (l.cost + K * (p.cost + 1) + 1) := by ring
  | anyB K l p ihl ihp =>
    have h1 := ihl envMap hEnv
    have h2 := ihp (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv)
    simp only [substExpr, Expr.cost]
    calc (substExpr envMap l).cost + K * ((substExpr (liftEnv1 envMap) p).cost + 1) + 1
        ≤ 2 * l.cost + K * (2 * p.cost + 1) + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add h1 (Nat.mul_le_mul_left K (by omega))) 1
      _ ≤ 2 * l.cost + K * (2 * (p.cost + 1)) + 2 := by
          have : K * (2 * p.cost + 1) ≤ K * (2 * (p.cost + 1)) := Nat.mul_le_mul_left K (by omega)
          omega
      _ = 2 * (l.cost + K * (p.cost + 1) + 1) := by ring
  | mapB K l f ihl ihf =>
    have h1 := ihl envMap hEnv
    have h2 := ihf (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv)
    simp only [substExpr, Expr.cost]
    calc (substExpr envMap l).cost + K * ((substExpr (liftEnv1 envMap) f).cost + 1) + 1
        ≤ 2 * l.cost + K * (2 * f.cost + 1) + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add h1 (Nat.mul_le_mul_left K (by omega))) 1
      _ ≤ 2 * l.cost + K * (2 * (f.cost + 1)) + 2 := by
          have : K * (2 * f.cost + 1) ≤ K * (2 * (f.cost + 1)) := Nat.mul_le_mul_left K (by omega)
          omega
      _ = 2 * (l.cost + K * (f.cost + 1) + 1) := by ring
  | foldrB K l z f ihl ihz ihf =>
    have h1 := ihl envMap hEnv
    have h2 := ihz envMap hEnv
    have h3 := ihf (liftEnv2 envMap) (envMap_liftEnv2_cost hEnv)
    simp only [substExpr, Expr.cost]
    calc (substExpr envMap l).cost + (substExpr envMap z).cost +
          K * ((substExpr (liftEnv2 envMap) f).cost + 1) + 1
        ≤ 2 * l.cost + 2 * z.cost + K * (2 * f.cost + 1) + 1 := by
          have := Nat.mul_le_mul_left K (show (substExpr (liftEnv2 envMap) f).cost + 1 ≤ 2 * f.cost + 1 by omega)
          omega
      _ ≤ 2 * l.cost + 2 * z.cost + K * (2 * (f.cost + 1)) + 2 := by
          have : K * (2 * f.cost + 1) ≤ K * (2 * (f.cost + 1)) := Nat.mul_le_mul_left K (by omega)
          omega
      _ = 2 * (l.cost + z.cost + K * (f.cost + 1) + 1) := by ring
  | op o a iha =>
    have h1 := iha envMap hEnv
    simp only [substExpr, Expr.cost]; omega
  | unit | bool _ | nat _ | none | nil =>
    simp only [substExpr, Expr.cost]; omega
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2
  | and _ _ ih1 ih2 | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2
  | appendL _ _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    have h1 := ih1 envMap hEnv
    have h2 := ih2 envMap hEnv
    simp only [substExpr, Expr.cost]; omega
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    have h1 := ih envMap hEnv
    simp only [substExpr, Expr.cost]; omega
  | ite _ _ _ ih1 ih2 ih3 | tset _ _ _ ih1 ih2 ih3 =>
    have h1 := ih1 envMap hEnv
    have h2 := ih2 envMap hEnv
    have h3 := ih3 envMap hEnv
    simp only [substExpr, Expr.cost]; omega

@[expose] def substNoQueryComp {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s)) :
    {Γ Δ : List (Ty S)} → {t : Ty S} →
      (∀ ⦃u⦄, Var Γ u → Expr O Δ u) →
      (c : Comp O I₁ Γ t) →
      c.queries (fun _ => 1) (fun _ => 0) = 0 →
      Comp O I₂ Δ t
  | _, _, _, envMap, .ret e, _ => .ret (substExpr envMap e)
  | _, _, _, envMap, .bind c k, h =>
    .bind
      (substNoQueryComp mapSamp envMap c (by simp [Comp.queries] at h; omega))
      (substNoQueryComp mapSamp (liftEnv1 envMap) k (by simp [Comp.queries] at h; omega))
  | _, _, _, envMap, .ite b c d, h =>
    .ite (substExpr envMap b)
      (substNoQueryComp mapSamp envMap c (by simp [Comp.queries] at h; omega))
      (substNoQueryComp mapSamp envMap d (by simp [Comp.queries] at h; omega))
  | _, _, _, envMap, .caseOpt e n s, h =>
    .caseOpt (substExpr envMap e)
      (substNoQueryComp mapSamp envMap n (by simp [Comp.queries] at h; omega))
      (substNoQueryComp mapSamp (liftEnv1 envMap) s (by simp [Comp.queries] at h; omega))
  | _, _, _, envMap, .caseSum e l r, h =>
    .caseSum (substExpr envMap e)
      (substNoQueryComp mapSamp (liftEnv1 envMap) l (by simp [Comp.queries] at h; omega))
      (substNoQueryComp mapSamp (liftEnv1 envMap) r (by simp [Comp.queries] at h; omega))
  | _, _, _, envMap, .sample s e, _ =>
    mapSamp s (substExpr envMap e)
  | _, _, _, _, .query _ _, h => by
    exfalso; simp [Comp.queries] at h
  | _, _, _, envMap, .iter 0 e _, _ =>
    .iter 0 (substExpr envMap e) (.ret (.var .zero))
  | _, _, _, envMap, .iter (n + 1) e body, h =>
    .iter (n + 1) (substExpr envMap e)
      (substNoQueryComp mapSamp (liftEnv1 envMap) body (by
        simp [Comp.queries] at h; omega))
  | _, _, _, envMap, .foldM 0 l z _, _ =>
    .foldM 0 (substExpr envMap l) (substExpr envMap z) (.ret (.var (.succ .zero)))
  | _, _, _, envMap, .foldM (K + 1) l z f, h =>
    .foldM (K + 1) (substExpr envMap l) (substExpr envMap z)
      (substNoQueryComp mapSamp (liftEnv2 envMap) f (by
        simp [Comp.queries] at h; omega))
  | _, _, _, envMap, .findM 0 l _, _ =>
    .findM 0 (substExpr envMap l) (.ret (.bool false))
  | _, _, _, envMap, .findM (K + 1) l p, h =>
    .findM (K + 1) (substExpr envMap l)
      (substNoQueryComp mapSamp (liftEnv1 envMap) p (by
        simp [Comp.queries] at h; omega))
  | _, _, _, envMap, .anyM 0 l _, _ =>
    .anyM 0 (substExpr envMap l) (.ret (.bool false))
  | _, _, _, envMap, .anyM (K + 1) l p, h =>
    .anyM (K + 1) (substExpr envMap l)
      (substNoQueryComp mapSamp (liftEnv1 envMap) p (by
        simp [Comp.queries] at h; omega))
  | _, _, _, _, .mapM 0 _ _, _ =>
    .ret .nil
  | _, _, _, envMap, .mapM (K + 1) l f, h =>
    .mapM (K + 1) (substExpr envMap l)
      (substNoQueryComp mapSamp (liftEnv1 envMap) f (by
        simp [Comp.queries] at h; omega))
  | _, _, _, _, .consumeFirstM 0 _ _ _, _ =>
    .ret (.pair (.bool false) .nil)
  | _, _, _, envMap, .consumeFirstM (K + 1) l p mk, h =>
    .consumeFirstM (K + 1) (substExpr envMap l)
      (substNoQueryComp mapSamp (liftEnv1 envMap) p (by
        simp [Comp.queries] at h; omega))
      (substExpr (liftEnv1 envMap) mk)

@[expose] def renEmpty {S : Sig} {Γ : List (Ty S)} : ∀ ⦃u⦄, Var [] u → Var Γ u
  | _, v => nomatch v

@[expose] def renId1 {S : Sig} {a : Ty S} {Γ : List (Ty S)} :
    ∀ ⦃u⦄, Var [a] u → Var (a :: Γ) u
  | _, .zero => .zero

@[expose] def renId2 {S : Sig} {a b : Ty S} {Γ : List (Ty S)} :
    ∀ ⦃u⦄, Var [a, b] u → Var (a :: b :: Γ) u
  | _, .zero => .zero
  | _, .succ .zero => .succ .zero

@[expose] def renSwap2 {S : Sig} {a b : Ty S} {Γ : List (Ty S)} :
    ∀ ⦃u⦄, Var [a, b] u → Var (b :: a :: Γ) u
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero

@[expose] def renUnit2 {S : Sig} {a b : Ty S} {Γ : List (Ty S)} :
    ∀ ⦃u⦄, Var [.unit, a] u → Var (a :: b :: .unit :: Γ) u
  | _, .zero => .succ (.succ .zero)
  | _, .succ .zero => .zero

@[expose] def envId1 {S : Sig} {O : Ops S} {a : Ty S} :
    ∀ ⦃u⦄, Var [a] u → Expr O [a] u
  | _, .zero => .var .zero

@[expose] def envFst2 {S : Sig} {O : Ops S} {a b r : Ty S} :
    ∀ ⦃u⦄, Var [a, b] u → Expr O [.prod a r, b] u
  | _, .zero => .fst (.var .zero)
  | _, .succ .zero => .var (.succ .zero)

@[expose] def envSwapFst2 {S : Sig} {O : Ops S} {a b r : Ty S} :
    ∀ ⦃u⦄, Var [a, b] u → Expr O [a, .prod b r] u
  | _, .zero => .var .zero
  | _, .succ .zero => .fst (.var (.succ .zero))

@[expose] def callBinaryComp {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {a b c : Ty S} {Δ : List (Ty S)}
    (m : Comp O I [a, b] c) : Comp O I (.prod a b :: Δ) c :=
  .bind (.ret (.snd (.var .zero)))
    (.bind (.ret (.fst (.var (.succ .zero))))
      (m.renameM renId2))

@[expose] def substQueryComp {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {rStTy : Ty S}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy)) :
    {Γ Δ : List (Ty S)} → {t : Ty S} →
      (∀ ⦃u⦄, Var Γ u → Expr O Δ u) →
      Expr O Δ rStTy →
      Comp O I₁ Γ t →
      Comp O I₂ Δ (.prod t rStTy)
  | _, _, _, envMap, rExpr, .ret e =>
    .ret (.pair (substExpr envMap e) rExpr)
  | _, _, _, envMap, rExpr, .bind c k =>
    .bind (substQueryComp mapSamp qImpl envMap rExpr c)
      (substQueryComp mapSamp qImpl (liftEnvFst envMap) (.snd (.var .zero)) k)
  | _, _, _, envMap, rExpr, .ite b c d =>
    .ite (substExpr envMap b)
      (substQueryComp mapSamp qImpl envMap rExpr c)
      (substQueryComp mapSamp qImpl envMap rExpr d)
  | _, _, _, envMap, rExpr, .caseOpt e n s =>
    .caseOpt (substExpr envMap e)
      (substQueryComp mapSamp qImpl envMap rExpr n)
      (substQueryComp mapSamp qImpl (liftEnv1 envMap) (exprWk1 rExpr) s)
  | _, _, _, envMap, rExpr, .caseSum e l r =>
    .caseSum (substExpr envMap e)
      (substQueryComp mapSamp qImpl (liftEnv1 envMap) (exprWk1 rExpr) l)
      (substQueryComp mapSamp qImpl (liftEnv1 envMap) (exprWk1 rExpr) r)
  | _, _, _, envMap, rExpr, .sample s e =>
    .bind (mapSamp s (substExpr envMap e))
      (.ret (.pair (.var .zero) (exprWk1 rExpr)))
  | _, _, _, envMap, rExpr, .query g e =>
    .bind (.ret (.pair (substExpr envMap e) rExpr))
      (callBinaryComp (qImpl g))
  | _, _, _, envMap, rExpr, .iter n e body =>
    .iter n (.pair (substExpr envMap e) rExpr)
      (substQueryComp mapSamp qImpl (liftEnvFst envMap) (.snd (.var .zero)) body)
  | _, _, _, envMap, rExpr, .foldM K l z f =>
    .foldM K (substExpr envMap l) (.pair (substExpr envMap z) rExpr)
      (substQueryComp mapSamp qImpl (liftEnvFold envMap) (.snd (.var (.succ .zero))) f)
  | _, _, _, _, rExpr, .findM 0 _ _ =>
    .ret (.pair .none rExpr)
  | _, _, _, envMap, rExpr, .findM (K + 1) l p =>
    if hc0 : (Comp.findM (K + 1) l p).queries (fun _ => 1) (fun _ => 0) = 0 then
      .bind (substNoQueryComp mapSamp envMap (.findM (K + 1) l p) hc0)
        (.ret (.pair (.var .zero) (exprWk1 rExpr)))
    else
      .foldM (K + 1) (substExpr envMap l) (.pair .none rExpr)
        (.caseOpt (.fst (.var (.succ .zero)))
          (.bind
            (substQueryComp mapSamp qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p)
            (.ret (.pair
              (.ite (.fst (.var .zero)) (.some (.var (.succ .zero))) .none)
              (.snd (.var .zero)))))
          (.ret (.var (.succ (.succ .zero)))))
  | _, _, _, _, rExpr, .anyM 0 _ _ =>
    .ret (.pair (.bool false) rExpr)
  | _, _, _, envMap, rExpr, .anyM (K + 1) l p =>
    if hc0 : (Comp.anyM (K + 1) l p).queries (fun _ => 1) (fun _ => 0) = 0 then
      .bind (substNoQueryComp mapSamp envMap (.anyM (K + 1) l p) hc0)
        (.ret (.pair (.var .zero) (exprWk1 rExpr)))
    else
      .foldM (K + 1) (substExpr envMap l) (.pair (.bool false) rExpr)
        (.ite (.fst (.var (.succ .zero)))
          (.ret (.var (.succ .zero)))
          (substQueryComp mapSamp qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p))
  | _, _, _, _, rExpr, .mapM 0 _ _ =>
    .ret (.pair .nil rExpr)
  | _, _, _, envMap, rExpr, .mapM (K + 1) l f =>
    if hc0 : (Comp.mapM (K + 1) l f).queries (fun _ => 1) (fun _ => 0) = 0 then
      .bind (substNoQueryComp mapSamp envMap (.mapM (K + 1) l f) hc0)
        (.ret (.pair (.var .zero) (exprWk1 rExpr)))
    else
      .bind
        (.foldM (K + 1) (substExpr envMap l) (.pair .nil rExpr)
          (.bind
            (substQueryComp mapSamp qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) f)
            (.ret (.pair
              (.cons (.fst (.var .zero)) (.fst (.var (.succ (.succ .zero)))))
              (.snd (.var .zero))))))
        (.bind
          (.foldM (K + 1) (.fst (.var .zero)) .nil
            (.ret (.cons (.var .zero) (.var (.succ .zero)))))
          (.ret (.pair (.var .zero) (.snd (.var (.succ .zero))))))
  | _, _, _, _, rExpr, .consumeFirstM 0 _ _ _ =>
    .ret (.pair (.pair (.bool false) .nil) rExpr)
  | _, _, _, envMap, rExpr, .consumeFirstM (K + 1) l p mk =>
    if hc0 : (Comp.consumeFirstM (K + 1) l p mk).queries (fun _ => 1) (fun _ => 0) = 0 then
      .bind (substNoQueryComp mapSamp envMap (.consumeFirstM (K + 1) l p mk) hc0)
        (.ret (.pair (.var .zero) (exprWk1 rExpr)))
    else
      .bind
        (.foldM (K + 1) (substExpr envMap l) (.pair (.pair (.bool false) .nil) rExpr)
          (.ite (.fst (.fst (.var (.succ .zero))))
            (.ret (.pair
              (.pair (.bool true) (.cons (.var .zero) (.snd (.fst (.var (.succ .zero))))))
              (.snd (.var (.succ .zero)))))
            (.bind
              (substQueryComp mapSamp qImpl (liftEnvPred2 envMap) (.snd (.var (.succ .zero))) p)
              (.ite (.fst (.var .zero))
                (.ret (.pair
                  (.pair (.bool true)
                    (.cons
                      (substExpr (liftEnvMk3 envMap) mk)
                      (.snd (.fst (.var (.succ (.succ .zero)))))))
                  (.snd (.var .zero))))
                (.ret (.pair
                  (.pair (.bool false)
                    (.cons (.var (.succ .zero)) (.snd (.fst (.var (.succ (.succ .zero)))))))
                  (.snd (.var .zero))))))))
        (.bind
          (.foldM (K + 1) (.snd (.fst (.var .zero))) .nil
            (.ret (.cons (.var .zero) (.var (.succ .zero)))))
          (.ret (.pair
            (.pair (.fst (.fst (.var (.succ .zero)))) (.var .zero))
            (.snd (.var (.succ .zero))))))

@[expose] def substQueryRed {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {κ : Type} {G : OracleSpec κ} {C_game : GameCodec S G}
    {rIn aIn aOut out rStTy : Ty S}
    (rInit : Expr O [rIn] rStTy)
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (R : CostedReduction O I₁ G C_game rIn aIn aOut out) :
    CostedReduction O I₂ G C_game rIn aIn aOut out where
  σ := .prod R.σ rStTy
  init :=
    .bind
      (substQueryComp mapSamp qImpl envId1 rInit R.init)
      (.ret (.pair (.fst (.fst (.var .zero)))
        (.pair (.snd (.fst (.var .zero))) (.snd (.var .zero)))))
  handle :=
    .bind
      (substQueryComp mapSamp qImpl envFst2 (.snd (.var .zero)) R.handle)
      (.ret (.pair (.fst (.fst (.var .zero)))
        (.pair (.snd (.fst (.var .zero))) (.snd (.var .zero)))))
  finish :=
    .bind
      (substQueryComp mapSamp qImpl envFst2 (.snd (.var .zero)) R.finish)
      (.ret (.fst (.var .zero)))

@[expose] def evalEnvMap {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (ρ : Env Δ) : Env Γ :=
  match Γ with
  | [] => .nil
  | _ :: _ => .cons ((envMap .zero).eval ρ) (evalEnvMap (fun ⦃_⦄ v => envMap (.succ v)) ρ)

theorem envGet_evalEnvMap {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (ρ : Env Δ) {u : Ty S} (v : Var Γ u) :
    (evalEnvMap envMap ρ).get v = (envMap v).eval ρ := by
  induction v with
  | zero => rfl
  | succ w ih => exact ih (fun ⦃_⦄ x => envMap (.succ x))

@[expose] def envRen {S : Sig} {Γ Δ : List (Ty S)}
    (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) (ρ : Env Δ) : Env Γ :=
  match Γ with
  | [] => .nil
  | _ :: _ => .cons (ρ.get (f .zero)) (envRen (fun ⦃_⦄ v => f (.succ v)) ρ)

theorem envGet_envRen {S : Sig} {Γ Δ : List (Ty S)}
    (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) (ρ : Env Δ) {u : Ty S} (v : Var Γ u) :
    (envRen f ρ).get v = ρ.get (f v) := by
  induction v with
  | zero => rfl
  | succ w ih => exact ih (fun ⦃_⦄ x => f (.succ x))

theorem envRen_succ {S : Sig} {a : Ty S} :
    ∀ {Γ Δ : List (Ty S)} (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) (x : a.denote) (ρ : Env Δ),
      envRen (fun ⦃_⦄ v => (f v).succ) (.cons x ρ) = envRen f ρ
  | [], _, _, _, _ => rfl
  | _ :: _, _, f, x, ρ =>
    congrArg (Env.cons _) (envRen_succ (fun ⦃_⦄ v => f (.succ v)) x ρ)

theorem envRen_liftRen {S : Sig} {a : Ty S} {Γ Δ : List (Ty S)}
    (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) (x : a.denote) (ρ : Env Δ) :
    envRen (liftRen f) (.cons x ρ) = .cons x (envRen f ρ) := by
  simp [envRen, liftRen, envRen_succ]

theorem expr_renameM_eval {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (e : Expr O Γ t) (ρ : Env Δ) :
    (e.renameM f).eval ρ = e.eval (envRen f ρ) := by
  induction e generalizing Δ with
  | var v => symm; exact envGet_envRen f ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2
  | and _ _ ih1 ih2 | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2
  | appendL _ _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    simp [Expr.renameM, Expr.eval, ih1, ih2]
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | op _ _ ih | len _ ih | tconst _ ih =>
    simp [Expr.renameM, Expr.eval, ih]
  | ite _ _ _ ih1 ih2 ih3 | tset _ _ _ ih1 ih2 ih3 =>
    simp [Expr.renameM, Expr.eval, ih1, ih2, ih3]
  | caseOpt e n s ihe ihn ihs =>
    simp only [Expr.renameM, Expr.eval, ihe, ihn]
    cases e.eval _ <;> simp [ihs, envRen_liftRen]
  | caseSum e l r ihe ihl ihr =>
    simp only [Expr.renameM, Expr.eval, ihe]
    cases e.eval _ <;> simp [ihl, ihr, envRen_liftRen]
  | letE e b ihe ihb =>
    simp [Expr.renameM, Expr.eval, ihe, ihb, envRen_liftRen]
  | findB K l p ihl ihp =>
    simp only [Expr.renameM, Expr.eval, ihl]
    congr 1; ext x; simp [ihp, envRen_liftRen]
  | anyB K l p ihl ihp =>
    simp only [Expr.renameM, Expr.eval, ihl]
    congr 1; ext x; simp [ihp, envRen_liftRen]
  | mapB K l f' ihl ihf =>
    simp only [Expr.renameM, Expr.eval, ihl]
    congr 1; ext x; simp [ihf, envRen_liftRen]
  | foldrB K l z f' ihl ihz ihf =>
    simp only [Expr.renameM, Expr.eval, ihl, ihz]
    congr 1; ext x acc; simp [ihf, envRen_liftRen]

theorem envRen_id {S : Sig} :
    ∀ {Γ : List (Ty S)} (ρ : Env Γ), envRen (fun ⦃_⦄ (v : Var Γ _) => v) ρ = ρ
  | [], .nil => rfl
  | _ :: _, .cons y ρ =>
    by dsimp only [envRen]; exact congrArg (Env.cons y) ((envRen_succ (fun ⦃_⦄ v => v) y ρ).trans (envRen_id ρ))

theorem envRen_var_succ {S : Sig} {a : Ty S} {Γ : List (Ty S)}
    (x : a.denote) (ρ : Env Γ) :
    envRen (fun ⦃_⦄ (v : Var Γ _) => v.succ) (.cons x ρ) = ρ :=
  (envRen_succ (fun ⦃_⦄ v => v) x ρ).trans (envRen_id ρ)

theorem exprWk1_eval {S : Sig} {O : Ops S} {a t : Ty S} {Γ : List (Ty S)}
    (e : Expr O Γ t) (x : a.denote) (ρ : Env Γ) :
    (exprWk1 e).eval (.cons x ρ) = e.eval ρ := by
  rw [exprWk1, expr_renameM_eval, envRen_var_succ]

theorem evalEnvMap_wk1 {S : Sig} {O : Ops S} {a : Ty S} :
    ∀ {Γ Δ : List (Ty S)} (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (x : a.denote) (ρ : Env Δ),
      evalEnvMap (fun ⦃_⦄ v => exprWk1 (envMap v)) (.cons x ρ) = evalEnvMap envMap ρ
  | [], _, _, _, _ => rfl
  | _ :: _, _, envMap, x, ρ => by
    simp only [evalEnvMap, exprWk1_eval]
    exact congrArg (Env.cons _) (evalEnvMap_wk1 (fun ⦃_⦄ v => envMap (.succ v)) x ρ)

theorem evalEnvMap_liftEnv1 {S : Sig} {O : Ops S} {a : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (x : a.denote) (ρ : Env Δ) :
    evalEnvMap (liftEnv1 envMap) (.cons x ρ) = .cons x (evalEnvMap envMap ρ) := by
  simp only [evalEnvMap, liftEnv1, evalEnvMap_wk1]; rfl

theorem evalEnvMap_liftEnv2 {S : Sig} {O : Ops S} {a b : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (x : a.denote) (y : b.denote) (ρ : Env Δ) :
    evalEnvMap (liftEnv2 envMap) (.cons x (.cons y ρ)) = .cons x (.cons y (evalEnvMap envMap ρ)) := by
  simp only [evalEnvMap, liftEnv2, evalEnvMap_wk1]; rfl

theorem evalEnvMap_liftEnvFst {S : Sig} {O : Ops S} {a rStTy : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (xr : a.denote × rStTy.denote) (ρ : Env Δ) :
    evalEnvMap (liftEnvFst envMap) (.cons xr ρ) = .cons xr.1 (evalEnvMap envMap ρ) := by
  simp only [evalEnvMap, liftEnvFst, evalEnvMap_wk1]; rfl

theorem evalEnvMap_liftEnvFold {S : Sig} {O : Ops S} {a b rStTy : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
    (x : a.denote) (br : b.denote × rStTy.denote) (ρ : Env Δ) :
    evalEnvMap (liftEnvFold envMap) (.cons x (.cons br ρ)) =
      .cons x (.cons br.1 (evalEnvMap envMap ρ)) := by
  simp only [evalEnvMap, liftEnvFold, evalEnvMap_wk1]; rfl

theorem evalEnvMap_liftEnvPred2 {S : Sig} {O : Ops S} {a xTy : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) (x : a.denote) (y : xTy.denote) (ρ : Env Δ) :
    evalEnvMap (liftEnvPred2 envMap) (.cons x (.cons y ρ)) = .cons x (evalEnvMap envMap ρ) := by
  simp only [evalEnvMap, liftEnvPred2, evalEnvMap_wk1]; rfl

theorem evalEnvMap_liftEnvMk3 {S : Sig} {O : Ops S} {a yTy xTy : Ty S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
    (z : yTy.denote) (x : a.denote) (y : xTy.denote) (ρ : Env Δ) :
    evalEnvMap (liftEnvMk3 envMap) (.cons z (.cons x (.cons y ρ))) =
      .cons x (evalEnvMap envMap ρ) := by
  simp only [evalEnvMap, liftEnvMk3, evalEnvMap_wk1]; rfl

theorem substExpr_eval {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u) {t : Ty S} (e : Expr O Γ t) (ρ : Env Δ) :
    (substExpr envMap e).eval ρ = e.eval (evalEnvMap envMap ρ) := by
  induction e generalizing Δ with
  | var v => symm; exact envGet_evalEnvMap envMap ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2
  | and _ _ ih1 ih2 | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2
  | appendL _ _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    simp [substExpr, Expr.eval, ih1, ih2]
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | op _ _ ih | len _ ih | tconst _ ih =>
    simp [substExpr, Expr.eval, ih]
  | ite _ _ _ ih1 ih2 ih3 | tset _ _ _ ih1 ih2 ih3 =>
    simp [substExpr, Expr.eval, ih1, ih2, ih3]
  | caseOpt e n s ihe ihn ihs =>
    simp only [substExpr, Expr.eval, ihe, ihn]
    cases e.eval _ <;> simp [ihs, evalEnvMap_liftEnv1]
  | caseSum e l r ihe ihl ihr =>
    simp only [substExpr, Expr.eval, ihe]
    cases e.eval _ <;> simp [ihl, ihr, evalEnvMap_liftEnv1]
  | letE e b ihe ihb =>
    simp [substExpr, Expr.eval, ihe, ihb, evalEnvMap_liftEnv1]
  | findB K l p ihl ihp =>
    simp only [substExpr, Expr.eval, ihl]
    congr 1; ext x; simp [ihp, evalEnvMap_liftEnv1]
  | anyB K l p ihl ihp =>
    simp only [substExpr, Expr.eval, ihl]
    congr 1; ext x; simp [ihp, evalEnvMap_liftEnv1]
  | mapB K l f ihl ihf =>
    simp only [substExpr, Expr.eval, ihl]
    congr 1; ext x; simp [ihf, evalEnvMap_liftEnv1]
  | foldrB K l z f ihl ihz ihf =>
    simp only [substExpr, Expr.eval, ihl, ihz]
    congr 1; ext x acc; simp [ihf, evalEnvMap_liftEnv2]

theorem comp_renameM_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)}
    (f : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (c : Comp O I Γ t) (ρ : Env Δ) :
    (c.renameM f).eval ρ = c.eval (envRen f ρ) := by
  induction c generalizing Δ with
  | ret e => simp [Comp.renameM, Comp.eval, expr_renameM_eval]
  | bind c k ihc ihk =>
    simp only [Comp.renameM, Comp.eval, ihc]
    exact bind_congr fun x => by simp [ihk, envRen_liftRen]
  | ite b c d ihc ihd =>
    simp [Comp.renameM, Comp.eval, expr_renameM_eval, ihc, ihd]
  | caseOpt e n s ihn ihs =>
    simp only [Comp.renameM, Comp.eval, expr_renameM_eval]
    cases e.eval _ <;> simp [ihn, ihs, envRen_liftRen]
  | caseSum e l r ihl ihr =>
    simp only [Comp.renameM, Comp.eval, expr_renameM_eval]
    cases e.eval _ <;> simp [ihl, ihr, envRen_liftRen]
  | sample s e => simp [Comp.renameM, Comp.eval, expr_renameM_eval]
  | query g e => dsimp only [Comp.renameM, Comp.eval]; rw [expr_renameM_eval]
  | iter n e body ih =>
    simp only [Comp.renameM, Comp.eval, expr_renameM_eval]
    congr 1; funext a; simp [ih, envRen_liftRen]
  | findM K l p ih =>
    simp only [Comp.renameM, Comp.eval, expr_renameM_eval]
    congr 1; funext x; simp [ih, envRen_liftRen]
  | anyM K l p ih =>
    simp only [Comp.renameM, Comp.eval, expr_renameM_eval]
    congr 1; funext x; simp [ih, envRen_liftRen]
  | mapM K l f' ih =>
    simp only [Comp.renameM, Comp.eval, expr_renameM_eval]
    congr 1; funext x; simp [ih, envRen_liftRen]
  | consumeFirstM K l p mk ih =>
    simp only [Comp.renameM, Comp.eval, expr_renameM_eval]
    congr 2
    · funext x; simp [ih, envRen_liftRen]
    · funext x; rw [envRen_liftRen]
  | foldM K l z f' ih =>
    simp only [Comp.renameM, Comp.eval, expr_renameM_eval]
    congr 1; funext x acc; simp [ih, envRen_liftRen]

theorem callBinaryComp_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {a b c : Ty S} {Δ : List (Ty S)}
    (m : Comp O I [a, b] c) (ab : a.denote × b.denote) (ρ : Env Δ) :
    (callBinaryComp m).eval (.cons ab ρ) = m.eval (.cons ab.1 (.cons ab.2 .nil)) := by
  simp [callBinaryComp, Comp.eval, Expr.eval, comp_renameM_eval, envRen, renId2]

theorem simulateQ_run_iterM {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (f : α → OracleComp T₁ α) (f' : α × σ → OracleComp T₂ (α × σ))
    (hf : ∀ ar, f' ar = (simulateQ simImpl (f ar.1)).run ar.2) :
    ∀ (n : ℕ) (a : α) (r : σ),
      iterM f' n (a, r) = (simulateQ simImpl (iterM f n a)).run r
  | 0, a, r => by simp [iterM]
  | n + 1, a, r => by
    simp only [iterM, simulateQ_bind, StateT.run_bind, hf]
    exact bind_congr fun ar => simulateQ_run_iterM simImpl f f' hf n ar.1 ar.2

theorem simulateQ_run_foldML {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α β σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (f : α → β → OracleComp T₁ β) (f' : α → β × σ → OracleComp T₂ (β × σ))
    (hf : ∀ x br, f' x br = (simulateQ simImpl (f x br.1)).run br.2) :
    ∀ (xs : List α) (b : β) (r : σ),
      foldML f' (b, r) xs = (simulateQ simImpl (foldML f b xs)).run r
  | [], b, r => by simp [foldML]
  | x :: xs, b, r => by
    simp only [foldML, simulateQ_bind, StateT.run_bind, hf]
    exact bind_congr fun br => simulateQ_run_foldML simImpl f f' hf xs br.1 br.2

theorem foldML_pure_cons {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} :
    ∀ (xs acc : List α),
      foldML (m := m) (fun x ys => pure (x :: ys)) acc xs = pure (xs.reverseAux acc)
  | [], _ => rfl
  | x :: xs, acc => by
    dsimp only [foldML, List.reverseAux]
    rw [pure_bind, foldML_pure_cons xs (x :: acc)]

theorem reverse_reverseAux {α : Type}
    (xs acc : List α) : (xs.reverseAux acc).reverse = acc.reverse ++ xs := by
  induction xs generalizing acc with
  | nil => simp [List.reverseAux]
  | cons x xs ih => dsimp only [List.reverseAux]; rw [ih (x :: acc)]; simp

theorem foldML_find_some {m : Type → Type} [Monad m] [LawfulMonad m] {α σ : Type}
    (stepNone : α → Option α × σ → m (Option α × σ)) (v : α) :
    ∀ (xs : List α) (r : σ),
      foldML (m := m)
        (fun x (acc : Option α × σ) => match acc.1 with
          | none => stepNone x acc
          | some _ => pure acc)
        (some v, r) xs = pure (some v, r)
  | [], _ => rfl
  | _ :: xs, r => by
    dsimp only [foldML]; rw [pure_bind]; exact foldML_find_some stepNone v xs r

theorem foldML_any_true {m : Type → Type} [Monad m] [LawfulMonad m] {α σ : Type}
    (stepFalse : α → Bool × σ → m (Bool × σ)) :
    ∀ (xs : List α) (r : σ),
      foldML (m := m)
        (fun x (acc : Bool × σ) => if acc.1 then pure acc else stepFalse x acc)
        (true, r) xs = pure (true, r)
  | [], _ => rfl
  | _ :: xs, r => by
    dsimp only [foldML]; simp only [↓reduceIte, pure_bind]
    exact foldML_any_true stepFalse xs r

theorem foldML_consume_true {m : Type → Type} [Monad m] [LawfulMonad m] {α σ : Type}
    (stepFalse : α → (Bool × List α) × σ → m ((Bool × List α) × σ)) :
    ∀ (xs accRev : List α) (r : σ),
      foldML (m := m)
        (fun x (acc : (Bool × List α) × σ) =>
          if acc.1.1 then pure ((true, x :: acc.1.2), acc.2)
          else stepFalse x acc)
        ((true, accRev), r) xs = pure ((true, xs.reverseAux accRev), r)
  | [], _, _ => rfl
  | x :: xs, accRev, r => by
    dsimp only [foldML, List.reverseAux]
    simp only [↓reduceIte, pure_bind]
    exact foldML_consume_true stepFalse xs (x :: accRev) r

theorem simulateQ_run_findML {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (p : α → OracleComp T₁ Bool) (p' : α → Option α × σ → OracleComp T₂ (Bool × σ))
    (hp : ∀ x r, p' x (none, r) = (simulateQ simImpl (p x)).run r) :
    ∀ (xs : List α) (r : σ),
      foldML
        (fun x (acc : Option α × σ) => match acc.1 with
          | none => p' x acc >>= fun br => pure (if br.1 then some x else none, br.2)
          | some _ => pure acc)
        (none, r) xs = (simulateQ simImpl (findML p xs)).run r
  | [], r => by simp [foldML, findML]
  | x :: xs, r => by
    dsimp only [foldML, findML]
    rw [hp x r, bind_assoc, simulateQ_bind, StateT.run_bind]
    refine bind_congr fun br => ?_
    rcases br with ⟨_ | _, r'⟩
    · simpa using simulateQ_run_findML simImpl p p' hp xs r'
    · simpa using foldML_find_some
        (fun y acc => p' y acc >>= fun z => pure (if z.1 then some y else none, z.2))
        x xs r'

theorem simulateQ_run_anyML {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (p : α → OracleComp T₁ Bool) (p' : α → Bool × σ → OracleComp T₂ (Bool × σ))
    (hp : ∀ x r, p' x (false, r) = (simulateQ simImpl (p x)).run r) :
    ∀ (xs : List α) (r : σ),
      foldML (fun x (acc : Bool × σ) => if acc.1 then pure acc else p' x acc)
        (false, r) xs = (simulateQ simImpl (anyML p xs)).run r
  | [], r => by simp [foldML, anyML]
  | x :: xs, r => by
    dsimp only [foldML, anyML]
    simp only [Bool.false_eq_true, ↓reduceIte, hp x r, simulateQ_bind, StateT.run_bind]
    refine bind_congr fun br => ?_
    rcases br with ⟨_ | _, r'⟩
    · simpa using simulateQ_run_anyML simImpl p p' hp xs r'
    · simpa using foldML_any_true p' xs r'

theorem stateT_run_pure {m : Type → Type} [Monad m] {σ α : Type} (x : α) (s : σ) :
    (pure x : StateT σ m α).run s = pure (x, s) := rfl

theorem stateT_run_lift {m : Type → Type} [Monad m] {σ α : Type} (mx : m α) (s : σ) :
    (StateT.lift mx : StateT σ m α).run s = (mx >>= fun x => pure (x, s)) := rfl

theorem simulateQ_run_mapML_aux {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α β σ : Type} (K : ℕ) (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (f : α → OracleComp T₁ β) (f' : α → List β × σ → OracleComp T₂ (β × σ))
    (hf : ∀ x accRev r, f' x (accRev, r) = (simulateQ simImpl (f x)).run r) :
    ∀ (xs : List α) (accRev : List β) (r : σ) (_ : accRev.length + xs.length ≤ K),
      (foldML (fun x (acc : List β × σ) => f' x acc >>= fun yr => pure (yr.1 :: acc.1, yr.2))
          (accRev, r) xs >>= fun z =>
        foldML (fun y ys => pure (y :: ys)) [] (z.1.take K) >>= fun ys => pure (ys, z.2)) =
        ((simulateQ simImpl (mapML f xs)).run r >>= fun ysR =>
          pure (accRev.reverse ++ ysR.1, ysR.2))
  | [], accRev, r, hlen => by
    have hle : accRev.length ≤ K := by simp only [List.length_nil, Nat.add_zero] at hlen; exact hlen
    dsimp only [foldML, mapML]
    simp only [pure_bind, List.take_of_length_le hle, foldML_pure_cons, simulateQ_pure,
      stateT_run_pure]
    change pure (accRev.reverse, r) = pure (accRev.reverse ++ [], r)
    simp
  | x :: xs, accRev, r, hlen => by
    dsimp only [foldML, mapML]
    simp only [hf x accRev r, simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]
    refine bind_congr (m := OracleComp T₂) fun yr => ?_
    have hlen' : (yr.1 :: accRev).length + xs.length ≤ K := by
      simp only [List.length_cons] at hlen ⊢; omega
    rw [simulateQ_run_mapML_aux K simImpl f f' hf xs (yr.1 :: accRev) yr.2 hlen']
    refine bind_congr (m := OracleComp T₂) fun ysR => ?_
    rw [simulateQ_pure, stateT_run_pure, pure_bind]
    simp [List.reverse_cons, List.append_assoc]

theorem simulateQ_run_consumeFirstML_aux {ι₁ ι₂ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α σ : Type} (K : ℕ) (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (p : α → OracleComp T₁ Bool) (mk : α → α)
    (p' : α → (Bool × List α) × σ → OracleComp T₂ (Bool × σ))
    (mk' : Bool × σ → α → (Bool × List α) × σ → α)
    (hp : ∀ x accRev r, p' x ((false, accRev), r) = (simulateQ simImpl (p x)).run r)
    (hmk : ∀ br x accRev r, mk' br x ((false, accRev), r) = mk x) :
    ∀ (xs accRev : List α) (r : σ) (_ : accRev.length + xs.length ≤ K),
      (foldML
          (fun x (acc : (Bool × List α) × σ) =>
            if acc.1.1 then pure ((true, x :: acc.1.2), acc.2)
            else
              p' x acc >>= fun br =>
                if br.1 then pure ((true, mk' br x acc :: acc.1.2), br.2)
                else pure ((false, x :: acc.1.2), br.2))
          ((false, accRev), r) xs >>= fun z =>
        foldML (fun y ys => pure (y :: ys)) [] (z.1.2.take K) >>= fun ys =>
          pure ((z.1.1, ys), z.2)) =
        ((simulateQ simImpl (consumeFirstML p mk xs)).run r >>= fun res =>
          pure ((res.1.1, accRev.reverse ++ res.1.2), res.2))
  | [], accRev, r, hlen => by
    have hle : accRev.length ≤ K := by simp only [List.length_nil, Nat.add_zero] at hlen; exact hlen
    dsimp only [foldML, consumeFirstML]
    simp only [pure_bind, List.take_of_length_le hle, foldML_pure_cons, simulateQ_pure,
      stateT_run_pure]
    change pure ((false, accRev.reverse), r) = pure ((false, accRev.reverse ++ []), r)
    simp
  | x :: xs, accRev, r, hlen => by
    dsimp only [foldML, consumeFirstML]
    simp only [Bool.false_eq_true, ↓reduceIte, hp x accRev r, bind_assoc, simulateQ_bind,
      StateT.run_bind]
    refine bind_congr fun br => ?_
    cases h : br.1
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      have hlen' : (x :: accRev).length + xs.length ≤ K := by
        simp only [List.length_cons] at hlen ⊢; omega
      rw [simulateQ_run_consumeFirstML_aux K simImpl p mk p' mk' hp hmk xs (x :: accRev) br.2 hlen']
      simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
      refine bind_congr fun res => ?_
      rw [simulateQ_pure, stateT_run_pure, pure_bind]
      simp
    · simp only [↓reduceIte, pure_bind, hmk br x accRev r]
      rw [foldML_consume_true _ xs (mk x :: accRev) br.2]
      have hRevLen : (xs.reverseAux (mk x :: accRev)).length ≤ K := by
        have hEqR := congrArg List.length (reverse_reverseAux xs (mk x :: accRev))
        simp only [List.length_reverse, List.length_append, List.length_cons] at hEqR hlen
        omega
      simp only [pure_bind, List.take_of_length_le hRevLen, foldML_pure_cons]
      have hRevEq : (xs.reverseAux (mk x :: accRev)).reverseAux [] =
          (xs.reverseAux (mk x :: accRev)).reverse := rfl
      rw [hRevEq, reverse_reverseAux, simulateQ_pure, stateT_run_pure, pure_bind]
      simp

theorem simulateQ_run_iterM_const {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (f : α → OracleComp T₁ α) (f' : α → OracleComp T₂ α) (r : σ)
    (hf : ∀ a, (f' a >>= fun x => pure (x, r)) = (simulateQ simImpl (f a)).run r) :
    ∀ (n : ℕ) (a : α),
      (iterM f' n a >>= fun x => pure (x, r)) = (simulateQ simImpl (iterM f n a)).run r
  | 0, a => by dsimp only [iterM]; rw [simulateQ_pure, stateT_run_pure, pure_bind]
  | n + 1, a => by
    dsimp only [iterM]
    simp only [bind_assoc, simulateQ_bind, StateT.run_bind]
    calc
      (f' a >>= fun x => iterM f' n x >>= fun y => pure (y, r))
          = (f' a >>= fun x => (simulateQ simImpl (iterM f n x)).run r) :=
            bind_congr fun x => simulateQ_run_iterM_const simImpl f f' r hf n x
      _ = ((f' a >>= fun x => pure (x, r)) >>= fun xr =>
            (simulateQ simImpl (iterM f n xr.1)).run xr.2) := by
            simp only [bind_assoc, pure_bind]
      _ = ((simulateQ simImpl (f a)).run r >>= fun xr =>
            (simulateQ simImpl (iterM f n xr.1)).run xr.2) := by
            rw [hf a]

theorem simulateQ_run_foldML_const {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α β σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (f : α → β → OracleComp T₁ β) (f' : α → β → OracleComp T₂ β) (r : σ)
    (hf : ∀ x b, (f' x b >>= fun y => pure (y, r)) = (simulateQ simImpl (f x b)).run r) :
    ∀ (xs : List α) (b : β),
      (foldML f' b xs >>= fun y => pure (y, r)) = (simulateQ simImpl (foldML f b xs)).run r
  | [], b => by dsimp only [foldML]; rw [simulateQ_pure, stateT_run_pure, pure_bind]
  | x :: xs, b => by
    simp only [foldML, bind_assoc, simulateQ_bind, StateT.run_bind]
    calc
      (f' x b >>= fun y => foldML f' y xs >>= fun z => pure (z, r))
          = (f' x b >>= fun y => (simulateQ simImpl (foldML f y xs)).run r) :=
            bind_congr fun y => simulateQ_run_foldML_const simImpl f f' r hf xs y
      _ = ((f' x b >>= fun y => pure (y, r)) >>= fun yr =>
            (simulateQ simImpl (foldML f yr.1 xs)).run yr.2) := by
            simp only [bind_assoc, pure_bind]
      _ = ((simulateQ simImpl (f x b)).run r >>= fun yr =>
            (simulateQ simImpl (foldML f yr.1 xs)).run yr.2) := by
            rw [hf x b]

theorem simulateQ_run_findML_const {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (p : α → OracleComp T₁ Bool) (p' : α → OracleComp T₂ Bool) (r : σ)
    (hp : ∀ x, (p' x >>= fun b => pure (b, r)) = (simulateQ simImpl (p x)).run r) :
    ∀ (xs : List α),
      (findML p' xs >>= fun y => pure (y, r)) = (simulateQ simImpl (findML p xs)).run r
  | [] => by dsimp only [findML]; rw [simulateQ_pure, stateT_run_pure, pure_bind]
  | x :: xs => by
    simp only [findML, bind_assoc, simulateQ_bind, StateT.run_bind]
    calc
      (p' x >>= fun b => (if b then pure (some x) else findML p' xs) >>= fun y => pure (y, r))
          = (p' x >>= fun b =>
              (simulateQ simImpl (if b then pure (some x) else findML p xs)).run r) := by
            refine bind_congr fun b => ?_
            cases b
            · simpa using simulateQ_run_findML_const simImpl p p' r hp xs
            · simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, pure_bind]
      _ = ((p' x >>= fun b => pure (b, r)) >>= fun br =>
            (simulateQ simImpl (if br.1 then pure (some x) else findML p xs)).run br.2) := by
            simp only [bind_assoc, pure_bind]
      _ = ((simulateQ simImpl (p x)).run r >>= fun br =>
            (simulateQ simImpl (if br.1 then pure (some x) else findML p xs)).run br.2) := by
            rw [hp x]

theorem simulateQ_run_anyML_const {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (p : α → OracleComp T₁ Bool) (p' : α → OracleComp T₂ Bool) (r : σ)
    (hp : ∀ x, (p' x >>= fun b => pure (b, r)) = (simulateQ simImpl (p x)).run r) :
    ∀ (xs : List α),
      (anyML p' xs >>= fun y => pure (y, r)) = (simulateQ simImpl (anyML p xs)).run r
  | [] => by dsimp only [anyML]; rw [simulateQ_pure, stateT_run_pure, pure_bind]
  | x :: xs => by
    simp only [anyML, bind_assoc, simulateQ_bind, StateT.run_bind]
    calc
      (p' x >>= fun b => (if b then pure true else anyML p' xs) >>= fun y => pure (y, r))
          = (p' x >>= fun b =>
              (simulateQ simImpl (if b then pure true else anyML p xs)).run r) := by
            refine bind_congr fun b => ?_
            cases b
            · simpa using simulateQ_run_anyML_const simImpl p p' r hp xs
            · simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, pure_bind]
      _ = ((p' x >>= fun b => pure (b, r)) >>= fun br =>
            (simulateQ simImpl (if br.1 then pure true else anyML p xs)).run br.2) := by
            simp only [bind_assoc, pure_bind]
      _ = ((simulateQ simImpl (p x)).run r >>= fun br =>
            (simulateQ simImpl (if br.1 then pure true else anyML p xs)).run br.2) := by
            rw [hp x]

theorem simulateQ_run_mapML_const {ι₁ ι₂ : Type} {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α β σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (f : α → OracleComp T₁ β) (f' : α → OracleComp T₂ β) (r : σ)
    (hf : ∀ x, (f' x >>= fun y => pure (y, r)) = (simulateQ simImpl (f x)).run r) :
    ∀ (xs : List α),
      (mapML f' xs >>= fun ys => pure (ys, r)) = (simulateQ simImpl (mapML f xs)).run r
  | [] => by dsimp only [mapML]; rw [simulateQ_pure, StateT.run_pure, pure_bind]
  | x :: xs => by
    dsimp only [mapML]
    rw [bind_assoc, simulateQ_bind, StateT.run_bind]
    calc
      (f' x >>= fun y => (mapML f' xs >>= fun ys => pure (y :: ys)) >>= fun z => pure (z, r))
          = (f' x >>= fun y =>
              (simulateQ simImpl (mapML f xs >>= fun ys => pure (y :: ys))).run r) := by
            refine bind_congr fun y => ?_
            rw [bind_assoc, simulateQ_bind, StateT.run_bind]
            simp only [pure_bind, simulateQ_pure, StateT.run_pure]
            rw [← simulateQ_run_mapML_const simImpl f f' r hf xs]
            simp only [bind_assoc, pure_bind]
      _ = ((f' x >>= fun y => pure (y, r)) >>= fun yr =>
            (simulateQ simImpl (mapML f xs >>= fun ys => pure (yr.1 :: ys))).run yr.2) := by
            simp only [bind_assoc, pure_bind]
      _ = ((simulateQ simImpl (f x)).run r >>= fun yr =>
            (simulateQ simImpl (mapML f xs >>= fun ys => pure (yr.1 :: ys))).run yr.2) := by
            rw [hf x]

theorem simulateQ_run_consumeFirstML_const {ι₁ ι₂ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂}
    {α σ : Type} (simImpl : QueryImpl T₁ (StateT σ (OracleComp T₂)))
    (p : α → OracleComp T₁ Bool) (p' : α → OracleComp T₂ Bool) (mk : α → α) (r : σ)
    (hp : ∀ x, (p' x >>= fun b => pure (b, r)) = (simulateQ simImpl (p x)).run r) :
    ∀ (xs : List α),
      (consumeFirstML p' mk xs >>= fun z => pure (z, r)) =
        (simulateQ simImpl (consumeFirstML p mk xs)).run r
  | [] => by dsimp only [consumeFirstML]; rw [simulateQ_pure, stateT_run_pure, pure_bind]
  | x :: xs => by
    simp only [consumeFirstML, bind_assoc, simulateQ_bind, StateT.run_bind]
    calc
      (p' x >>= fun b =>
          (if b then pure (true, mk x :: xs)
           else consumeFirstML p' mk xs >>= fun res => pure (res.1, x :: res.2)) >>= fun z =>
            pure (z, r))
          = (p' x >>= fun b =>
              (simulateQ simImpl
                (if b then pure (true, mk x :: xs)
                 else consumeFirstML p mk xs >>= fun res => pure (res.1, x :: res.2))).run r) := by
            refine bind_congr fun b => ?_
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, simulateQ_bind,
                StateT.run_bind]
              rw [← simulateQ_run_consumeFirstML_const simImpl p p' mk r hp xs]
              simp only [bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
            · simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, pure_bind]
      _ = ((p' x >>= fun b => pure (b, r)) >>= fun br =>
            (simulateQ simImpl
              (if br.1 then pure (true, mk x :: xs)
               else consumeFirstML p mk xs >>= fun res => pure (res.1, x :: res.2))).run br.2) := by
            simp only [bind_assoc, pure_bind]
      _ = ((simulateQ simImpl (p x)).run r >>= fun br =>
            (simulateQ simImpl
              (if br.1 then pure (true, mk x :: xs)
               else consumeFirstML p mk xs >>= fun res => pure (res.1, x :: res.2))).run br.2) := by
            rw [hp x]

abbrev listElemTy {S : Sig} {O : Ops S} {Γ : List (Ty S)} {u : Ty S}
    (_ : Expr O Γ (.list u)) : Ty S := u

abbrev compRetTy {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {u : Ty S} (_ : Comp O I Γ u) : Ty S := u

theorem substNoQueryComp_eval {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {rStTy : Ty S}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (simImpl : QueryImpl T₁ (StateT rStTy.denote (OracleComp T₂)))
    (hSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)} (e : Expr O Δ (I₁.smp.sDom s))
      (ρ : Env Δ) (r : rStTy.denote),
      ((mapSamp s e).eval ρ >>= fun x => pure (x, r)) =
        (simulateQ simImpl (I₁.liftP (I₁.smp.samp s (e.eval ρ)))).run r) :
    ∀ {Γ Δ : List (Ty S)} {t : Ty S}
      (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
      (c : Comp O I₁ Γ t) (hc : c.queries (fun _ => 1) (fun _ => 0) = 0)
      (ρ : Env Δ) (r : rStTy.denote),
      ((substNoQueryComp mapSamp envMap c hc).eval ρ >>= fun x => pure (x, r)) =
        (simulateQ simImpl (c.eval (evalEnvMap envMap ρ))).run r := by
  intro Γ Δ t envMap c hc ρ r
  induction c generalizing Δ r with
  | ret e => simp [substNoQueryComp, Comp.eval, substExpr_eval, simulateQ_pure]
  | bind c k ihc ihk =>
    simp only [substNoQueryComp, Comp.eval, bind_assoc, simulateQ_bind, StateT.run_bind]
    have h1 := ihc envMap (by simp [Comp.queries] at hc; omega) ρ r
    calc
      ((substNoQueryComp mapSamp envMap c _).eval ρ >>= fun x =>
          (substNoQueryComp mapSamp (liftEnv1 envMap) k _).eval (.cons x ρ) >>= fun y => pure (y, r))
          = ((substNoQueryComp mapSamp envMap c _).eval ρ >>= fun x =>
              (simulateQ simImpl (k.eval (.cons x (evalEnvMap envMap ρ)))).run r) := by
            refine bind_congr fun x => ?_
            simpa [evalEnvMap_liftEnv1] using
              ihk (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons x ρ) r
      _ = (((substNoQueryComp mapSamp envMap c _).eval ρ >>= fun x => pure (x, r)) >>= fun xr =>
            (simulateQ simImpl (k.eval (.cons xr.1 (evalEnvMap envMap ρ)))).run xr.2) := by
            simp only [bind_assoc, pure_bind]
      _ = ((simulateQ simImpl (c.eval (evalEnvMap envMap ρ))).run r >>= fun xr =>
            (simulateQ simImpl (k.eval (.cons xr.1 (evalEnvMap envMap ρ)))).run xr.2) := by
            rw [h1]
  | ite b c d ihc ihd =>
    simp only [substNoQueryComp, Comp.eval, substExpr_eval]
    split
    · exact ihc envMap (by simp [Comp.queries] at hc; omega) ρ r
    · exact ihd envMap (by simp [Comp.queries] at hc; omega) ρ r
  | caseOpt e n s ihn ihs =>
    simp only [substNoQueryComp, Comp.eval, substExpr_eval]
    cases e.eval (evalEnvMap envMap ρ) with
    | none => exact ihn envMap (by simp [Comp.queries] at hc; omega) ρ r
    | some v =>
      simpa [evalEnvMap_liftEnv1] using
        ihs (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons v ρ) r
  | caseSum e l r' ihl ihr =>
    simp only [substNoQueryComp, Comp.eval, substExpr_eval]
    cases e.eval (evalEnvMap envMap ρ) with
    | inl v =>
      simpa [evalEnvMap_liftEnv1] using
        ihl (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons v ρ) r
    | inr v =>
      simpa [evalEnvMap_liftEnv1] using
        ihr (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons v ρ) r
  | sample s e =>
    dsimp only [substNoQueryComp, Comp.eval]
    simpa [substExpr_eval] using hSamp s (substExpr envMap e) ρ r
  | query _ _ =>
    exfalso; simp [Comp.queries] at hc
  | iter n e body ih =>
    cases n with
    | zero => simp [substNoQueryComp, Comp.eval, iterM, substExpr_eval, simulateQ_pure]
    | succ n =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval]
      refine simulateQ_run_iterM_const simImpl _ _ r (fun a => ?_) (n + 1) _
      simpa [evalEnvMap_liftEnv1] using
        ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons a ρ) r
  | foldM K l z f ih =>
    cases K with
    | zero => simp [substNoQueryComp, Comp.eval, foldML, substExpr_eval, simulateQ_pure]
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval, substExpr_eval]
      refine simulateQ_run_foldML_const simImpl _ _ r (fun x b => ?_) _ _
      simpa [evalEnvMap_liftEnv2] using
        ih (liftEnv2 envMap) (by simp [Comp.queries] at hc; omega) (.cons x (.cons b ρ)) r
  | findM K l p ih =>
    cases K with
    | zero => simp [substNoQueryComp, Comp.eval, findML, substExpr_eval, simulateQ_pure]
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval]
      refine simulateQ_run_findML_const simImpl _ _ r (fun x => ?_) _
      simpa [evalEnvMap_liftEnv1] using
        ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons x ρ) r
  | anyM K l p ih =>
    cases K with
    | zero => simp [substNoQueryComp, Comp.eval, anyML, substExpr_eval, simulateQ_pure]
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval]
      refine simulateQ_run_anyML_const simImpl _ _ r (fun x => ?_) _
      simpa [evalEnvMap_liftEnv1] using
        ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons x ρ) r
  | mapM K l f ih =>
    cases K with
    | zero => simp [substNoQueryComp, Comp.eval, Expr.eval, mapML, simulateQ_pure]
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval]
      refine simulateQ_run_mapML_const simImpl _ _ r (fun x => ?_) _
      simpa [evalEnvMap_liftEnv1] using
        ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons x ρ) r
  | consumeFirstM K l p mk ih =>
    cases K with
    | zero =>
      simp [substNoQueryComp, Comp.eval, Expr.eval, consumeFirstML, simulateQ_pure]
    | succ K =>
      dsimp only [substNoQueryComp, Comp.eval]
      rw [substExpr_eval]
      have hmk : (fun x => (substExpr (liftEnv1 envMap) mk).eval (.cons x ρ)) =
          (fun x => mk.eval (.cons x (evalEnvMap envMap ρ))) := by
        funext x; rw [substExpr_eval, evalEnvMap_liftEnv1]
      rw [hmk]
      refine simulateQ_run_consumeFirstML_const simImpl _ _ _ r (fun x => ?_) _
      simpa [evalEnvMap_liftEnv1] using
        ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega) (.cons x ρ) r

theorem substQueryComp_eval {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {rStTy : Ty S}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (simImpl : QueryImpl T₁ (StateT rStTy.denote (OracleComp T₂)))
    (hSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)} (e : Expr O Δ (I₁.smp.sDom s))
      (ρ : Env Δ) (r : rStTy.denote),
      ((mapSamp s e).eval ρ >>= fun x => pure (x, r)) =
        (simulateQ simImpl (I₁.liftP (I₁.smp.samp s (e.eval ρ)))).run r)
    (hQuery : ∀ (g : I₁.Tag) (x : (I₁.dom g).denote) (r : rStTy.denote),
      (qImpl g).eval (.cons x (.cons r .nil)) =
        (I₁.dec g x <$> simImpl (I₁.enc g x)).run r) :
    ∀ {Γ Δ : List (Ty S)} {t : Ty S}
      (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
      (rExpr : Expr O Δ rStTy)
      (c : Comp O I₁ Γ t) (ρ : Env Δ),
      (substQueryComp mapSamp qImpl envMap rExpr c).eval ρ =
        (simulateQ simImpl (c.eval (evalEnvMap envMap ρ))).run (rExpr.eval ρ) := by
  intro Γ Δ t envMap rExpr c ρ
  induction c generalizing Δ with
  | ret e => simp [substQueryComp, Comp.eval, Expr.eval, substExpr_eval]
  | bind c k ihc ihk =>
    simp only [substQueryComp, Comp.eval, ihc, simulateQ_bind, StateT.run_bind]
    refine bind_congr fun xr => ?_
    simpa [Expr.eval, Env.get, evalEnvMap_liftEnvFst] using
      ihk (liftEnvFst envMap) (.snd (.var .zero)) (.cons xr ρ)
  | ite b c d ihc ihd =>
    simp only [substQueryComp, Comp.eval, substExpr_eval]
    split <;> [exact ihc envMap rExpr ρ; exact ihd envMap rExpr ρ]
  | caseOpt e n s ihn ihs =>
    simp only [substQueryComp, Comp.eval, substExpr_eval]
    cases e.eval (evalEnvMap envMap ρ) with
    | none => exact ihn envMap rExpr ρ
    | some v =>
      simpa [exprWk1_eval, evalEnvMap_liftEnv1] using ihs (liftEnv1 envMap) (exprWk1 rExpr) (.cons v ρ)
  | caseSum e l r ihl ihr =>
    simp only [substQueryComp, Comp.eval, substExpr_eval]
    cases e.eval (evalEnvMap envMap ρ) with
    | inl v =>
      simpa [exprWk1_eval, evalEnvMap_liftEnv1] using ihl (liftEnv1 envMap) (exprWk1 rExpr) (.cons v ρ)
    | inr v =>
      simpa [exprWk1_eval, evalEnvMap_liftEnv1] using ihr (liftEnv1 envMap) (exprWk1 rExpr) (.cons v ρ)
  | sample s e =>
    dsimp only [substQueryComp, Comp.eval]
    have h := hSamp s (substExpr envMap e) ρ (rExpr.eval ρ)
    simpa [Expr.eval, Env.get, exprWk1_eval, substExpr_eval] using h
  | query g e =>
    simp [substQueryComp, Comp.eval, Expr.eval, substExpr_eval, callBinaryComp_eval, hQuery]
  | iter n e body ih =>
    dsimp only [substQueryComp, Comp.eval, Expr.eval]
    rw [substExpr_eval]
    refine simulateQ_run_iterM simImpl _ _ (fun ar => ?_) n _ _
    simpa [Expr.eval, Env.get, evalEnvMap_liftEnvFst] using
      ih (liftEnvFst envMap) (.snd (.var .zero)) (.cons ar ρ)
  | foldM K l z f ih =>
    dsimp only [substQueryComp, Comp.eval, Expr.eval]
    rw [substExpr_eval, substExpr_eval]
    refine simulateQ_run_foldML simImpl _ _ (fun x br => ?_) _ _ _
    simpa [Expr.eval, Env.get, evalEnvMap_liftEnvFold] using
      ih (liftEnvFold envMap) (.snd (.var (.succ .zero))) (.cons x (.cons br ρ))
  | findM K l p ih =>
    cases K with
    | zero => simp [substQueryComp, Comp.eval, Expr.eval, findML, simulateQ_pure]
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · simpa [Comp.eval, Expr.eval, Env.get, exprWk1_eval] using
          substNoQueryComp_eval mapSamp simImpl hSamp envMap (.findM (K + 1) l p) hc0 ρ (rExpr.eval ρ)
      · dsimp only [Comp.eval, Expr.eval]
        simp only [Env.get]
        rw [substExpr_eval]
        have h := simulateQ_run_findML simImpl
          (fun x => p.eval (.cons x (evalEnvMap envMap ρ)))
          (fun x acc => (substQueryComp mapSamp qImpl (liftEnvPred2 (x := .prod (.opt _) rStTy) envMap)
            (.snd (.var (.succ .zero))) p).eval (.cons x (.cons acc ρ)))
          (fun x r => by
            simpa [Expr.eval, Env.get, evalEnvMap_liftEnvPred2] using
              ih (liftEnvPred2 (x := .prod (.opt _) rStTy) envMap) (.snd (.var (.succ .zero)))
                (.cons x (.cons (none, r) ρ)))
          ((l.eval (evalEnvMap envMap ρ)).take (K + 1)) (rExpr.eval ρ)
        rw [← h]
        congr 1; funext x acc; cases acc.1 <;> rfl
  | anyM K l p ih =>
    cases K with
    | zero => simp [substQueryComp, Comp.eval, Expr.eval, anyML, simulateQ_pure]
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · simpa [Comp.eval, Expr.eval, Env.get, exprWk1_eval] using
          substNoQueryComp_eval mapSamp simImpl hSamp envMap (.anyM (K + 1) l p) hc0 ρ (rExpr.eval ρ)
      · dsimp only [Comp.eval, Expr.eval]
        simp only [Env.get]
        rw [substExpr_eval]
        refine simulateQ_run_anyML simImpl
          (fun x => p.eval (.cons x (evalEnvMap envMap ρ)))
          (fun x acc => (substQueryComp mapSamp qImpl (liftEnvPred2 (x := .prod .bool rStTy) envMap)
            (.snd (.var (.succ .zero))) p).eval (.cons x (.cons acc ρ)))
          (fun x r => ?_) _ _
        simpa [Expr.eval, Env.get, evalEnvMap_liftEnvPred2] using
          ih (liftEnvPred2 (x := .prod .bool rStTy) envMap) (.snd (.var (.succ .zero)))
            (.cons x (.cons (false, r) ρ))
  | mapM K l f ih =>
    cases K with
    | zero => simp [substQueryComp, Comp.eval, Expr.eval, mapML, simulateQ_pure]
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · simpa [Comp.eval, Expr.eval, Env.get, exprWk1_eval] using
          substNoQueryComp_eval mapSamp simImpl hSamp envMap (.mapM (K + 1) l f) hc0 ρ (rExpr.eval ρ)
      · dsimp only [Comp.eval, Expr.eval]
        simp only [Env.get]
        rw [substExpr_eval]
        have h := simulateQ_run_mapML_aux (K + 1) simImpl
          (fun x => f.eval (.cons x (evalEnvMap envMap ρ)))
          (fun x acc => (substQueryComp mapSamp qImpl
            (liftEnvPred2 (x := .prod (.list (compRetTy f)) rStTy) envMap)
            (.snd (.var (.succ .zero))) f).eval (.cons x (.cons acc ρ)))
          (fun x accRev r => by
            simpa [Expr.eval, Env.get, evalEnvMap_liftEnvPred2] using
              ih (liftEnvPred2 (x := .prod (.list (compRetTy f)) rStTy) envMap)
                (.snd (.var (.succ .zero))) (.cons x (.cons (accRev, r) ρ)))
          ((l.eval (evalEnvMap envMap ρ)).take (K + 1)) [] (rExpr.eval ρ)
          (by simp only [List.length_nil, Nat.zero_add]; exact List.length_take_le (K + 1) _)
        simpa [List.nil_append] using h
  | consumeFirstM K l p mk ih =>
    cases K with
    | zero => simp [substQueryComp, Comp.eval, Expr.eval, consumeFirstML, simulateQ_pure]
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · simpa [Comp.eval, Expr.eval, Env.get, exprWk1_eval] using
          substNoQueryComp_eval mapSamp simImpl hSamp envMap (.consumeFirstM (K + 1) l p mk) hc0 ρ
            (rExpr.eval ρ)
      · dsimp only [Comp.eval, Expr.eval]
        simp only [Env.get]
        rw [substExpr_eval]
        have h := simulateQ_run_consumeFirstML_aux (K + 1) simImpl
          (fun x => p.eval (.cons x (evalEnvMap envMap ρ)))
          (fun x => mk.eval (.cons x (evalEnvMap envMap ρ)))
          (fun x acc => (substQueryComp mapSamp qImpl
            (liftEnvPred2 (x := .prod (.prod .bool (.list (listElemTy l))) rStTy) envMap)
            (.snd (.var (.succ .zero))) p).eval (.cons x (.cons acc ρ)))
          (fun br x acc => (substExpr
            (liftEnvMk3 (y := .prod .bool rStTy)
              (x := .prod (.prod .bool (.list (listElemTy l))) rStTy) envMap)
            mk).eval (.cons br (.cons x (.cons acc ρ))))
          (fun x accRev r => by
            simpa [Expr.eval, Env.get, evalEnvMap_liftEnvPred2] using
              ih (liftEnvPred2 (x := .prod (.prod .bool (.list (listElemTy l))) rStTy) envMap)
                (.snd (.var (.succ .zero))) (.cons x (.cons ((false, accRev), r) ρ)))
          (fun br x accRev r => by
            rw [substExpr_eval, evalEnvMap_liftEnvMk3])
          ((l.eval (evalEnvMap envMap ρ)).take (K + 1)) [] (rExpr.eval ρ)
          (by simp only [List.length_nil, Nat.zero_add]; exact List.length_take_le (K + 1) _)
        simpa [List.nil_append] using h

theorem substQueryRed_eval {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec.{0, 0} ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec.{0, 0} ι₂} {I₂ : Iface S T₂}
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C_game : GameCodec S G}
    {rIn aIn aOut out rStTy : Ty S}
    (rInit : Expr O [rIn] rStTy)
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (simImpl : QueryImpl T₁ (StateT rStTy.denote (OracleComp T₂)))
    (hFwdU : ∀ n (r : rStTy.denote),
      (simulateQ simImpl (I₁.fwdU n)).run r = (I₂.fwdU n >>= fun u => pure (u, r)))
    (hSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)} (e : Expr O Δ (I₁.smp.sDom s))
      (ρ : Env Δ) (r : rStTy.denote),
      ((mapSamp s e).eval ρ >>= fun x => pure (x, r)) =
        (simulateQ simImpl (I₁.liftP (I₁.smp.samp s (e.eval ρ)))).run r)
    (hQuery : ∀ (g : I₁.Tag) (x : (I₁.dom g).denote) (r : rStTy.denote),
      (qImpl g).eval (.cons x (.cons r .nil)) =
        (I₁.dec g x <$> simImpl (I₁.enc g x)).run r)
    (R : CostedReduction O I₁ G C_game rIn aIn aOut out)
    (adv : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) :
    (substQueryRed rInit mapSamp qImpl R).eval adv x =
      Prod.fst <$> (simulateQ simImpl (R.eval adv x)).run (rInit.eval (.cons x .nil)) := by
  let R' : CostedReduction O I₂ G C_game rIn aIn aOut out :=
    { σ := .prod R.σ rStTy
      init := .bind (substQueryComp mapSamp qImpl envId1 rInit R.init)
        (.ret (.pair (.fst (.fst (.var .zero)))
          (.pair (.snd (.fst (.var .zero))) (.snd (.var .zero)))))
      handle := .bind (substQueryComp mapSamp qImpl envFst2 (.snd (.var .zero)) R.handle)
        (.ret (.pair (.fst (.fst (.var .zero)))
          (.pair (.snd (.fst (.var .zero))) (.snd (.var .zero)))))
      finish := .bind (substQueryComp mapSamp qImpl envFst2 (.snd (.var .zero)) R.finish)
        (.ret (.fst (.var .zero))) }
  have hSim : ∀ {α : Type} (oa : OracleComp (unifSpec + G) α)
      (s : R.σ.denote) (rSt : rStTy.denote),
      (simulateQ R'.impl oa).run (s, rSt) =
        ((simulateQ simImpl ((simulateQ R.impl oa).run s)).run rSt >>= fun p =>
          pure (p.1.1, (p.1.2, p.2))) := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure b =>
      intro s rSt
      simp only [simulateQ_pure]
      rfl
    | query_bind q k ih =>
      intro s rSt
      rw [simulateQ_bind, simulateQ_bind]
      erw [simulateQ_query, simulateQ_query]
      cases q with
      | inl n =>
        simp only [OracleQuery.input_query, OracleQuery.cont_query,
          id_map, CostedReduction.impl, ReductionDsl.handlerImpl,
          simulateQ_bind, StateT.run_bind, stateT_run_lift, hFwdU, bind_assoc, pure_bind]
        refine bind_congr fun u => ?_
        exact ih u s rSt
      | inr t =>
        simp only [OracleQuery.input_query, OracleQuery.cont_query,
          id_map, CostedReduction.impl, ReductionDsl.handlerImpl,
          simulateQ_bind, StateT.run_bind, StateT.run_mk]
        dsimp only [R', Comp.eval, Expr.eval, Env.get]
        rw [bind_assoc, substQueryComp_eval mapSamp qImpl simImpl hSamp hQuery envFst2
          (.snd (.var .zero)) R.handle (.cons (s, rSt) (.cons (C_game.qenc t) .nil))]
        simp only [evalEnvMap, envFst2, Expr.eval, Env.get,
          simulateQ_pure, stateT_run_pure, bind_assoc, pure_bind]
        refine bind_congr fun vr => ?_
        exact ih (C_game.rdec t vr.1.1) vr.1.2 vr.2
  change R'.eval adv x = _
  dsimp only [CostedReduction.eval]
  have hInit : R'.init.eval (.cons x .nil) =
      ((simulateQ simImpl (R.init.eval (.cons x .nil))).run (rInit.eval (.cons x .nil)) >>= fun p =>
        pure (p.1.1, (p.1.2, p.2))) := by
    dsimp only [R', Comp.eval, Expr.eval, Env.get]
    rw [substQueryComp_eval mapSamp qImpl simImpl hSamp hQuery envId1 rInit R.init (.cons x .nil)]
    simp only [evalEnvMap, envId1, Expr.eval, Env.get]
  rw [hInit]
  simp only [simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  refine bind_congr fun ys => ?_
  rw [hSim (adv ys.1.1) ys.1.2 ys.2]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun bs => ?_
  dsimp only [R', Comp.eval, Expr.eval, Env.get]
  rw [substQueryComp_eval mapSamp qImpl simImpl hSamp hQuery envFst2 (.snd (.var .zero)) R.finish
    (.cons (bs.1.2, bs.2) (.cons bs.1.1 .nil))]
  simp only [evalEnvMap, envFst2, Expr.eval, Env.get]

/-! ### Generic `substNoQueryComp` / `substQueryComp` / `substQueryRed` Query & Cost Bounds -/

@[expose, simp] def compListMNodes {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => 0
  | _, _, .bind c k | _, _, .ite _ c k | _, _, .caseOpt _ c k | _, _, .caseSum _ c k =>
    compListMNodes c + compListMNodes k
  | _, _, .iter _ _ b | _, _, .foldM _ _ _ b => compListMNodes b
  | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b | _, _, .consumeFirstM _ _ b _ =>
    compListMNodes b + 1

@[expose, simp] def compQueryCount {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret _ | _, _, .sample _ _ => 0
  | _, _, .query _ _ => 1
  | _, _, .bind c k | _, _, .ite _ c k | _, _, .caseOpt _ c k | _, _, .caseSum _ c k =>
    compQueryCount c + compQueryCount k
  | _, _, .iter _ _ b | _, _, .foldM _ _ _ b => compQueryCount b
  | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b | _, _, .consumeFirstM _ _ b _ =>
    compQueryCount b

@[expose, simp] def compNodes {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => 1
  | _, _, .bind c k | _, _, .ite _ c k | _, _, .caseOpt _ c k | _, _, .caseSum _ c k =>
    compNodes c + compNodes k + 1
  | _, _, .iter _ _ b | _, _, .foldM _ _ _ b => compNodes b + 1
  | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b | _, _, .consumeFirstM _ _ b _ =>
    compNodes b + 1

theorem comp_renameM_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ Δ : List (Ty S)} {t : Ty S} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) (c : Comp O I Γ t) :
    (c.renameM ξ).cost = c.cost := by
  induction c generalizing Δ with
  | ret e => simp [Comp.renameM, Comp.cost]
  | sample s e => simp [Comp.renameM, Comp.cost]
  | query g e => simp [Comp.renameM, Comp.cost]
  | bind _ _ ih1 ih2 => simp [Comp.renameM, Comp.cost, ih1, ih2]
  | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp [Comp.renameM, Comp.cost, ih1, ih2]
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih | consumeFirstM _ _ _ _ ih
  | foldM _ _ _ _ ih =>
    simp [Comp.renameM, Comp.cost, ih]

theorem comp_renameM_queries {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u)
    (c : Comp O I Γ t) (wT : I.Tag → ℕ) (wS : I.smp.Samp → ℕ) :
    (c.renameM ξ).queries wT wS = c.queries wT wS := by
  induction c generalizing Δ <;> simp [Comp.renameM, Comp.queries, *]

theorem callBinaryComp_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {a b c : Ty S} {Δ : List (Ty S)} (m : Comp O I [a, b] c) :
    (callBinaryComp (Δ := Δ) m).cost = m.cost + 8 := by
  simp only [callBinaryComp, Comp.cost, comp_renameM_cost, Expr.cost]; omega

theorem callBinaryComp_queries {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {a b c : Ty S} {Δ : List (Ty S)} (m : Comp O I [a, b] c)
    (wT : I.Tag → ℕ) (wS : I.smp.Samp → ℕ) :
    (callBinaryComp (Δ := Δ) m).queries wT wS = m.queries wT wS := by
  simp [callBinaryComp, Comp.queries]

theorem envMap_liftEnvFst_cost {S : Sig} {O : Ops S} {a rStTy : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (h : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: Γ) u), (liftEnvFst (rStTy := rStTy) envMap v).cost ≤ 2
  | _, .zero => by simp [liftEnvFst, Expr.cost]
  | _, .succ w => by simp only [liftEnvFst, exprWk1_cost]; exact h w

theorem envMap_liftEnvFold_cost {S : Sig} {O : Ops S} {a b rStTy : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (h : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: b :: Γ) u), (liftEnvFold (rStTy := rStTy) envMap v).cost ≤ 2
  | _, .zero => by simp [liftEnvFold, Expr.cost]
  | _, .succ .zero => by simp [liftEnvFold, Expr.cost]
  | _, .succ (.succ w) => by simp only [liftEnvFold, exprWk1_cost]; exact h w

theorem envMap_liftEnvPred2_cost {S : Sig} {O : Ops S} {a x : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (h : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: Γ) u), (liftEnvPred2 (x := x) envMap v).cost ≤ 2
  | _, .zero => by simp [liftEnvPred2, Expr.cost]
  | _, .succ w => by simp only [liftEnvPred2, exprWk1_cost]; exact h w

theorem envMap_liftEnvMk3_cost {S : Sig} {O : Ops S} {a y x : Ty S} {Γ Δ : List (Ty S)}
    {envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u}
    (h : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2) :
    ∀ ⦃u⦄ (v : Var (a :: Γ) u), (liftEnvMk3 (y := y) (x := x) envMap v).cost ≤ 2
  | _, .zero => by simp [liftEnvMk3, Expr.cost]
  | _, .succ w => by simp only [liftEnvMk3, exprWk1_cost]; exact h w

theorem envId1_cost {S : Sig} {O : Ops S} {a : Ty S} :
    ∀ ⦃u⦄ (v : Var [a] u), (envId1 (O := O) v).cost ≤ 2
  | _, .zero => by simp [envId1, Expr.cost]

theorem envFst2_cost {S : Sig} {O : Ops S} {a b r : Ty S} :
    ∀ ⦃u⦄ (v : Var [a, b] u), (envFst2 (O := O) (r := r) v).cost ≤ 2
  | _, .zero => by simp [envFst2, Expr.cost]
  | _, .succ .zero => by simp [envFst2, Expr.cost]

theorem envSwapFst2_cost {S : Sig} {O : Ops S} {a b r : Ty S} :
    ∀ ⦃u⦄ (v : Var [a, b] u), (envSwapFst2 (O := O) (r := r) v).cost ≤ 2
  | _, .zero => by simp [envSwapFst2, Expr.cost]
  | _, .succ .zero => by simp [envSwapFst2, Expr.cost]

theorem substNoQueryComp_queries {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (wT₂ : I₂.Tag → ℕ)
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).queries wT₂ (fun _ => 0) = 0)
    {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
    (c : Comp O I₁ Γ t) (hc : c.queries (fun _ => 1) (fun _ => 0) = 0) :
    (substNoQueryComp mapSamp envMap c hc).queries wT₂ (fun _ => 0) = 0 := by
  induction c generalizing Δ with
  | ret _ => rfl
  | bind c k ihc ihk =>
    simp [substNoQueryComp, Comp.queries,
      ihc envMap (by simp [Comp.queries] at hc; omega),
      ihk (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)]
  | ite _ c d ihc ihd =>
    simp [substNoQueryComp, Comp.queries,
      ihc envMap (by simp [Comp.queries] at hc; omega),
      ihd envMap (by simp [Comp.queries] at hc; omega)]
  | caseOpt _ n s ihn ihs =>
    simp [substNoQueryComp, Comp.queries,
      ihn envMap (by simp [Comp.queries] at hc; omega),
      ihs (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)]
  | caseSum _ l r ihl ihr =>
    simp [substNoQueryComp, Comp.queries,
      ihl (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega),
      ihr (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)]
  | sample s e => exact hSamp s (substExpr envMap e)
  | query _ _ => exfalso; simp [Comp.queries] at hc
  | iter n _ body ih =>
    cases n with
    | zero => simp [substNoQueryComp, Comp.queries]
    | succ n =>
      simp [substNoQueryComp, Comp.queries,
        ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)]
  | foldM K _ _ f ih =>
    cases K with
    | zero => simp [substNoQueryComp, Comp.queries]
    | succ K =>
      simp [substNoQueryComp, Comp.queries,
        ih (liftEnv2 envMap) (by simp [Comp.queries] at hc; omega)]
  | findM K _ p ih | anyM K _ p ih | mapM K _ p ih | consumeFirstM K _ p _ ih =>
    cases K with
    | zero => simp [substNoQueryComp, Comp.queries]
    | succ K =>
      simp [substNoQueryComp, Comp.queries,
        ih (liftEnv1 envMap) (by simp [Comp.queries] at hc; omega)]

theorem comp_cost_pos {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) : 1 ≤ c.cost := by
  cases c with
  | sample _ e => have := expr_cost_pos e; simp only [Comp.cost]; omega
  | query _ e => have := expr_cost_pos e; simp only [Comp.cost]; omega
  | _ => simp only [Comp.cost]; omega

theorem substNoQueryComp_cost_le {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).cost ≤ e.cost + I₁.smp.sCost s)
    {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2)
    (c : Comp O I₁ Γ t) (hc : c.queries (fun _ => 1) (fun _ => 0) = 0) :
    (substNoQueryComp mapSamp envMap c hc).cost ≤ 2 * c.cost := by
  induction c generalizing Δ with
  | ret e =>
    have he := substExpr_cost_le envMap hEnv e
    simp only [substNoQueryComp, Comp.cost]; omega
  | bind c k ihc ihk =>
    have h1 := ihc envMap hEnv (by simp [Comp.queries] at hc; omega)
    have h2 := ihk (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (by simp [Comp.queries] at hc; omega)
    simp only [substNoQueryComp, Comp.cost]; omega
  | ite b c d ihc ihd =>
    have hb := substExpr_cost_le envMap hEnv b
    have h1 := ihc envMap hEnv (by simp [Comp.queries] at hc; omega)
    have h2 := ihd envMap hEnv (by simp [Comp.queries] at hc; omega)
    simp only [substNoQueryComp, Comp.cost]; omega
  | caseOpt e n s ihn ihs =>
    have he := substExpr_cost_le envMap hEnv e
    have h1 := ihn envMap hEnv (by simp [Comp.queries] at hc; omega)
    have h2 := ihs (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (by simp [Comp.queries] at hc; omega)
    simp only [substNoQueryComp, Comp.cost]; omega
  | caseSum e l r ihl ihr =>
    have he := substExpr_cost_le envMap hEnv e
    have h1 := ihl (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (by simp [Comp.queries] at hc; omega)
    have h2 := ihr (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (by simp [Comp.queries] at hc; omega)
    simp only [substNoQueryComp, Comp.cost]; omega
  | sample s e =>
    have he := substExpr_cost_le envMap hEnv e
    have hs := hSamp s (substExpr envMap e)
    simp only [substNoQueryComp, Comp.cost]; omega
  | query _ _ => exfalso; simp [Comp.queries] at hc
  | iter n e body ih =>
    have he := substExpr_cost_le envMap hEnv e
    cases n with
    | zero => simp only [substNoQueryComp, Comp.cost]; omega
    | succ n =>
      have hb := ih (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (by simp [Comp.queries] at hc; omega)
      have hm := Nat.mul_le_mul_left (n + 1)
        (show (substNoQueryComp mapSamp (liftEnv1 envMap) body _).cost + 1 ≤ 2 * (body.cost + 1) by omega)
      have hr : (n + 1) * (2 * (body.cost + 1)) = 2 * ((n + 1) * (body.cost + 1)) := by ring
      simp only [substNoQueryComp, Comp.cost]; omega
  | foldM K l z f ih =>
    have hl := substExpr_cost_le envMap hEnv l
    have hz := substExpr_cost_le envMap hEnv z
    cases K with
    | zero => simp only [substNoQueryComp, Comp.cost]; omega
    | succ K =>
      have hf := ih (liftEnv2 envMap) (envMap_liftEnv2_cost hEnv) (by simp [Comp.queries] at hc; omega)
      have hm := Nat.mul_le_mul_left (K + 1)
        (show (substNoQueryComp mapSamp (liftEnv2 envMap) f _).cost + 1 ≤ 2 * (f.cost + 1) by omega)
      have hr : (K + 1) * (2 * (f.cost + 1)) = 2 * ((K + 1) * (f.cost + 1)) := by ring
      simp only [substNoQueryComp, Comp.cost]; omega
  | findM K l p ih | anyM K l p ih =>
    have hl := substExpr_cost_le envMap hEnv l
    cases K with
    | zero => simp only [substNoQueryComp, Comp.cost]; omega
    | succ K =>
      have hp := ih (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (by simp [Comp.queries] at hc; omega)
      have hm := Nat.mul_le_mul_left (K + 1)
        (show (substNoQueryComp mapSamp (liftEnv1 envMap) p _).cost + 1 ≤ 2 * (p.cost + 1) by omega)
      have hr : (K + 1) * (2 * (p.cost + 1)) = 2 * ((K + 1) * (p.cost + 1)) := by ring
      simp only [substNoQueryComp, Comp.cost]; omega
  | mapM K l f ih =>
    have hl := substExpr_cost_le envMap hEnv l
    have hl1 := expr_cost_pos l
    cases K with
    | zero => simp only [substNoQueryComp, Comp.cost, Expr.cost]; omega
    | succ K =>
      have hf := ih (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (by simp [Comp.queries] at hc; omega)
      have hm := Nat.mul_le_mul_left (K + 1)
        (show (substNoQueryComp mapSamp (liftEnv1 envMap) f _).cost + 1 ≤ 2 * (f.cost + 1) by omega)
      have hr : (K + 1) * (2 * (f.cost + 1)) = 2 * ((K + 1) * (f.cost + 1)) := by ring
      simp only [substNoQueryComp, Comp.cost]; omega
  | consumeFirstM K l p mk ih =>
    have hl := substExpr_cost_le envMap hEnv l
    have hl1 := expr_cost_pos l
    cases K with
    | zero => simp only [substNoQueryComp, Comp.cost, Expr.cost]; omega
    | succ K =>
      have hmk := substExpr_cost_le (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) mk
      have hp := ih (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (by simp [Comp.queries] at hc; omega)
      have hm := Nat.mul_le_mul_left (K + 1)
        (show (substNoQueryComp mapSamp (liftEnv1 envMap) p _).cost +
          (substExpr (liftEnv1 envMap) mk).cost + 1 ≤ 2 * (p.cost + mk.cost + 1) by omega)
      have hr : (K + 1) * (2 * (p.cost + mk.cost + 1)) =
          2 * ((K + 1) * (p.cost + mk.cost + 1)) := by ring
      simp only [substNoQueryComp, Comp.cost]; omega

theorem substQueryComp_queries_le {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {rStTy : Ty S}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (wT₁ : I₁.Tag → ℕ) (wT₂ : I₂.Tag → ℕ)
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).queries wT₂ (fun _ => 0) = 0)
    (hQuery : ∀ g, (qImpl g).queries wT₂ (fun _ => 0) ≤ wT₁ g)
    {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
    (rExpr : Expr O Δ rStTy)
    (c : Comp O I₁ Γ t) :
    (substQueryComp mapSamp qImpl envMap rExpr c).queries wT₂ (fun _ => 0) ≤
      c.queries wT₁ (fun _ => 0) := by
  induction c generalizing Δ with
  | ret _ => simp [substQueryComp, Comp.queries]
  | bind c k ihc ihk =>
    have h1 := ihc envMap rExpr
    have h2 := ihk (liftEnvFst envMap) (.snd (.var .zero))
    simp only [substQueryComp, Comp.queries]; omega
  | ite _ c d ihc ihd =>
    have h1 := ihc envMap rExpr
    have h2 := ihd envMap rExpr
    simp only [substQueryComp, Comp.queries]; omega
  | caseOpt _ n s ihn ihs =>
    have h1 := ihn envMap rExpr
    have h2 := ihs (liftEnv1 envMap) (exprWk1 rExpr)
    simp only [substQueryComp, Comp.queries]; omega
  | caseSum _ l r ihl ihr =>
    have h1 := ihl (liftEnv1 envMap) (exprWk1 rExpr)
    have h2 := ihr (liftEnv1 envMap) (exprWk1 rExpr)
    simp only [substQueryComp, Comp.queries]; omega
  | sample s e =>
    simp [substQueryComp, Comp.queries, hSamp s (substExpr envMap e)]
  | query g _ =>
    simpa [substQueryComp, Comp.queries, callBinaryComp_queries] using hQuery g
  | iter n _ body ih =>
    have hb := ih (liftEnvFst envMap) (.snd (.var .zero))
    simp only [substQueryComp, Comp.queries]
    exact Nat.mul_le_mul_left n hb
  | foldM K _ _ f ih =>
    have hf := ih (liftEnvFold envMap) (.snd (.var (.succ .zero)))
    simp only [substQueryComp, Comp.queries]
    exact Nat.mul_le_mul_left K hf
  | findM K l p ih =>
    cases K with
    | zero => simp [substQueryComp, Comp.queries]
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · simp [Comp.queries, substNoQueryComp_queries mapSamp wT₂ hSamp envMap _ hc0]
      · have hp := ih (liftEnvPred2 (x := .prod (.opt (listElemTy l)) rStTy) envMap)
          (.snd (.var (.succ .zero)))
        dsimp only [Comp.queries]
        exact Nat.mul_le_mul_left (K + 1) (by omega)
  | anyM K l p ih =>
    cases K with
    | zero => simp [substQueryComp, Comp.queries]
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · simp [Comp.queries, substNoQueryComp_queries mapSamp wT₂ hSamp envMap _ hc0]
      · have hp := ih (liftEnvPred2 (x := .prod .bool rStTy) envMap) (.snd (.var (.succ .zero)))
        dsimp only [Comp.queries]
        exact Nat.mul_le_mul_left (K + 1) (by omega)
  | mapM K l f ih =>
    cases K with
    | zero => simp [substQueryComp, Comp.queries]
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · simp [Comp.queries, substNoQueryComp_queries mapSamp wT₂ hSamp envMap _ hc0]
      · have hf := ih (liftEnvPred2 (x := .prod (.list (compRetTy f)) rStTy) envMap)
          (.snd (.var (.succ .zero)))
        dsimp only [Comp.queries]
        exact Nat.mul_le_mul_left (K + 1) (by omega)
  | consumeFirstM K l p mk ih =>
    cases K with
    | zero => simp [substQueryComp, Comp.queries]
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · simp [Comp.queries, substNoQueryComp_queries mapSamp wT₂ hSamp envMap _ hc0]
      · have hp := ih (liftEnvPred2 (x := .prod (.prod .bool (.list (listElemTy l))) rStTy) envMap)
          (.snd (.var (.succ .zero)))
        dsimp only [Comp.queries]
        exact Nat.mul_le_mul_left (K + 1) (by omega)

lemma findM_cost_arith (K sl lCost rCost sq pCost pqEx pq1 pNodes : ℕ)
    (hl : sl ≤ 2 * lCost) (hl1 : 1 ≤ lCost) (hqpos : 1 ≤ pq1)
    (hp : 2 * sq ≤ 7 * pCost + 2 * (1 + 1) + 2 * pqEx + 96 * pNodes * pq1) :
    2 * (sl + (1 + rCost + 1) +
        (K + 1) *
          ((1 + 1) +
            max (sq + (1 + 1 + max (1 + 1) 1 + 1 + (1 + 1) + 1 + 1) + 1) (1 + 1) + 1 + 1) + 1) ≤
      7 * (lCost + (K + 1) * (pCost + 1) + 1) + 2 * rCost + 2 * ((K + 1) * pqEx) +
        96 * (pNodes + 1) * ((K + 1) * pq1) := by
  set M := max (sq + (1 + 1 + max (1 + 1) 1 + 1 + (1 + 1) + 1 + 1) + 1) (1 + 1)
  have hM : M ≤ max (sq + 10) 2 := by omega
  have hstep : 2 * (M + 4) ≤
      7 * (pCost + 1) + 2 * pqEx + 96 * (pNodes + 1) * pq1 := by
    have : 96 * (pNodes + 1) * pq1 = 96 * pNodes * pq1 + 96 * pq1 := by ring
    omega
  have hm := Nat.mul_le_mul_left (K + 1) hstep
  have h1 : 2 * ((K + 1) * ((1 + 1) + M + 1 + 1)) = (K + 1) * (2 * (M + 4)) := by ring
  have h2 : (K + 1) * (7 * (pCost + 1) + 2 * pqEx + 96 * (pNodes + 1) * pq1) =
      7 * ((K + 1) * (pCost + 1)) + 2 * ((K + 1) * pqEx) +
        96 * (pNodes + 1) * ((K + 1) * pq1) := by ring
  omega

lemma anyM_cost_arith (K sl lCost rCost sq pCost pqEx pq1 pNodes : ℕ)
    (hl : sl ≤ 2 * lCost) (hl1 : 1 ≤ lCost) (hqpos : 1 ≤ pq1)
    (hp : 2 * sq ≤ 7 * pCost + 2 * (1 + 1) + 2 * pqEx + 96 * pNodes * pq1) :
    2 * (sl + (1 + rCost + 1) +
        (K + 1) * ((1 + 1) + max (1 + 1) sq + 1 + 1) + 1) ≤
      7 * (lCost + (K + 1) * (pCost + 1) + 1) + 2 * rCost + 2 * ((K + 1) * pqEx) +
        96 * (pNodes + 1) * ((K + 1) * pq1) := by
  set M := max (1 + 1) sq
  have hM : M ≤ max 2 sq := by omega
  have hstep : 2 * (M + 4) ≤
      7 * (pCost + 1) + 2 * pqEx + 96 * (pNodes + 1) * pq1 := by
    have : 96 * (pNodes + 1) * pq1 = 96 * pNodes * pq1 + 96 * pq1 := by ring
    omega
  have hm := Nat.mul_le_mul_left (K + 1) hstep
  have h1 : 2 * ((K + 1) * ((1 + 1) + M + 1 + 1)) = (K + 1) * (2 * (M + 4)) := by ring
  have h2 : (K + 1) * (7 * (pCost + 1) + 2 * pqEx + 96 * (pNodes + 1) * pq1) =
      7 * ((K + 1) * (pCost + 1)) + 2 * ((K + 1) * pqEx) +
        96 * (pNodes + 1) * ((K + 1) * pq1) := by ring
  omega

lemma mapM_cost_arith (K sl lCost rCost sq fCost fqEx fq1 fNodes : ℕ)
    (hl : sl ≤ 2 * lCost) (hl1 : 1 ≤ lCost) (hqpos : 1 ≤ fq1)
    (hf : 2 * sq ≤ 7 * fCost + 2 * (1 + 1) + 2 * fqEx + 96 * fNodes * fq1) :
    2 * ((sl + (1 + rCost + 1) +
          (K + 1) * (sq + (((1 + 1) + (1 + 1) + 1) + (1 + 1) + 1 + 1) + 1 + 1) + 1) +
        (((1 + 1) + 1 + (K + 1) * ((1 + 1 + 1 + 1) + 1) + 1) +
          ((1 + (1 + 1) + 1) + 1) + 1) + 1) ≤
      7 * (lCost + (K + 1) * (fCost + 1) + 1) + 2 * rCost + 2 * ((K + 1) * fqEx) +
        96 * (fNodes + 1) * ((K + 1) * fq1) := by
  have hstep : 2 * (sq + 16) + 28 ≤
      7 * (fCost + 1) + 2 * fqEx + 96 * (fNodes + 1) * fq1 := by
    have : 96 * (fNodes + 1) * fq1 = 96 * fNodes * fq1 + 96 * fq1 := by ring
    omega
  have hm := Nat.mul_le_mul_left (K + 1) hstep
  have h1 :
      2 * ((sl + (1 + rCost + 1) +
            (K + 1) * (sq + (((1 + 1) + (1 + 1) + 1) + (1 + 1) + 1 + 1) + 1 + 1) + 1) +
          (((1 + 1) + 1 + (K + 1) * ((1 + 1 + 1 + 1) + 1) + 1) +
            ((1 + (1 + 1) + 1) + 1) + 1) + 1) + K * 28 =
        2 * sl + 2 * rCost + (K + 1) * (2 * (sq + 16) + 28) := by ring
  have h2 : (K + 1) * (7 * (fCost + 1) + 2 * fqEx + 96 * (fNodes + 1) * fq1) =
      7 * ((K + 1) * (fCost + 1)) + 2 * ((K + 1) * fqEx) +
        96 * (fNodes + 1) * ((K + 1) * fq1) := by ring
  omega

lemma consumeFirstM_cost_arith (K sl lCost rCost smk mkCost sq pCost pqEx pq1 pNodes : ℕ)
    (hl : sl ≤ 2 * lCost) (hl1 : 1 ≤ lCost)
    (hmk : smk ≤ 2 * mkCost) (_hmk1 : 1 ≤ mkCost) (hqpos : 1 ≤ pq1)
    (hp : 2 * sq ≤ 7 * pCost + 2 * (1 + 1) + 2 * pqEx + 96 * pNodes * pq1) :
    2 * ((sl + ((1 + 1 + 1) + rCost + 1) +
          (K + 1) *
            ((1 + 1 + 1) +
              max (((1 + (1 + (1 + 1 + 1) + 1) + 1) + (1 + 1) + 1) + 1)
                (sq +
                  ((1 + 1) +
                    max (((1 + (smk + (1 + 1 + 1) + 1) + 1) + (1 + 1) + 1) + 1)
                      (((1 + (1 + (1 + 1 + 1) + 1) + 1) + (1 + 1) + 1) + 1) + 1) + 1) + 1 + 1) + 1) +
        ((((1 + 1 + 1) + 1 + (K + 1) * ((1 + 1 + 1 + 1) + 1) + 1) +
          ((((1 + 1 + 1) + 1 + 1) + (1 + 1) + 1) + 1) + 1)) + 1) ≤
      7 * (lCost + (K + 1) * (pCost + mkCost + 1) + 1) + 2 * rCost + 2 * ((K + 1) * pqEx) +
        96 * (pNodes + 1) * ((K + 1) * pq1) := by
  set M := max (((1 + (1 + (1 + 1 + 1) + 1) + 1) + (1 + 1) + 1) + 1)
    (sq +
      ((1 + 1) +
        max (((1 + (smk + (1 + 1 + 1) + 1) + 1) + (1 + 1) + 1) + 1)
          (((1 + (1 + (1 + 1 + 1) + 1) + 1) + (1 + 1) + 1) + 1) + 1) + 1)
  have hM : M ≤ max 12 (sq + max (smk + 11) 12 + 4) := by omega
  have hstep : 2 * (M + 10) + 42 ≤
      7 * (pCost + mkCost + 1) + 2 * pqEx + 96 * (pNodes + 1) * pq1 := by
    have : 96 * (pNodes + 1) * pq1 = 96 * pNodes * pq1 + 96 * pq1 := by ring
    omega
  have hm := Nat.mul_le_mul_left (K + 1) hstep
  have h1 :
      2 * ((sl + ((1 + 1 + 1) + rCost + 1) +
            (K + 1) * ((1 + 1 + 1) + M + 1 + 1) + 1) +
          ((((1 + 1 + 1) + 1 + (K + 1) * ((1 + 1 + 1 + 1) + 1) + 1) +
            ((((1 + 1 + 1) + 1 + 1) + (1 + 1) + 1) + 1) + 1)) + 1) + K * 42 =
        2 * sl + 2 * rCost + (K + 1) * (2 * (M + 10) + 42) := by ring
  have h2 : (K + 1) * (7 * (pCost + mkCost + 1) + 2 * pqEx + 96 * (pNodes + 1) * pq1) =
      7 * ((K + 1) * (pCost + mkCost + 1)) + 2 * ((K + 1) * pqEx) +
        96 * (pNodes + 1) * ((K + 1) * pq1) := by ring
  omega

set_option maxHeartbeats 400000 in
theorem substQueryComp_cost_le {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {rStTy : Ty S}
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (qEx : I₁.Tag → ℕ)
    (hsPos : ∀ s, 1 ≤ I₁.smp.sCost s)
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).cost ≤ e.cost + I₁.smp.sCost s)
    (hQuery : ∀ g, (qImpl g).cost + 10 ≤ 3 * I₁.qCost g + qEx g)
    {Γ Δ : List (Ty S)} {t : Ty S}
    (envMap : ∀ ⦃u⦄, Var Γ u → Expr O Δ u)
    (hEnv : ∀ ⦃u⦄ (v : Var Γ u), (envMap v).cost ≤ 2)
    (rExpr : Expr O Δ rStTy)
    (c : Comp O I₁ Γ t) :
    2 * (substQueryComp mapSamp qImpl envMap rExpr c).cost ≤
      7 * c.cost + 2 * rExpr.cost + 2 * c.queries qEx (fun _ => 0) +
        96 * compListMNodes c * c.queries (fun _ => 1) (fun _ => 0) := by
  induction c generalizing Δ with
  | ret e =>
    have he := substExpr_cost_le envMap hEnv e
    have he1 := expr_cost_pos e
    simp only [substQueryComp, Comp.cost, Expr.cost, Comp.queries, compListMNodes]; omega
  | bind c k ihc ihk =>
    have hc := ihc envMap hEnv rExpr
    have hk := ihk (liftEnvFst envMap) (envMap_liftEnvFst_cost hEnv) (.snd (.var .zero))
    simp only [Expr.cost] at hk
    simp only [substQueryComp, Comp.cost, Comp.queries, compListMNodes]
    have hmc : 96 * compListMNodes c * c.queries (fun _ => 1) (fun _ => 0) ≤
        96 * (compListMNodes c + compListMNodes k) * c.queries (fun _ => 1) (fun _ => 0) :=
      Nat.mul_le_mul_right _ (by omega)
    have hmk : 96 * compListMNodes k * k.queries (fun _ => 1) (fun _ => 0) ≤
        96 * (compListMNodes c + compListMNodes k) * k.queries (fun _ => 1) (fun _ => 0) :=
      Nat.mul_le_mul_right _ (by omega)
    have hsum :
        96 * (compListMNodes c + compListMNodes k) * c.queries (fun _ => 1) (fun _ => 0) +
          96 * (compListMNodes c + compListMNodes k) * k.queries (fun _ => 1) (fun _ => 0) =
        96 * (compListMNodes c + compListMNodes k) *
          (c.queries (fun _ => 1) (fun _ => 0) + k.queries (fun _ => 1) (fun _ => 0)) := by ring
    omega
  | ite b c d ihc ihd =>
    have hb := substExpr_cost_le envMap hEnv b
    have hc := ihc envMap hEnv rExpr
    have hd := ihd envMap hEnv rExpr
    have hmc : 96 * compListMNodes c * c.queries (fun _ => 1) (fun _ => 0) ≤
        96 * (compListMNodes c + compListMNodes d) *
          max (c.queries (fun _ => 1) (fun _ => 0)) (d.queries (fun _ => 1) (fun _ => 0)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 96 (Nat.le_add_right _ _)) (Nat.le_max_left _ _)
    have hmd : 96 * compListMNodes d * d.queries (fun _ => 1) (fun _ => 0) ≤
        96 * (compListMNodes c + compListMNodes d) *
          max (c.queries (fun _ => 1) (fun _ => 0)) (d.queries (fun _ => 1) (fun _ => 0)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 96 (Nat.le_add_left _ _)) (Nat.le_max_right _ _)
    simp only [substQueryComp, Comp.cost, Comp.queries, compListMNodes]; omega
  | caseOpt e n s ihn ihs =>
    have he := substExpr_cost_le envMap hEnv e
    have hn := ihn envMap hEnv rExpr
    have hs := ihs (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (exprWk1 rExpr)
    rw [exprWk1_cost] at hs
    have hmn : 96 * compListMNodes n * n.queries (fun _ => 1) (fun _ => 0) ≤
        96 * (compListMNodes n + compListMNodes s) *
          max (n.queries (fun _ => 1) (fun _ => 0)) (s.queries (fun _ => 1) (fun _ => 0)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 96 (Nat.le_add_right _ _)) (Nat.le_max_left _ _)
    have hms : 96 * compListMNodes s * s.queries (fun _ => 1) (fun _ => 0) ≤
        96 * (compListMNodes n + compListMNodes s) *
          max (n.queries (fun _ => 1) (fun _ => 0)) (s.queries (fun _ => 1) (fun _ => 0)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 96 (Nat.le_add_left _ _)) (Nat.le_max_right _ _)
    simp only [substQueryComp, Comp.cost, Comp.queries, compListMNodes]; omega
  | caseSum e l r ihl ihr =>
    have he := substExpr_cost_le envMap hEnv e
    have hl := ihl (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (exprWk1 rExpr)
    have hr := ihr (liftEnv1 envMap) (envMap_liftEnv1_cost hEnv) (exprWk1 rExpr)
    rw [exprWk1_cost] at hl hr
    have hml : 96 * compListMNodes l * l.queries (fun _ => 1) (fun _ => 0) ≤
        96 * (compListMNodes l + compListMNodes r) *
          max (l.queries (fun _ => 1) (fun _ => 0)) (r.queries (fun _ => 1) (fun _ => 0)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 96 (Nat.le_add_right _ _)) (Nat.le_max_left _ _)
    have hmr : 96 * compListMNodes r * r.queries (fun _ => 1) (fun _ => 0) ≤
        96 * (compListMNodes l + compListMNodes r) *
          max (l.queries (fun _ => 1) (fun _ => 0)) (r.queries (fun _ => 1) (fun _ => 0)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 96 (Nat.le_add_left _ _)) (Nat.le_max_right _ _)
    simp only [substQueryComp, Comp.cost, Comp.queries, compListMNodes]; omega
  | sample s e =>
    have he := substExpr_cost_le envMap hEnv e
    have he1 := expr_cost_pos e
    have hs1 := hsPos s
    have hs := hSamp s (substExpr envMap e)
    simp only [substQueryComp, Comp.cost, Expr.cost, exprWk1_cost, Comp.queries, compListMNodes]
    omega
  | query g e =>
    have he := substExpr_cost_le envMap hEnv e
    have he1 := expr_cost_pos e
    have hq := hQuery g
    simp only [substQueryComp, Comp.cost, Expr.cost, callBinaryComp_cost, Comp.queries,
      compListMNodes]
    omega
  | iter n e body ih =>
    have he := substExpr_cost_le envMap hEnv e
    have he1 := expr_cost_pos e
    have hb := ih (liftEnvFst envMap) (envMap_liftEnvFst_cost hEnv) (.snd (.var .zero))
    simp only [Expr.cost] at hb
    simp only [substQueryComp, Comp.cost, Expr.cost, Comp.queries, compListMNodes]
    have hm := Nat.mul_le_mul_left n
      (show 2 * ((substQueryComp mapSamp qImpl (liftEnvFst envMap) (.snd (.var .zero)) body).cost + 1) ≤
        7 * (body.cost + 1) + 2 * body.queries qEx (fun _ => 0) +
          96 * compListMNodes body * body.queries (fun _ => 1) (fun _ => 0) by omega)
    have hring1 : 2 * (n * ((substQueryComp mapSamp qImpl (liftEnvFst envMap) (.snd (.var .zero)) body).cost + 1)) =
        n * (2 * ((substQueryComp mapSamp qImpl (liftEnvFst envMap) (.snd (.var .zero)) body).cost + 1)) := by ring
    have hring2 : n * (7 * (body.cost + 1) + 2 * body.queries qEx (fun _ => 0) +
          96 * compListMNodes body * body.queries (fun _ => 1) (fun _ => 0)) =
        7 * (n * (body.cost + 1)) + 2 * (n * body.queries qEx (fun _ => 0)) +
          96 * compListMNodes body * (n * body.queries (fun _ => 1) (fun _ => 0)) := by ring
    omega
  | foldM K l z f ih =>
    have hl := substExpr_cost_le envMap hEnv l
    have hl1 := expr_cost_pos l
    have hz := substExpr_cost_le envMap hEnv z
    have hz1 := expr_cost_pos z
    have hf := ih (liftEnvFold envMap) (envMap_liftEnvFold_cost hEnv) (.snd (.var (.succ .zero)))
    simp only [Expr.cost] at hf
    simp only [substQueryComp, Comp.cost, Expr.cost, Comp.queries, compListMNodes]
    have hm := Nat.mul_le_mul_left K
      (show 2 * ((substQueryComp mapSamp qImpl (liftEnvFold envMap) (.snd (.var (.succ .zero))) f).cost + 1) ≤
        7 * (f.cost + 1) + 2 * f.queries qEx (fun _ => 0) +
          96 * compListMNodes f * f.queries (fun _ => 1) (fun _ => 0) by omega)
    have hring1 : 2 * (K * ((substQueryComp mapSamp qImpl (liftEnvFold envMap) (.snd (.var (.succ .zero))) f).cost + 1)) =
        K * (2 * ((substQueryComp mapSamp qImpl (liftEnvFold envMap) (.snd (.var (.succ .zero))) f).cost + 1)) := by ring
    have hring2 : K * (7 * (f.cost + 1) + 2 * f.queries qEx (fun _ => 0) +
          96 * compListMNodes f * f.queries (fun _ => 1) (fun _ => 0)) =
        7 * (K * (f.cost + 1)) + 2 * (K * f.queries qEx (fun _ => 0)) +
          96 * compListMNodes f * (K * f.queries (fun _ => 1) (fun _ => 0)) := by ring
    omega
  | findM K l p ih =>
    have hl := substExpr_cost_le envMap hEnv l
    have hl1 := expr_cost_pos l
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.cost, Expr.cost, Comp.queries, compListMNodes]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hno := substNoQueryComp_cost_le mapSamp hSamp envMap hEnv (.findM (K + 1) l p) hc0
        have hp1 := comp_cost_pos p
        have hkp : 2 ≤ (K + 1) * (p.cost + 1) := by
          calc 2 = 1 * 2 := rfl
            _ ≤ (K + 1) * (p.cost + 1) := Nat.mul_le_mul (by omega) (by omega)
        simp only [Comp.cost, Expr.cost, exprWk1_cost, Comp.queries, compListMNodes] at hno ⊢
        omega
      · have hp := ih (liftEnvPred2 (x := .prod (.opt (listElemTy l)) rStTy) envMap)
          (envMap_liftEnvPred2_cost hEnv) (.snd (.var (.succ .zero)))
        simp only [Expr.cost] at hp
        have hqpos : 1 ≤ p.queries (fun _ => 1) (fun _ => 0) := by
          rcases Nat.eq_zero_or_pos (p.queries (fun _ => 1) (fun _ => 0)) with h0 | hpos
          · exfalso; exact hc0 (by simp [Comp.queries, h0])
          · exact hpos
        simp only [Comp.cost, Expr.cost, Comp.queries, compListMNodes]
        exact findM_cost_arith K _ _ _ _ _ _ _ _ hl hl1 hqpos hp
  | anyM K l p ih =>
    have hl := substExpr_cost_le envMap hEnv l
    have hl1 := expr_cost_pos l
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.cost, Expr.cost, Comp.queries, compListMNodes]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hno := substNoQueryComp_cost_le mapSamp hSamp envMap hEnv (.anyM (K + 1) l p) hc0
        have hp1 := comp_cost_pos p
        have hkp : 2 ≤ (K + 1) * (p.cost + 1) := by
          calc 2 = 1 * 2 := rfl
            _ ≤ (K + 1) * (p.cost + 1) := Nat.mul_le_mul (by omega) (by omega)
        simp only [Comp.cost, Expr.cost, exprWk1_cost, Comp.queries, compListMNodes] at hno ⊢
        omega
      · have hp := ih (liftEnvPred2 (x := .prod .bool rStTy) envMap)
          (envMap_liftEnvPred2_cost hEnv) (.snd (.var (.succ .zero)))
        simp only [Expr.cost] at hp
        have hqpos : 1 ≤ p.queries (fun _ => 1) (fun _ => 0) := by
          rcases Nat.eq_zero_or_pos (p.queries (fun _ => 1) (fun _ => 0)) with h0 | hpos
          · exfalso; exact hc0 (by simp [Comp.queries, h0])
          · exact hpos
        simp only [Comp.cost, Expr.cost, Comp.queries, compListMNodes]
        exact anyM_cost_arith K _ _ _ _ _ _ _ _ hl hl1 hqpos hp
  | mapM K l f ih =>
    have hl := substExpr_cost_le envMap hEnv l
    have hl1 := expr_cost_pos l
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.cost, Expr.cost, Comp.queries, compListMNodes]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hno := substNoQueryComp_cost_le mapSamp hSamp envMap hEnv (.mapM (K + 1) l f) hc0
        have hf1 := comp_cost_pos f
        have hkf : 2 ≤ (K + 1) * (f.cost + 1) := by
          calc 2 = 1 * 2 := rfl
            _ ≤ (K + 1) * (f.cost + 1) := Nat.mul_le_mul (by omega) (by omega)
        simp only [Comp.cost, Expr.cost, exprWk1_cost, Comp.queries, compListMNodes] at hno ⊢
        omega
      · have hf := ih (liftEnvPred2 (x := .prod (.list (compRetTy f)) rStTy) envMap)
          (envMap_liftEnvPred2_cost hEnv) (.snd (.var (.succ .zero)))
        simp only [Expr.cost] at hf
        have hqpos : 1 ≤ f.queries (fun _ => 1) (fun _ => 0) := by
          rcases Nat.eq_zero_or_pos (f.queries (fun _ => 1) (fun _ => 0)) with h0 | hpos
          · exfalso; exact hc0 (by simp [Comp.queries, h0])
          · exact hpos
        simp only [Comp.cost, Expr.cost, Comp.queries, compListMNodes]
        exact mapM_cost_arith K _ _ _ _ _ _ _ _ hl hl1 hqpos hf
  | consumeFirstM K l p mk ih =>
    have hl := substExpr_cost_le envMap hEnv l
    have hl1 := expr_cost_pos l
    cases K with
    | zero =>
      simp only [substQueryComp, Comp.cost, Expr.cost, Comp.queries, compListMNodes]; omega
    | succ K =>
      dsimp only [substQueryComp]
      split_ifs with hc0
      · have hno := substNoQueryComp_cost_le mapSamp hSamp envMap hEnv
          (.consumeFirstM (K + 1) l p mk) hc0
        have hp1 := comp_cost_pos p
        have hmk1 := expr_cost_pos mk
        have hkp : 3 ≤ (K + 1) * (p.cost + mk.cost + 1) := by
          calc 3 = 1 * 3 := rfl
            _ ≤ (K + 1) * (p.cost + mk.cost + 1) := Nat.mul_le_mul (by omega) (by omega)
        simp only [Comp.cost, Expr.cost, exprWk1_cost, Comp.queries, compListMNodes] at hno ⊢
        omega
      · have hmk := substExpr_cost_le
          (liftEnvMk3 (y := .prod .bool rStTy)
            (x := .prod (.prod .bool (.list (listElemTy l))) rStTy) envMap)
          (envMap_liftEnvMk3_cost hEnv) mk
        have hmk1 := expr_cost_pos mk
        have hp := ih (liftEnvPred2 (x := .prod (.prod .bool (.list (listElemTy l))) rStTy) envMap)
          (envMap_liftEnvPred2_cost hEnv) (.snd (.var (.succ .zero)))
        simp only [Expr.cost] at hp
        have hqpos : 1 ≤ p.queries (fun _ => 1) (fun _ => 0) := by
          rcases Nat.eq_zero_or_pos (p.queries (fun _ => 1) (fun _ => 0)) with h0 | hpos
          · exfalso; exact hc0 (by simp [Comp.queries, h0])
          · exact hpos
        simp only [Comp.cost, Expr.cost, Comp.queries, compListMNodes]
        exact consumeFirstM_cost_arith K _ _ _ _ _ _ _ _ _ _ hl hl1 hmk hmk1 hqpos hp

theorem substQueryRed_totalQueries_le {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {κ : Type} {G : OracleSpec κ} {C_game : GameCodec S G}
    {rIn aIn aOut out rStTy : Ty S}
    (rInit : Expr O [rIn] rStTy)
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (wT₁ : I₁.Tag → ℕ) (wT₂ : I₂.Tag → ℕ)
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).queries wT₂ (fun _ => 0) = 0)
    (hQuery : ∀ g, (qImpl g).queries wT₂ (fun _ => 0) ≤ wT₁ g)
    (R : CostedReduction O I₁ G C_game rIn aIn aOut out) (q : ℕ) :
    (substQueryRed rInit mapSamp qImpl R).totalQueries wT₂ (fun _ => 0) q ≤
      R.totalQueries wT₁ (fun _ => 0) q := by
  have hi := substQueryComp_queries_le mapSamp qImpl wT₁ wT₂ hSamp hQuery envId1 rInit R.init
  have hh := substQueryComp_queries_le mapSamp qImpl wT₁ wT₂ hSamp hQuery envFst2
    (.snd (.var .zero)) R.handle
  have hf := substQueryComp_queries_le mapSamp qImpl wT₁ wT₂ hSamp hQuery envFst2
    (.snd (.var .zero)) R.finish
  have hmh := Nat.mul_le_mul_left q hh
  simp only [substQueryRed, CostedReduction.totalQueries, Comp.queries, Nat.add_zero]
  omega

theorem substQueryRed_totalCost_le {S : Sig} {O : Ops S}
    {ι₁ : Type} {T₁ : OracleSpec ι₁} {I₁ : Iface S T₁}
    {ι₂ : Type} {T₂ : OracleSpec ι₂} {I₂ : Iface S T₂}
    {κ : Type} {G : OracleSpec κ} {C_game : GameCodec S G}
    {rIn aIn aOut out rStTy : Ty S}
    (rInit : Expr O [rIn] rStTy)
    (mapSamp : ∀ (s : I₁.smp.Samp) {Δ : List (Ty S)},
      Expr O Δ (I₁.smp.sDom s) → Comp O I₂ Δ (I₁.smp.sTy s))
    (qImpl : (g : I₁.Tag) → Comp O I₂ [I₁.dom g, rStTy] (.prod (I₁.cod g) rStTy))
    (qEx : I₁.Tag → ℕ)
    (huCost : I₂.uCost ≤ 3 * I₁.uCost)
    (hsPos : ∀ s, 1 ≤ I₁.smp.sCost s)
    (hSamp : ∀ s {Δ} (e : Expr O Δ _), (mapSamp s e).cost ≤ e.cost + I₁.smp.sCost s)
    (hQuery : ∀ g, (qImpl g).cost + 10 ≤ 3 * I₁.qCost g + qEx g)
    (R : CostedReduction O I₁ G C_game rIn aIn aOut out) (q : ℕ) :
    2 * (substQueryRed rInit mapSamp qImpl R).totalCost q ≤
      7 * R.totalCost q + 2 * rInit.cost + 60 + 28 * q +
        2 * R.totalQueries qEx (fun _ => 0) q +
        96 * (compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish) *
          R.totalQueries (fun _ => 1) (fun _ => 0) q := by
  have hi := substQueryComp_cost_le mapSamp qImpl qEx hsPos hSamp hQuery envId1 envId1_cost
    rInit R.init
  have hh := substQueryComp_cost_le mapSamp qImpl qEx hsPos hSamp hQuery envFst2 envFst2_cost
    (.snd (.var .zero)) R.handle
  have hf := substQueryComp_cost_le mapSamp qImpl qEx hsPos hSamp hQuery envFst2 envFst2_cost
    (.snd (.var .zero)) R.finish
  simp only [Expr.cost] at hh hf
  simp only [substQueryRed, CostedReduction.totalCost, CostedReduction.totalQueries, Comp.cost,
    Expr.cost]
  set sh := (substQueryComp mapSamp qImpl envFst2 (.snd (.var .zero)) R.handle).cost
  set M2 := max I₂.uCost (sh + (((1 + 1 + 1) + ((1 + 1 + 1) + (1 + 1) + 1) + 1) + 1) + 1 + C_game.codecCost)
  set M1 := max I₁.uCost (R.handle.cost + C_game.codecCost)
  have hmax : 2 * M2 ≤
      7 * M1 + 28 +
        2 * R.handle.queries qEx (fun _ => 0) +
        96 * compListMNodes R.handle * R.handle.queries (fun _ => 1) (fun _ => 0) := by
    omega
  have hmh := Nat.mul_le_mul_left q hmax
  have hm_l : 2 * (q * M2) = q * (2 * M2) := by ring
  have hm_eq :
      q * (7 * M1 + 28 +
        2 * R.handle.queries qEx (fun _ => 0) +
        96 * compListMNodes R.handle * R.handle.queries (fun _ => 1) (fun _ => 0)) =
      7 * (q * M1) + 28 * q +
        2 * (q * R.handle.queries qEx (fun _ => 0)) +
        96 * compListMNodes R.handle * (q * R.handle.queries (fun _ => 1) (fun _ => 0)) := by ring
  set N := compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish
  have hLi : 96 * compListMNodes R.init * R.init.queries (fun _ => 1) (fun _ => 0) ≤
      96 * N * R.init.queries (fun _ => 1) (fun _ => 0) :=
    Nat.mul_le_mul_right _ (by omega)
  have hLh : 96 * compListMNodes R.handle * (q * R.handle.queries (fun _ => 1) (fun _ => 0)) ≤
      96 * N * (q * R.handle.queries (fun _ => 1) (fun _ => 0)) :=
    Nat.mul_le_mul_right _ (by omega)
  have hLf : 96 * compListMNodes R.finish * R.finish.queries (fun _ => 1) (fun _ => 0) ≤
      96 * N * R.finish.queries (fun _ => 1) (fun _ => 0) :=
    Nat.mul_le_mul_right _ (by omega)
  have hLsum :
      96 * N * R.init.queries (fun _ => 1) (fun _ => 0) +
        96 * N * (q * R.handle.queries (fun _ => 1) (fun _ => 0)) +
        96 * N * R.finish.queries (fun _ => 1) (fun _ => 0) =
      96 * N * (R.init.queries (fun _ => 1) (fun _ => 0) +
        q * R.handle.queries (fun _ => 1) (fun _ => 0) +
        R.finish.queries (fun _ => 1) (fun _ => 0)) := by ring
  omega

/-! ## 4. Lifting `atomicFsOps` ASTs to `atomicFig8Ops` -/

@[expose] def liftFsExpr {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} :
    Expr (atomicFsOps ℓ Pt C encT) Γ t →
      Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ t
  | .var v => .var v
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .add a b => .add (liftFsExpr a) (liftFsExpr b)
  | .sub a b => .sub (liftFsExpr a) (liftFsExpr b)
  | .mulK k a => .mulK k (liftFsExpr a)
  | .divK k a => .divK k (liftFsExpr a)
  | .modK k a => .modK k (liftFsExpr a)
  | .lt a b => .lt (liftFsExpr a) (liftFsExpr b)
  | .eqN a b => .eqN (liftFsExpr a) (liftFsExpr b)
  | .not a => .not (liftFsExpr a)
  | .and a b => .and (liftFsExpr a) (liftFsExpr b)
  | .ite c a b => .ite (liftFsExpr c) (liftFsExpr a) (liftFsExpr b)
  | .pair a b => .pair (liftFsExpr a) (liftFsExpr b)
  | .fst a => .fst (liftFsExpr a)
  | .snd a => .snd (liftFsExpr a)
  | .inl a => .inl (liftFsExpr a)
  | .inr a => .inr (liftFsExpr a)
  | .none => .none
  | .some a => .some (liftFsExpr a)
  | .caseOpt e n s => .caseOpt (liftFsExpr e) (liftFsExpr n) (liftFsExpr s)
  | .caseSum e l r => .caseSum (liftFsExpr e) (liftFsExpr l) (liftFsExpr r)
  | .letE e b => .letE (liftFsExpr e) (liftFsExpr b)
  | .op o a => Expr.op (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (Sum.inl o) (liftFsExpr a)
  | .nil => .nil
  | .cons x l => .cons (liftFsExpr x) (liftFsExpr l)
  | .len l => .len (liftFsExpr l)
  | .take n l => .take (liftFsExpr n) (liftFsExpr l)
  | .appendL K a b => .appendL K (liftFsExpr a) (liftFsExpr b)
  | .findB K l p => .findB K (liftFsExpr l) (liftFsExpr p)
  | .anyB K l p => .anyB K (liftFsExpr l) (liftFsExpr p)
  | .mapB K l f => .mapB K (liftFsExpr l) (liftFsExpr f)
  | .foldrB K l z f => .foldrB K (liftFsExpr l) (liftFsExpr z) (liftFsExpr f)
  | .tconst a => .tconst (liftFsExpr a)
  | .tget m i => .tget (liftFsExpr m) (liftFsExpr i)
  | .tset m i a => .tset (liftFsExpr m) (liftFsExpr i) (liftFsExpr a)

@[expose] def liftBaseSamp {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    (s : UniformSamplerTag ReductionDsl.AtomicBaseUnif)
    (e : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ
      ((ReductionDsl.atomicBaseSamplers ℓ Pt).sDom s)) :
    Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt) Γ
      ((ReductionDsl.atomicBaseSamplers ℓ Pt).sTy s) :=
  match s with
  | .bool =>
    Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (I := fsaeadHeaderIface ℓ Pt)
      .bool e
  | .index N =>
    Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (I := fsaeadHeaderIface ℓ Pt)
      (.index N) e
  | .base .bv128 =>
    Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (I := fsaeadHeaderIface ℓ Pt)
      (.base .bv128) e
  | .base .bv256 =>
    Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (I := fsaeadHeaderIface ℓ Pt)
      (.base .bv256) e
  | .base .bv512 =>
    Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (I := fsaeadHeaderIface ℓ Pt)
      (.base .bv512) e

@[expose] def liftFsCoinComp {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} :
    Comp (atomicFsOps ℓ Pt C encT) (coinOnlyBaseIface ℓ Pt) Γ t →
      Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt) Γ t
  | .ret e => .ret (liftFsExpr e)
  | .bind c k => .bind (liftFsCoinComp c) (liftFsCoinComp k)
  | .ite b c d => .ite (liftFsExpr b) (liftFsCoinComp c) (liftFsCoinComp d)
  | .caseOpt e n s => .caseOpt (liftFsExpr e) (liftFsCoinComp n) (liftFsCoinComp s)
  | .caseSum e l r => .caseSum (liftFsExpr e) (liftFsCoinComp l) (liftFsCoinComp r)
  | .sample s e => liftBaseSamp s (liftFsExpr e)
  | .query g _ => nomatch g
  | .iter n e body => .iter n (liftFsExpr e) (liftFsCoinComp body)
  | .findM K l p => .findM K (liftFsExpr l) (liftFsCoinComp p)
  | .anyM K l p => .anyM K (liftFsExpr l) (liftFsCoinComp p)
  | .mapM K l f => .mapM K (liftFsExpr l) (liftFsCoinComp f)
  | .consumeFirstM K l p mk =>
    .consumeFirstM K (liftFsExpr l) (liftFsCoinComp p) (liftFsExpr mk)
  | .foldM K l z f => .foldM K (liftFsExpr l) (liftFsExpr z) (liftFsCoinComp f)

@[expose] def liftFsSlotComp {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} :
    Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t →
      Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (slotOtccaTargetIface ℓ Pt) Γ t
  | .ret e => .ret (liftFsExpr e)
  | .bind c k => .bind (liftFsSlotComp c) (liftFsSlotComp k)
  | .ite b c d => .ite (liftFsExpr b) (liftFsSlotComp c) (liftFsSlotComp d)
  | .caseOpt e n s => .caseOpt (liftFsExpr e) (liftFsSlotComp n) (liftFsSlotComp s)
  | .caseSum e l r => .caseSum (liftFsExpr e) (liftFsSlotComp l) (liftFsSlotComp r)
  | .sample s e =>
    Comp.sample (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (I := slotOtccaTargetIface ℓ Pt)
      s (liftFsExpr e)
  | .query g e =>
    Comp.query (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (I := slotOtccaTargetIface ℓ Pt)
      g (liftFsExpr e)
  | .iter n e body => .iter n (liftFsExpr e) (liftFsSlotComp body)
  | .findM K l p => .findM K (liftFsExpr l) (liftFsSlotComp p)
  | .anyM K l p => .anyM K (liftFsExpr l) (liftFsSlotComp p)
  | .mapM K l f => .mapM K (liftFsExpr l) (liftFsSlotComp f)
  | .consumeFirstM K l p mk =>
    .consumeFirstM K (liftFsExpr l) (liftFsSlotComp p) (liftFsExpr mk)
  | .foldM K l z f => .foldM K (liftFsExpr l) (liftFsExpr z) (liftFsSlotComp f)

@[expose] def liftNoQuerySlotComp {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (dflt : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [] (.opt wireSaltCtT))
    (dfltM : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [] (.opt PlainT)) :
    Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t →
      Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt) Γ t
  | .ret e => .ret (liftFsExpr e)
  | .bind c k => .bind (liftNoQuerySlotComp dflt dfltM c) (liftNoQuerySlotComp dflt dfltM k)
  | .ite b c d =>
    .ite (liftFsExpr b) (liftNoQuerySlotComp dflt dfltM c) (liftNoQuerySlotComp dflt dfltM d)
  | .caseOpt e n s =>
    .caseOpt (liftFsExpr e) (liftNoQuerySlotComp dflt dfltM n) (liftNoQuerySlotComp dflt dfltM s)
  | .caseSum e l r =>
    .caseSum (liftFsExpr e) (liftNoQuerySlotComp dflt dfltM l) (liftNoQuerySlotComp dflt dfltM r)
  | .sample s e => liftBaseSamp s (liftFsExpr e)
  | .query OTCCATag.enc _ => .ret (dflt.renameM renEmpty)
  | .query OTCCATag.dec _ => .ret (dfltM.renameM renEmpty)
  | .iter n e body => .iter n (liftFsExpr e) (liftNoQuerySlotComp dflt dfltM body)
  | .findM K l p => .findM K (liftFsExpr l) (liftNoQuerySlotComp dflt dfltM p)
  | .anyM K l p => .anyM K (liftFsExpr l) (liftNoQuerySlotComp dflt dfltM p)
  | .mapM K l f => .mapM K (liftFsExpr l) (liftNoQuerySlotComp dflt dfltM f)
  | .consumeFirstM K l p mk =>
    .consumeFirstM K (liftFsExpr l) (liftNoQuerySlotComp dflt dfltM p) (liftFsExpr mk)
  | .foldM K l z f =>
    .foldM K (liftFsExpr l) (liftFsExpr z) (liftNoQuerySlotComp dflt dfltM f)

theorem liftFsExpr_cost {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (e : Expr (atomicFsOps ℓ Pt C encT) Γ t) :
    (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam) e).cost = e.cost := by
  induction e with
  | op o a ih =>
    change (liftFsExpr a).cost + (atomicFsOps ℓ Pt C encT).cost o =
      a.cost + (atomicFsOps ℓ Pt C encT).cost o
    rw [ih]
  | _ => simp [liftFsExpr, Expr.cost, *]

theorem liftBaseSamp_cost {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    (s : UniformSamplerTag ReductionDsl.AtomicBaseUnif)
    (e : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ
      ((ReductionDsl.atomicBaseSamplers ℓ Pt).sDom s)) :
    (liftBaseSamp s e).cost = e.cost + (ReductionDsl.atomicBaseSamplers ℓ Pt).sCost s := by
  rcases s with _ | _ | (_ | _ | _) <;> rfl

theorem liftBaseSamp_queries {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    (s : UniformSamplerTag ReductionDsl.AtomicBaseUnif)
    (e : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ
      ((ReductionDsl.atomicBaseSamplers ℓ Pt).sDom s))
    (wT : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (liftBaseSamp s e).queries wT (fun _ => 0) = 0 := by
  rcases s with _ | _ | (_ | _ | _) <;> rfl

theorem liftFsCoinComp_cost {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp (atomicFsOps ℓ Pt C encT) (coinOnlyBaseIface ℓ Pt) Γ t) :
    (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) c).cost = c.cost := by
  induction c with
  | query g _ => nomatch g
  | sample s e =>
    dsimp only [liftFsCoinComp]
    rw [liftBaseSamp_cost, liftFsExpr_cost]
    rfl
  | _ => simp [liftFsCoinComp, liftFsExpr_cost, Comp.cost, *]

theorem liftFsCoinComp_queries {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp (atomicFsOps ℓ Pt C encT) (coinOnlyBaseIface ℓ Pt) Γ t)
    (wT : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) c).queries wT (fun _ => 0) = 0 := by
  induction c with
  | query g _ => nomatch g
  | sample s e => exact liftBaseSamp_queries s _ wT
  | _ => simp [liftFsCoinComp, Comp.queries, *]

theorem liftFsSlotComp_cost {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c).cost = c.cost := by
  induction c <;> simp [liftFsSlotComp, liftFsExpr_cost, Comp.cost, *]

theorem liftFsSlotComp_queries {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t)
    (wT : (slotOtccaTargetIface ℓ Pt).Tag → ℕ)
    (wS : (slotOtccaTargetIface ℓ Pt).smp.Samp → ℕ) :
    (liftFsSlotComp (Dh := Dh) (encPt := encPt) (lam := lam) c).queries wT wS = c.queries wT wS := by
  induction c <;> simp [liftFsSlotComp, Comp.queries, *]

theorem liftNoQuerySlotComp_cost {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)}
    (dflt : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [] (.opt wireSaltCtT))
    (dfltM : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [] (.opt PlainT))
    (hd : dflt.cost = 1) (hdM : dfltM.cost = 1)
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t) :
    (liftNoQuerySlotComp dflt dfltM c).cost ≤ c.cost := by
  induction c with
  | ret e => simp [liftNoQuerySlotComp, liftFsExpr_cost, Comp.cost]
  | bind _ _ ih1 ih2 => simp only [liftNoQuerySlotComp, Comp.cost]; omega
  | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    have hm := max_le_max ih1 ih2
    simp only [liftNoQuerySlotComp, liftFsExpr_cost, Comp.cost]; omega
  | sample s e =>
    dsimp only [liftNoQuerySlotComp]
    rw [liftBaseSamp_cost, liftFsExpr_cost]
    exact le_rfl
  | query g e =>
    have he1 := CryptoVerification.E2E.Costed.Expr.one_le_cost e
    cases g <;> simp only [liftNoQuerySlotComp, Comp.cost, Expr.renameM_cost, hd, hdM] <;> omega
  | iter n e _ ih =>
    have hm := Nat.mul_le_mul_left n (Nat.add_le_add_right ih 1)
    simp only [liftNoQuerySlotComp, liftFsExpr_cost, Comp.cost]; omega
  | findM K l _ ih | anyM K l _ ih | mapM K l _ ih =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ih 1)
    simp only [liftNoQuerySlotComp, liftFsExpr_cost, Comp.cost]; omega
  | consumeFirstM K l _ mk ih =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right (Nat.add_le_add_right ih mk.cost) 1)
    simp only [liftNoQuerySlotComp, liftFsExpr_cost, Comp.cost]; omega
  | foldM K l z _ ih =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ih 1)
    simp only [liftNoQuerySlotComp, liftFsExpr_cost, Comp.cost]; omega

theorem liftNoQuerySlotComp_queries {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)}
    (dflt : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [] (.opt wireSaltCtT))
    (dfltM : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) [] (.opt PlainT))
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt) Γ t)
    (wT : (fsaeadHeaderIface ℓ Pt).Tag → ℕ) :
    (liftNoQuerySlotComp dflt dfltM c).queries wT (fun _ => 0) = 0 := by
  induction c with
  | sample s _ => exact liftBaseSamp_queries s _ wT
  | query g _ => cases g <;> rfl
  | _ => simp [liftNoQuerySlotComp, Comp.queries, *]



theorem liftFsExpr_eval {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)}
    (e : Expr (atomicFsOps ℓ Pt C encT) Γ t) (ρ : Env Γ) :
    (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam) e).eval ρ = e.eval ρ := by
  induction e with
  | var v => rfl
  | unit => rfl
  | bool b => rfl
  | nat n => rfl
  | add a b iha ihb => simp [liftFsExpr, Expr.eval, iha, ihb]
  | sub a b iha ihb => simp [liftFsExpr, Expr.eval, iha, ihb]
  | mulK k a iha => simp [liftFsExpr, Expr.eval, iha]
  | divK k a iha => simp [liftFsExpr, Expr.eval, iha]
  | modK k a iha => simp [liftFsExpr, Expr.eval, iha]
  | lt a b iha ihb => simp [liftFsExpr, Expr.eval, iha, ihb]
  | eqN a b iha ihb => simp [liftFsExpr, Expr.eval, iha, ihb]
  | not a iha => simp [liftFsExpr, Expr.eval, iha]
  | and a b iha ihb => simp [liftFsExpr, Expr.eval, iha, ihb]
  | ite c a b ihc iha ihb =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihc ρ, iha ρ, ihb ρ]
  | pair a b iha ihb => simp [liftFsExpr, Expr.eval, iha, ihb]
  | fst a iha => simp [liftFsExpr, Expr.eval, iha]
  | snd a iha => simp [liftFsExpr, Expr.eval, iha]
  | inl a iha => simp [liftFsExpr, Expr.eval, iha]
  | inr a iha => simp [liftFsExpr, Expr.eval, iha]
  | none => rfl
  | some a iha => simp [liftFsExpr, Expr.eval, iha]
  | caseOpt e n s ihe ihn ihs =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihe ρ]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihe ihl ihr =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihe ρ]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | letE e b ihe ihb =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihe ρ]; exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha =>
    exact congrArg ((atomicFsOps ℓ Pt C encT).eval o) (iha ρ)
  | nil => rfl
  | cons x l ihx ihl => simp [liftFsExpr, Expr.eval, ihx, ihl]
  | len l ihl => simp [liftFsExpr, Expr.eval, ihl]
  | take n l ihn ihl => simp [liftFsExpr, Expr.eval, ihn, ihl]
  | appendL K a b iha ihb => simp [liftFsExpr, Expr.eval, iha, ihb]
  | findB K l p ihl ihp =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihl ρ]
    congr 1; funext x; exact ihp (.cons x ρ)
  | anyB K l p ihl ihp =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihl ρ]
    congr 1; funext x; exact ihp (.cons x ρ)
  | mapB K l f ihl ihf =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihl ρ]
    congr 1; funext x; exact ihf (.cons x ρ)
  | foldrB K l z f ihl ihz ihf =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihl ρ, ihz ρ]
    congr 2; funext x acc; exact ihf (.cons x (.cons acc ρ))
  | tconst a iha =>
    dsimp only [liftFsExpr, Expr.eval]; funext i; exact iha ρ
  | tget m i ihm ihi =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihm ρ, ihi ρ]
  | tset m i a ihm ihi iha =>
    dsimp only [liftFsExpr, Expr.eval]; rw [ihm ρ, ihi ρ, iha ρ]

theorem coinOnlyBaseIface_liftP {ℓ : ℕ} {Pt : Type} {α : Type} (p : ProbComp α) :
    (coinOnlyBaseIface ℓ Pt).liftP p = p := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind n mx ih =>
    simp only [ReductionDsl.Iface.liftP, simulateQ_query_bind] at ih ⊢
    exact bind_congr ih

theorem liftBaseSamp_eval {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    (s : UniformSamplerTag ReductionDsl.AtomicBaseUnif)
    (e : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ
      ((ReductionDsl.atomicBaseSamplers ℓ Pt).sDom s))
    (ρ : Env Γ) :
    (liftBaseSamp s e).eval ρ =
      (fsaeadHeaderIface ℓ Pt).liftP
        ((ReductionDsl.atomicBaseSamplers ℓ Pt).samp s (e.eval ρ)) := by
  rcases s with _ | N | (_ | _ | _) <;> rfl

theorem iterM_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α : Type} (f : α → ProbComp α) :
    ∀ (n : ℕ) (a : α),
      ReductionDsl.iterM (fun x => I.liftP (f x)) n a =
        I.liftP (ReductionDsl.iterM f n a)
  | 0, a => rfl
  | n + 1, a => by
    simp only [ReductionDsl.iterM, ReductionDsl.Iface.liftP, simulateQ_bind]
    exact bind_congr fun a' => iterM_liftP I f n a'

theorem findML_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α : Type} (p : α → ProbComp Bool) :
    ∀ (xs : List α),
      ReductionDsl.findML (fun x => I.liftP (p x)) xs =
        I.liftP (ReductionDsl.findML p xs)
  | [] => rfl
  | x :: xs => by
    simp only [ReductionDsl.findML, ReductionDsl.Iface.liftP, simulateQ_bind]
    exact bind_congr fun b => match b with
      | true => rfl
      | false => findML_liftP I p xs

theorem anyML_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α : Type} (p : α → ProbComp Bool) :
    ∀ (xs : List α),
      ReductionDsl.anyML (fun x => I.liftP (p x)) xs =
        I.liftP (ReductionDsl.anyML p xs)
  | [] => rfl
  | x :: xs => by
    simp only [ReductionDsl.anyML, ReductionDsl.Iface.liftP, simulateQ_bind]
    exact bind_congr fun b => match b with
      | true => rfl
      | false => anyML_liftP I p xs

theorem mapML_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α β : Type} (f : α → ProbComp β) :
    ∀ (xs : List α),
      ReductionDsl.mapML (fun x => I.liftP (f x)) xs =
        I.liftP (ReductionDsl.mapML f xs)
  | [] => rfl
  | x :: xs => by
    have ih := mapML_liftP I f xs
    simp only [ReductionDsl.mapML, ReductionDsl.Iface.liftP, simulateQ_bind] at ih ⊢
    refine bind_congr fun y => ?_
    simp only [ih, simulateQ_pure]

theorem consumeFirstML_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α : Type} (p : α → ProbComp Bool) (mk : α → α) :
    ∀ (xs : List α),
      ReductionDsl.consumeFirstML (fun x => I.liftP (p x)) mk xs =
        I.liftP (ReductionDsl.consumeFirstML p mk xs)
  | [] => rfl
  | x :: xs => by
    have ih := consumeFirstML_liftP I p mk xs
    simp only [ReductionDsl.consumeFirstML, ReductionDsl.Iface.liftP,
      simulateQ_bind] at ih ⊢
    refine bind_congr fun b => ?_
    cases b with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, ih, simulateQ_bind, simulateQ_pure]

theorem foldML_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α β : Type} (f : α → β → ProbComp β) :
    ∀ (xs : List α) (b : β),
      ReductionDsl.foldML (fun x acc => I.liftP (f x acc)) b xs =
        I.liftP (ReductionDsl.foldML f b xs)
  | [], _ => rfl
  | x :: xs, b => by
    simp only [ReductionDsl.foldML, ReductionDsl.Iface.liftP, simulateQ_bind]
    exact bind_congr fun b' => foldML_liftP I f xs b'

theorem liftFsCoinComp_eval {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)}
    (c : Comp (atomicFsOps ℓ Pt C encT) (coinOnlyBaseIface ℓ Pt) Γ t) (ρ : Env Γ) :
    (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) c).eval ρ =
      (fsaeadHeaderIface ℓ Pt).liftP (c.eval ρ) := by
  induction c with
  | ret e =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval]; rfl
  | bind c k ihc ihk =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [ihc ρ]
    simp only [ReductionDsl.Iface.liftP, simulateQ_bind]
    exact bind_congr fun x => ihk (.cons x ρ)
  | ite b c d ihc ihd =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval]
    cases b.eval ρ <;> [exact ihd ρ; exact ihc ρ]
  | caseOpt e n s ihn ihs =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | sample s e =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftBaseSamp_eval, liftFsExpr_eval, coinOnlyBaseIface_liftP]
  | query g _ => exact nomatch g
  | iter n e body ihb =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval]
    have hbody : (fun a => (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) body).eval (.cons a ρ)) =
        (fun a => (fsaeadHeaderIface ℓ Pt).liftP (body.eval (.cons a ρ))) :=
      funext fun a => ihb (.cons a ρ)
    rw [hbody]
    exact iterM_liftP (fsaeadHeaderIface ℓ Pt) (fun a => body.eval (.cons a ρ)) n (e.eval ρ)
  | findM K l p ihp =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval]
    have hp : (fun x => (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) p).eval (.cons x ρ)) =
        (fun x => (fsaeadHeaderIface ℓ Pt).liftP (p.eval (.cons x ρ))) :=
      funext fun x => ihp (.cons x ρ)
    rw [hp]
    exact findML_liftP (fsaeadHeaderIface ℓ Pt) (fun x => p.eval (.cons x ρ)) ((l.eval ρ).take K)
  | anyM K l p ihp =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval]
    have hp : (fun x => (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) p).eval (.cons x ρ)) =
        (fun x => (fsaeadHeaderIface ℓ Pt).liftP (p.eval (.cons x ρ))) :=
      funext fun x => ihp (.cons x ρ)
    rw [hp]
    exact anyML_liftP (fsaeadHeaderIface ℓ Pt) (fun x => p.eval (.cons x ρ)) ((l.eval ρ).take K)
  | mapM K l f ihf =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval]
    have hf : (fun x => (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) f).eval (.cons x ρ)) =
        (fun x => (fsaeadHeaderIface ℓ Pt).liftP (f.eval (.cons x ρ))) :=
      funext fun x => ihf (.cons x ρ)
    rw [hf]
    exact mapML_liftP (fsaeadHeaderIface ℓ Pt) (fun x => f.eval (.cons x ρ)) ((l.eval ρ).take K)
  | consumeFirstM K l p mk ihp =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval]
    have hp : (fun x => (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) p).eval (.cons x ρ)) =
        (fun x => (fsaeadHeaderIface ℓ Pt).liftP (p.eval (.cons x ρ))) :=
      funext fun x => ihp (.cons x ρ)
    have hmk : (fun x => (liftFsExpr (Dh := Dh) (encPt := encPt) (lam := lam) mk).eval (.cons x ρ)) =
        (fun x => mk.eval (.cons x ρ)) :=
      funext fun x => liftFsExpr_eval mk (.cons x ρ)
    rw [hp, hmk]
    exact consumeFirstML_liftP (fsaeadHeaderIface ℓ Pt) (fun x => p.eval (.cons x ρ))
      (fun x => mk.eval (.cons x ρ)) ((l.eval ρ).take K)
  | foldM K l z f ihf =>
    dsimp only [liftFsCoinComp, Comp.eval]
    rw [liftFsExpr_eval, liftFsExpr_eval]
    have hf : (fun x acc => (liftFsCoinComp (Dh := Dh) (encPt := encPt) (lam := lam) f).eval (.cons x (.cons acc ρ))) =
        (fun x acc => (fsaeadHeaderIface ℓ Pt).liftP (f.eval (.cons x (.cons acc ρ)))) :=
      funext fun x => funext fun acc => ihf (.cons x (.cons acc ρ))
    rw [hf]
    exact foldML_liftP (fsaeadHeaderIface ℓ Pt) (fun x acc => f.eval (.cons x (.cons acc ρ)))
      ((l.eval ρ).take K) (z.eval ρ)


/-! ### `CoinSimEquiv` + `Iface.liftP` monadic combinators -/

theorem coinSimEquiv_liftP_pure {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α : Type} (a : α) :
    CoinSimEquiv I.fwdU (pure a) (I.liftP (pure a)) :=
  CoinSimEquiv.of_eq (by simp [Iface.liftP])

theorem coinSimEquiv_liftP_map {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α β : Type} (f : α → β) {oa : OracleComp T α} {q : ProbComp α}
    (h : CoinSimEquiv I.fwdU oa (I.liftP q)) :
    CoinSimEquiv I.fwdU (f <$> oa) (I.liftP (f <$> q)) :=
  (h.map f).trans (CoinSimEquiv.of_eq (by simp [Iface.liftP, simulateQ_map]))

theorem coinSimEquiv_liftP_bind_of_support {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α β : Type} {oa : OracleComp T α} {q : ProbComp α}
    {k₁ : α → OracleComp T β} {k₂ : α → ProbComp β}
    (hoa : CoinSimEquiv I.fwdU oa (I.liftP q))
    (hk : ∀ a ∈ support q, CoinSimEquiv I.fwdU (k₁ a) (I.liftP (k₂ a))) :
    CoinSimEquiv I.fwdU (oa >>= k₁) (I.liftP (q >>= k₂)) := by
  have hmid : CoinSimEquiv I.fwdU (I.liftP q >>= k₁) (I.liftP q >>= fun a => I.liftP (k₂ a)) := by
    refine ⟨fun {σ} impl himpl s => ?_⟩
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
    have hL : ((simulateQ impl (I.liftP q)).run s >>=
        fun z => (simulateQ impl (k₁ z.1)).run z.2) =ᵈ
        (q >>= fun a => (simulateQ impl (k₁ a)).run s) := by
      refine ((Computational.Proofs.ReductionDsl.FsAtomicMacros.evalDistEq_simulateQ_liftP
        I impl himpl q s).bind fun _ => EvalDistEq.rfl).trans ?_
      simp only [bind_assoc, pure_bind]
      exact EvalDistEq.rfl
    have hR : ((simulateQ impl (I.liftP q)).run s >>=
        fun z => (simulateQ impl (I.liftP (k₂ z.1))).run z.2) =ᵈ
        (q >>= fun a => (simulateQ impl (I.liftP (k₂ a))).run s) := by
      refine ((Computational.Proofs.ReductionDsl.FsAtomicMacros.evalDistEq_simulateQ_liftP
        I impl himpl q s).bind fun _ => EvalDistEq.rfl).trans ?_
      simp only [bind_assoc, pure_bind]
      exact EvalDistEq.rfl
    have hM : (q >>= fun a => (simulateQ impl (k₁ a)).run s) =ᵈ
        (q >>= fun a => (simulateQ impl (I.liftP (k₂ a))).run s) :=
      Computational.Proofs.GameHop.Rnd.evalDistEq_bind_right_of_mem_support q
        fun a ha => (hk a ha).run_eq impl himpl s
    exact hL.trans (hM.trans hR.symm)
  exact ((hoa.bind fun a => CoinSimEquiv.refl (k₁ a)).trans hmid).trans
    (CoinSimEquiv.of_eq (by simp [Iface.liftP, simulateQ_bind]))

theorem coinSimEquiv_liftP_map_bind_of_support {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α α' β : Type} (f : α → α')
    {oa : OracleComp T α'} {q : ProbComp α}
    {k₁ : α' → OracleComp T β} {k₂ : α → ProbComp β}
    (hoa : CoinSimEquiv I.fwdU oa (I.liftP (f <$> q)))
    (hk : ∀ a ∈ support q, CoinSimEquiv I.fwdU (k₁ (f a)) (I.liftP (k₂ a))) :
    CoinSimEquiv I.fwdU (oa >>= k₁) (I.liftP (q >>= k₂)) := by
  have hmid : CoinSimEquiv I.fwdU (I.liftP (f <$> q) >>= k₁)
      (I.liftP (q >>= k₂)) := by
    refine ⟨fun {σ} impl himpl s => ?_⟩
    rw [simulateQ_bind, StateT.run_bind]
    have hL : ((simulateQ impl (I.liftP (f <$> q))).run s >>=
        fun z => (simulateQ impl (k₁ z.1)).run z.2) =ᵈ
        (q >>= fun a => (simulateQ impl (k₁ (f a))).run s) := by
      refine ((Computational.Proofs.ReductionDsl.FsAtomicMacros.evalDistEq_simulateQ_liftP
        I impl himpl (f <$> q) s).bind fun _ => EvalDistEq.rfl).trans ?_
      simp only [bind_map_left, bind_assoc, pure_bind]
      exact EvalDistEq.rfl
    have hR : (simulateQ impl (I.liftP (q >>= k₂))).run s =ᵈ
        (q >>= fun a => (simulateQ impl (I.liftP (k₂ a))).run s) := by
      have h1 : I.liftP (q >>= k₂) = (I.liftP q >>= fun a => I.liftP (k₂ a)) := by
        simp [Iface.liftP, simulateQ_bind]
      rw [h1, simulateQ_bind, StateT.run_bind]
      refine ((Computational.Proofs.ReductionDsl.FsAtomicMacros.evalDistEq_simulateQ_liftP
        I impl himpl q s).bind fun _ => EvalDistEq.rfl).trans ?_
      simp only [bind_assoc, pure_bind]
      exact EvalDistEq.rfl
    have hM : (q >>= fun a => (simulateQ impl (k₁ (f a))).run s) =ᵈ
        (q >>= fun a => (simulateQ impl (I.liftP (k₂ a))).run s) :=
      Computational.Proofs.GameHop.Rnd.evalDistEq_bind_right_of_mem_support q
        fun a ha => (hk a ha).run_eq impl himpl s
    exact hL.trans (hM.trans hR.symm)
  exact (hoa.bind fun a' => CoinSimEquiv.refl (k₁ a')).trans hmid

/-! ## 5. One-Stage Real (`fsImpl`) and Slot (`fsSlotImpl`) Session Handlers -/

section RouterDSL

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

local notation "SigA" => (atomicSig ℓ Pt)
local notation "OpsF" => (atomicFig8Ops ℓ Pt C Dh encPt encT lam)
local notation "IfaceF" => (fsaeadHeaderIface ℓ Pt)

abbrev hybSessStTy : Ty SigA :=
  mapTy (hybBaseTy (Pt := Pt) (ℓ := ℓ))
    (CryptoGames.FSAEAD.Thm5.Costed.stTy
      (CK := BitVec 256) (MK := BitVec 256)
      (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt))

abbrev saltSlotStAtomTy : Ty SigA :=
  mapTy (swBaseTy (Pt := Pt) (ℓ := ℓ))
    (CryptoGames.Ratchet.LibsignalInst.Costed.saltSlotStTy (Pt := Pt) ℓ)

/-- Initial `hybSessStTy` expression `(initHSE b, .inl ())` from coin `b : .bool` (`v0`). -/
@[expose] def initHybSessStExpr : Expr OpsF [.bool] (hybSessStTy ℓ Pt) :=
  liftFsExpr
    (compilePureExpr (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
      (Γ := [.bool])
      (.pair
        (CryptoGames.FSAEAD.Thm5.Costed.initHSE
          (CK := BitVec 256) (MK := BitVec 256)
          (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt) (.var .zero))
        (.inl .unit)))

/-- Empty `SaltSlotSt Pt` expression `(none, [])` in `atomicSig ℓ Pt`. -/
@[expose] def emptySaltSlotAtomExpr {Γ : List (Ty SigA)} :
    Expr OpsF Γ (saltSlotStAtomTy ℓ Pt) :=
  .pair .none .nil

/-- One-stage `fsImpl` handler in `HybridCosted` compiled to `OpsF` and `IfaceF`.
Note: multi-session FS-AEAD reductions never issue `corruptReceiver` (`hNoCr` bound `0`), so
`realCrStep` returns `(none, s)` directly. -/
@[expose] def realTrStep (jPos mSlot : ℕ) :
    Comp OpsF IfaceF [.prod fig8PubAdT PlainT, hybSessStTy ℓ Pt]
      (.prod (.opt lctT) (hybSessStTy ℓ Pt)) :=
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
  let sIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ _ Δ _ := fun a =>
    Comp.sample (I := I₀.withSamp _) (Sum.inl (Sum.inr ())) a
  let src : Comp _ (I₀.withSamp _)
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.transmitBody ae G 1 1
        maxForwardJumps jPos mSlot sIdeal (some (fun x => sIdeal (.fst x))))
  liftFsCoinComp (compilePureComp (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) src)

@[expose] def realChStep (jPos mSlot : ℕ) :
    Comp OpsF IfaceF [.prod fig8PubAdT (.prod PlainT PlainT), hybSessStTy ℓ Pt]
      (.prod (.opt lctT) (hybSessStTy ℓ Pt)) :=
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
  let sIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ _ Δ _ := fun a =>
    Comp.sample (I := I₀.withSamp _) (Sum.inl (Sum.inr ())) a
  let src : Comp _ (I₀.withSamp _)
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod (CryptoGames.FSAEAD.Costed.bt .msg) (CryptoGames.FSAEAD.Costed.bt .msg)),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.challengeBody ae G 1 1
        maxForwardJumps jPos mSlot sIdeal (some (fun x => sIdeal (.fst x))))
  liftFsCoinComp (compilePureComp (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) src)

@[expose] def realCsStep (qSim : ℕ) (la : Bool) :
    Comp OpsF IfaceF [.unit, hybSessStTy ℓ Pt]
      (.prod (.opt fsSendStT) (hybSessStTy ℓ Pt)) :=
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
  let src : Comp _ (I₀.withSamp _)
      [.unit, CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt CryptoGames.FSAEAD.Costed.rssTy) CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.var (.succ .zero)))
      (CryptoGames.FSAEAD.Thm5.Costed.corruptSenderBody (I₀ := I₀) ae G 1 1 qSim la)
  liftFsCoinComp (compilePureComp (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) src)

@[expose] def realCrStep :
    Comp OpsF IfaceF [.unit, hybSessStTy ℓ Pt]
      (.prod (.opt (.prod fsSendStT fsRecvStT)) (hybSessStTy ℓ Pt)) :=
  .ret (.pair .none (.var (.succ .zero)))

@[expose] def realDlStep (qSim jPos mSlot : ℕ) (la : Bool) :
    Comp OpsF IfaceF [.prod fig8PubAdT lctT, hybSessStTy ℓ Pt]
      (.prod (.opt (fsRrT PlainT)) (hybSessStTy ℓ Pt)) :=
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
  let src : Comp _ (I₀.withSamp _)
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim jPos mSlot la (some (fun _ => .ret .none)))
  liftFsCoinComp (compilePureComp (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) src)

@[expose] def realIjStep (qSim jPos mSlot : ℕ) (la : Bool) :
    Comp OpsF IfaceF [.prod fig8PubAdT lctT, hybSessStTy ℓ Pt]
      (.prod (.opt (fsRrT PlainT)) (hybSessStTy ℓ Pt)) :=
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
  let src : Comp _ (I₀.withSamp _)
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim jPos mSlot la (some (fun _ => .ret .none)))
  liftFsCoinComp (compilePureComp (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) src)

/-- Slot-side `OTCCATag` handler on `saltTbl : .tbl saltSlotStAtomTy` (`slotLift (slotSaltImpl{,NF} false)`). -/
@[expose] def slotOtccaImpl (nf : Bool) (qSim : ℕ) :
    (g : OTCCATag) →
      Comp OpsF IfaceF
        [(slotOtccaTargetIface ℓ Pt).dom g, .tbl (saltSlotStAtomTy ℓ Pt)]
        (.prod ((slotOtccaTargetIface ℓ Pt).cod g) (.tbl (saltSlotStAtomTy ℓ Pt)))
  | .enc =>
    let encStep := liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam)
      .none .none
      (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltEncC (Γ := [])
          C clampedProtoSignalCodec ℓ encT idOf 1 1 false qSim))
    -- v0 : .prod slotAdT PlainT (`((slotIdx, ad), m)`), v1 : .tbl saltSlotStAtomTy
    .bind (.ret (.tget (.var (.succ .zero)) (.fst (.fst (.var .zero)))))
      (.bind
        (encStep.renameM renId2)
        (.ret (.pair (.fst (.var .zero))
          (.tset (.var (.succ (.succ (.succ .zero))))
            (.fst (.fst (.var (.succ (.succ .zero)))))
            (.snd (.var .zero))))))
  | .dec =>
    let decStep := liftNoQuerySlotComp (Pt := Pt) (Dh := Dh) (encPt := encPt) (lam := lam)
      .none .none
      (compilePureComp (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
        (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltDecC (Γ := [])
          C clampedProtoSignalCodec ℓ encT idOf 1 1 nf false qSim))
    -- v0 : .prod slotAdT wireSaltCtT (`((slotIdx, ad), e)`), v1 : .tbl saltSlotStAtomTy
    .bind (.ret (.tget (.var (.succ .zero)) (.fst (.fst (.var .zero)))))
      (.bind
        (decStep.renameM renId2)
        (.ret (.pair (.fst (.var .zero))
          (.tset (.var (.succ (.succ (.succ .zero))))
            (.fst (.fst (.var (.succ (.succ .zero)))))
            (.snd (.var .zero))))))

abbrev slotSessStTy : Ty SigA :=
  .prod (hybSessStTy ℓ Pt) (.tbl (saltSlotStAtomTy ℓ Pt))

@[expose] def liftSlotHybStep {qTy rTy : Ty SigA} (nf : Bool) (qSim : ℕ)
    (c : Comp (atomicFsOps ℓ Pt C encT) (slotOtccaTargetIface ℓ Pt)
      [qTy, hybSessStTy ℓ Pt] (.prod rTy (hybSessStTy ℓ Pt))) :
    Comp OpsF IfaceF [qTy, slotSessStTy ℓ Pt] (.prod rTy (slotSessStTy ℓ Pt)) :=
  -- v0 : qTy, v1 : (hybSt, saltTbl)
  .bind
    (substQueryComp
      (I₁ := slotOtccaTargetIface ℓ Pt) (I₂ := IfaceF)
      (fun s {_} e => liftBaseSamp s e)
      (slotOtccaImpl ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim)
      envSwapFst2
      (.snd (.var (.succ .zero)))
      (liftFsSlotComp c))
    (.ret (.pair (.fst (.fst (.var .zero)))
      (.pair (.snd (.fst (.var .zero))) (.snd (.var .zero)))))

@[expose] def slotTrStep (nf : Bool) (qSim N : ℕ) :
    Comp OpsF IfaceF [.prod fig8PubAdT PlainT, slotSessStTy ℓ Pt]
      (.prod (.opt lctT) (slotSessStTy ℓ Pt)) :=
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := CryptoGames.OTCCA.Costed.otccaIface
    (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1
  let sIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ _ Δ _ := fun a =>
    Comp.sample (I := I₀.withSamp _) (Sum.inl ()) a
  let sEnc : ∀ {Δ},
      Expr _ Δ (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .msg)) →
      Comp _ (I₀.withSamp _) Δ (CryptoGames.FSAEAD.Costed.bt .ct) := fun iam =>
    .bind (Comp.query (I := I₀.withSamp _) CryptoGames.OTCCA.Costed.OtccaTag.enc iam)
      (.caseOpt (.var .zero) (sIdeal (.fst (exprWk1 iam))) (.ret (.var .zero)))
  let src : Comp _ (I₀.withSamp _)
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad) (CryptoGames.FSAEAD.Costed.bt .msg),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.transmitBody ae G 1 1
        maxForwardJumps N N sIdeal (some sEnc))
  liftSlotHybStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim
    (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src)

@[expose] def slotChStep (nf : Bool) (qSim N : ℕ) :
    Comp OpsF IfaceF [.prod fig8PubAdT (.prod PlainT PlainT), slotSessStTy ℓ Pt]
      (.prod (.opt lctT) (slotSessStTy ℓ Pt)) :=
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := CryptoGames.OTCCA.Costed.otccaIface
    (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1
  let sIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ _ Δ _ := fun a =>
    Comp.sample (I := I₀.withSamp _) (Sum.inl ()) a
  let sEnc : ∀ {Δ},
      Expr _ Δ (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .msg)) →
      Comp _ (I₀.withSamp _) Δ (CryptoGames.FSAEAD.Costed.bt .ct) := fun iam =>
    .bind (Comp.query (I := I₀.withSamp _) CryptoGames.OTCCA.Costed.OtccaTag.enc iam)
      (.caseOpt (.var .zero) (sIdeal (.fst (exprWk1 iam))) (.ret (.var .zero)))
  let src : Comp _ (I₀.withSamp _)
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod (CryptoGames.FSAEAD.Costed.bt .msg) (CryptoGames.FSAEAD.Costed.bt .msg)),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.challengeBody ae G 1 1
        maxForwardJumps N N sIdeal (some sEnc))
  liftSlotHybStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim
    (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src)

@[expose] def slotCsStep (qSim : ℕ) (la : Bool) :
    Comp OpsF IfaceF [.unit, slotSessStTy ℓ Pt]
      (.prod (.opt fsSendStT) (slotSessStTy ℓ Pt)) :=
  .bind (.ret (.fst (.var (.succ .zero))))
    (.bind
      ((realCsStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) qSim la).renameM renSwap2)
      (.ret (.pair (.fst (.var .zero))
        (.pair (.snd (.var .zero)) (.snd (.var (.succ (.succ (.succ .zero)))))))))

@[expose] def slotCrStep :
    Comp OpsF IfaceF [.unit, slotSessStTy ℓ Pt]
      (.prod (.opt (.prod fsSendStT fsRecvStT)) (slotSessStTy ℓ Pt)) :=
  .ret (.pair .none (.var (.succ .zero)))

@[expose] def slotDlStep (nf : Bool) (qSim N : ℕ) (la : Bool) :
    Comp OpsF IfaceF [.prod fig8PubAdT lctT, slotSessStTy ℓ Pt]
      (.prod (.opt (fsRrT PlainT)) (slotSessStTy ℓ Pt)) :=
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := CryptoGames.OTCCA.Costed.otccaIface
    (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1
  let sDec : ∀ {Δ},
      Expr _ Δ (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .ct)) →
      Comp _ (I₀.withSamp _) Δ (.opt (CryptoGames.FSAEAD.Costed.bt .msg)) := fun iae =>
    Comp.query (I := I₀.withSamp _) CryptoGames.OTCCA.Costed.OtccaTag.dec iae
  let src : Comp _ (I₀.withSamp _)
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.deliverBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim N N la (some sDec))
  liftSlotHybStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim
    (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src)

@[expose] def slotIjStep (nf : Bool) (qSim N : ℕ) (la : Bool) :
    Comp OpsF IfaceF [.prod fig8PubAdT lctT, slotSessStTy ℓ Pt]
      (.prod (.opt (fsRrT PlainT)) (slotSessStTy ℓ Pt)) :=
  let ae := lAeadR C clampedProtoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  let ideal := lIdeal C clampedProtoSignalCodec ℓ encT
  let I₀ := CryptoGames.OTCCA.Costed.otccaIface
    (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
    (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
    (CryptoGames.FSAEAD.Costed.bt .msg)
    (CryptoGames.FSAEAD.Costed.bt .ct) ideal 1
  let sDec : ∀ {Δ},
      Expr _ Δ (.prod (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .ct)) →
      Comp _ (I₀.withSamp _) Δ (.opt (CryptoGames.FSAEAD.Costed.bt .msg)) := fun iae =>
    Comp.query (I := I₀.withSamp _) CryptoGames.OTCCA.Costed.OtccaTag.dec iae
  let src : Comp _ (I₀.withSamp _)
      [.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (.prod .nat (CryptoGames.FSAEAD.Costed.bt .ct)),
       CryptoGames.FSAEAD.Thm5.Costed.stTy]
      (.prod (.opt (CryptoGames.FSAEAD.Costed.rrTy (CryptoGames.FSAEAD.Costed.bt .msg)))
        CryptoGames.FSAEAD.Thm5.Costed.stTy) :=
    .bind (.ret (.pair (.var .zero) (.var (.succ .zero))))
      (CryptoGames.FSAEAD.Thm5.Costed.injectBody (I₀ := I₀) ae G 1 1
        maxForwardJumps qSim N N la (some sDec))
  liftSlotHybStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) nf qSim
    (compilePureComp (multiMacroBundle (Pt := Pt) C ℓ encT idOf) src)

/-! ### Lazy per-session `pubRedImpl` + `fsImpl` / `fsSlotImpl` wrappers and router state -/

abbrev realEntryTy : Ty SigA := .prod .bool (.opt (hybSessStTy ℓ Pt))
abbrev slotEntryTy : Ty SigA := .prod .bool (.opt (slotSessStTy ℓ Pt))
abbrev routerStTy : Ty SigA := .prod (.tbl (realEntryTy ℓ Pt)) (.tbl (slotEntryTy ℓ Pt))

@[expose] def initRouterStExpr {Γ : List (Ty SigA)} : Expr OpsF Γ (routerStTy ℓ Pt) :=
  .pair (.tconst (.pair (.bool false) .none)) (.tconst (.pair (.bool false) .none))

/-- Ensure `optSt : .opt sTy` (`v0`) is initialized, using `mkInit : Comp OpsF IfaceF [] sTy`. -/
@[expose] def ensureSessInit {sTy : Ty SigA} (mkInit : Comp OpsF IfaceF [] sTy) :
    Comp OpsF IfaceF [.opt sTy] sTy :=
  .caseOpt (.var .zero)
    (mkInit.renameM renEmpty)
    (.ret (.var .zero))

@[expose] def initRealSessComp : Comp OpsF IfaceF [] (hybSessStTy ℓ Pt) :=
  .bind (Comp.sample (O := OpsF) (I := IfaceF) UniformSamplerTag.bool .unit)
    (.ret (initHybSessStExpr ℓ Pt C Dh encPt encT idOf lam))

@[expose] def initSlotSessComp : Comp OpsF IfaceF [] (slotSessStTy ℓ Pt) :=
  .bind (Comp.sample (O := OpsF) (I := IfaceF) UniformSamplerTag.bool .unit)
    (.ret (.pair (initHybSessStExpr ℓ Pt C Dh encPt encT idOf lam)
      (.tconst (emptySaltSlotAtomExpr ℓ Pt C Dh encPt encT lam))))

/-- Map `optRrE : .opt (fsRrT PlainT)` with `pubE : lpubT` via `pubRedImpl`'s `withPub`. -/
@[expose] def mapRrWithPubExpr {Γ : List (Ty SigA)}
    (optRrE : Expr OpsF Γ (.opt (fsRrT PlainT)))
    (pubE : Expr OpsF Γ lpubT) :
    Expr OpsF Γ (.opt (fsRrT (.prod lpubT PlainT))) :=
  .caseOpt optRrE .none
    (.some
      (.caseSum (.var .zero) (.inl .unit)
        (.inr (.pair (.fst (.var .zero))
          (.caseOpt (.snd (.var .zero)) .none
            (.some (.pair (exprWk1 (exprWk1 (exprWk1 pubE))) (.var .zero))))))))

/-- Run one `pubRedImpl` + lazy session step on a single-session entry `(ended, optS) : .prod .bool (.opt sTy)`. -/
@[expose] def runLazyPubSess {sTy : Ty SigA}
    (mkInit : Comp OpsF IfaceF [] sTy)
    (trS : Comp OpsF IfaceF [.prod fig8PubAdT PlainT, sTy] (.prod (.opt lctT) sTy))
    (chS : Comp OpsF IfaceF [.prod fig8PubAdT (.prod PlainT PlainT), sTy] (.prod (.opt lctT) sTy))
    (csS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt fsSendStT) sTy))
    (crS : Comp OpsF IfaceF [.unit, sTy] (.prod (.opt (.prod fsSendStT fsRecvStT)) sTy))
    (dlS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy))
    (ijS : Comp OpsF IfaceF [.prod fig8PubAdT lctT, sTy] (.prod (.opt (fsRrT PlainT)) sTy)) :
    (g : FSAEADTag) →
      Comp OpsF IfaceF
        [(IfaceF).dom g, .prod .bool (.opt sTy)]
        (.prod ((IfaceF).cod g) (.prod .bool (.opt sTy)))
  | .tr =>
    -- v0 = (hdr, (pub, m)), v1 = (ended, optS)
    .bind (.ret (.snd (.var (.succ .zero))))
      (.bind ((ensureSessInit ℓ Pt C Dh encPt encT lam mkInit).renameM renId1)
        (.bind (.ret (.pair (.pair (.fst (.var (.succ (.succ .zero))))
            (.fst (.snd (.var (.succ (.succ .zero))))))
            (.snd (.snd (.var (.succ (.succ .zero)))))))
          (.bind
            (trS.renameM renId2)
            (.ret (.pair (.fst (.var .zero))
              (.pair (.fst (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
                (.some (.snd (.var .zero)))))))))
  | .ch =>
    -- v0 = (hdr, ((pub0, m0), (pub1, m1))), v1 = (ended, optS)
    .bind (.ret (.snd (.var (.succ .zero))))
      (.bind ((ensureSessInit ℓ Pt C Dh encPt encT lam mkInit).renameM renId1)
        (.bind (.ret (.pair (.pair (.fst (.var (.succ (.succ .zero))))
            (.fst (.fst (.snd (.var (.succ (.succ .zero)))))))
            (.pair (.snd (.fst (.snd (.var (.succ (.succ .zero))))))
              (.snd (.snd (.snd (.var (.succ (.succ .zero)))))))))
          (.bind
            (chS.renameM renId2)
            (.ret (.pair (.fst (.var .zero))
              (.pair (.fst (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
                (.some (.snd (.var .zero)))))))))
  | .cs =>
    .bind (.ret (.snd (.var (.succ .zero))))
      (.bind ((ensureSessInit ℓ Pt C Dh encPt encT lam mkInit).renameM renId1)
        (.bind
          (csS.renameM renUnit2)
          (.ret (.pair (.fst (.var .zero))
            (.pair (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
              (.some (.snd (.var .zero))))))))
  | .cr =>
    .bind (.ret (.snd (.var (.succ .zero))))
      (.bind ((ensureSessInit ℓ Pt C Dh encPt encT lam mkInit).renameM renId1)
        (.bind
          (crS.renameM renUnit2)
          (.ret (.pair (.fst (.var .zero))
            (.pair
              (.caseOpt (.fst (.var .zero))
                (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
                (.bool true))
              (.some (.snd (.var .zero))))))))
  | .dl =>
    -- v0 = (hdr, c), v1 = (ended, optS); first compute lPubOf c.2
    let pubOptE : Expr OpsF [(IfaceF).dom .dl, .prod .bool (.opt sTy)] (.opt lpubT) :=
      liftFsExpr (lPubOfExpr ℓ Pt C encT (.snd (.snd (.var .zero))))
    .caseOpt pubOptE
      (.ret (.pair .none (.var (.succ .zero))))
      -- v0 = pub, v1 = (hdr, c), v2 = (ended, optS)
      (.bind (.ret (.snd (.var (.succ (.succ .zero)))))
        (.bind ((ensureSessInit ℓ Pt C Dh encPt encT lam mkInit).renameM renId1)
          (.bind (.ret (.pair (.pair (.fst (.var (.succ (.succ (.succ .zero)))))
              (.var (.succ (.succ .zero))))
              (.snd (.var (.succ (.succ (.succ .zero)))))))
            (.bind
              (dlS.renameM renId2)
              (.bind (.ret (.fst (.var .zero)))
                -- v0 = optRr, v1 = (optRr, s'), v2 = ad_c, v3 = s0, v4 = optS, v5 = pub, v6 = (hdr, c), v7 = (ended, optS)
                (.ret (.pair
                  (mapRrWithPubExpr ℓ Pt C Dh encPt encT lam
                    (.var .zero)
                    (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
                  (.pair (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                    (.some (.snd (.var (.succ .zero))))))))))))
  | .ij =>
    let pubOptE : Expr OpsF [(IfaceF).dom .ij, .prod .bool (.opt sTy)] (.opt lpubT) :=
      liftFsExpr (lPubOfExpr ℓ Pt C encT (.snd (.snd (.var .zero))))
    .caseOpt pubOptE
      (.ret (.pair
        (.ite (.fst (.var (.succ .zero))) .none (.some (.inl .unit)))
        (.var (.succ .zero))))
      -- v0 = pub, v1 = (hdr, c), v2 = (ended, optS)
      (.bind (.ret (.snd (.var (.succ (.succ .zero)))))
        (.bind ((ensureSessInit ℓ Pt C Dh encPt encT lam mkInit).renameM renId1)
          (.bind (.ret (.pair (.pair (.fst (.var (.succ (.succ (.succ .zero)))))
              (.var (.succ (.succ .zero))))
              (.snd (.var (.succ (.succ (.succ .zero)))))))
            (.bind
              (ijS.renameM renId2)
              (.bind (.ret (.fst (.var .zero)))
                (.ret (.pair
                  (mapRrWithPubExpr ℓ Pt C Dh encPt encT lam
                    (.var .zero)
                    (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
                  (.pair (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                    (.some (.snd (.var (.succ .zero))))))))))))

@[expose] def toFsTag : FSHdrTag → FSAEADTag
  | .tr => .tr
  | .ch => .ch
  | .cs => .cs
  | .cr => .cr
  | .dl => .dl
  | .ij => .ij


/-- Router query handler for `(stage, la : Bool)` and `(j, qR : ℕ)` on `(sIdx, payload)` (`v0`)
and `rSt = (realTbl, slotTbl)` (`v1`):
- `sIdx == j`: forwards `payload` to external `fsaeadHeaderIface ℓ Pt`.
- `stage = false` (`lSessAdv`): `sIdx < j` -> `slotTbl` (`nf = false`), `sIdx > j` -> `realTbl` (`hp 0 0 la`).
- `stage = true` (`lWireSessAdv`): `sIdx < j` -> `realTbl` (`hp N N la`), `sIdx > j` -> `slotTbl` (`nf = true`). -/
@[expose] def routerQueryMacro (stage la : Bool) (j qR : ℕ) (g : FSHdrTag) :
    Comp OpsF IfaceF [.prod .nat ((IfaceF).dom (toFsTag g)), routerStTy ℓ Pt]
      (.prod ((IfaceF).cod (toFsTag g)) (routerStTy ℓ Pt)) :=
  let N := authHopCutoff maxForwardJumps qR la
  let qSim := 2 * qR + 4
  let jPosR := if stage then N else 0
  let mSlotR := if stage then N else 0
  let realStep := runLazyPubSess ℓ Pt C Dh encPt encT lam
    (initRealSessComp ℓ Pt C Dh encPt encT idOf lam)
    (realTrStep ℓ Pt C Dh encPt encT idOf lam jPosR mSlotR)
    (realChStep ℓ Pt C Dh encPt encT idOf lam jPosR mSlotR)
    (realCsStep ℓ Pt C Dh encPt encT idOf lam qSim la)
    (realCrStep ℓ Pt C Dh encPt encT lam)
    (realDlStep ℓ Pt C Dh encPt encT idOf lam qSim jPosR mSlotR la)
    (realIjStep ℓ Pt C Dh encPt encT idOf lam qSim jPosR mSlotR la)
    (toFsTag g)
  let slotStep := runLazyPubSess ℓ Pt C Dh encPt encT lam
    (initSlotSessComp ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam))
    (slotTrStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
    (slotChStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N)
    (slotCsStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) qSim la)
    (slotCrStep ℓ Pt C Dh encPt encT lam)
    (slotDlStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
    (slotIjStep ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage qSim N la)
    (toFsTag g)
  let runRealBranch :
      Comp OpsF IfaceF [.prod .nat ((IfaceF).dom (toFsTag g)), routerStTy ℓ Pt]
        (.prod ((IfaceF).cod (toFsTag g)) (routerStTy ℓ Pt)) :=
    .bind (.ret (.tget (.fst (.var (.succ .zero))) (.fst (.var .zero))))
      (.bind (.ret (.snd (.var (.succ .zero))))
        (.bind
          (realStep.renameM renId2)
          (.ret (.pair (.fst (.var .zero))
            (.pair
              (.tset (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
                (.fst (.var (.succ (.succ (.succ .zero)))))
                (.snd (.var .zero)))
              (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))))))
  let runSlotBranch :
      Comp OpsF IfaceF [.prod .nat ((IfaceF).dom (toFsTag g)), routerStTy ℓ Pt]
        (.prod ((IfaceF).cod (toFsTag g)) (routerStTy ℓ Pt)) :=
    .bind (.ret (.tget (.snd (.var (.succ .zero))) (.fst (.var .zero))))
      (.bind (.ret (.snd (.var (.succ .zero))))
        (.bind
          (slotStep.renameM renId2)
          (.ret (.pair (.fst (.var .zero))
            (.pair
              (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
              (.tset (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
                (.fst (.var (.succ (.succ (.succ .zero)))))
                (.snd (.var .zero))))))))
  .ite (.eqN (.fst (.var .zero)) (.nat j))
    (.bind (Comp.query (O := OpsF) (I := IfaceF) (toFsTag g) (.snd (.var .zero)))
      (.ret (.pair (.var .zero) (.var (.succ (.succ .zero))))))
    (.ite (.lt (.fst (.var .zero)) (.nat j))
      (if stage then runRealBranch else runSlotBranch)
      (if stage then runSlotBranch else runRealBranch))

/-! ### Intermediate Atomic Multi-Session Interface & `PureAuxBundle` -/

@[expose] def fsaeadMultiAtomicIface (qep qR B0 : ℕ) :
    Iface SigA
      (unifSpec + OracleSpec.sigma (fun _ : ℕ => CryptoGames.FSAEAD.spec
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))) where
  fwdU n := query
    (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ => CryptoGames.FSAEAD.spec
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))) (.inl n)
  uCost := 1
  Tag := FSHdrTag
  dom g := .prod .nat ((IfaceF).dom (toFsTag g))
  cod g := (IfaceF).cod (toFsTag g)
  enc g sx := match (IfaceF).enc (toFsTag g) sx.2 with
    | Sum.inl n => Sum.inl n
    | Sum.inr q => Sum.inr ⟨sx.1, q⟩
  dec g sx r :=
    match h : (IfaceF).enc (toFsTag g) sx.2 with
    | Sum.inl _ => (IfaceF).dec (toFsTag g) sx.2 (h.symm ▸ r)
    | Sum.inr _ => (IfaceF).dec (toFsTag g) sx.2 (h.symm ▸ r)
  qCost g := fsMultiQueryC qep qR B0 g / 3
  smp := atomicSamplers ℓ Pt

@[expose] def fsMultiSampMacro (qep qR B0 : ℕ) (sampBV : ProbComp (BitVec 256)) :
    (s : CKASamp) →
      Comp OpsF (fsaeadMultiAtomicIface ℓ Pt qep qR B0)
        [mapTy (fSortCKA ℓ Pt)
          ((CryptoGames.CKA.ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortCKA ℓ Pt)
          ((CryptoGames.CKA.ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sTy s))
  | .bit =>
    Comp.sample (O := OpsF) (I := fsaeadMultiAtomicIface ℓ Pt qep qR B0) UniformSamplerTag.bool .unit
  | .kr | .kc | .ccoins | .k =>
    Comp.sample (O := OpsF) (I := fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (UniformSamplerTag.base AtomicUnifBase.bv256) .unit
  | .i =>
    Comp.sample (O := OpsF) (I := fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (UniformSamplerTag.base AtomicUnifBase.pt) .unit

@[expose] def fsMultiPureAuxBundle (qep qR B0 : ℕ) (sampBV : ProbComp (BitVec 256)) :
    PureAuxBundle
      (prngSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      SigA
      (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      OpsF
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        sampBV sampBV sampBV ($ᵗ Pt) sampBV)
      (fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (.prod IdKey IdKey) where
  fSort := fSortCKA ℓ Pt
  opMacro := ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0
  sampMacro := fsMultiSampMacro ℓ Pt C Dh encPt encT lam qep qR B0 sampBV
  queryMacro
    | .tr => Comp.query (O := OpsF) (I := fsaeadMultiAtomicIface ℓ Pt qep qR B0) FSHdrTag.tr (.var .zero)
    | .ch => Comp.query (O := OpsF) (I := fsaeadMultiAtomicIface ℓ Pt qep qR B0) FSHdrTag.ch (.var .zero)
    | .cs => Comp.query (O := OpsF) (I := fsaeadMultiAtomicIface ℓ Pt qep qR B0) FSHdrTag.cs (.var .zero)
    | .cr => Comp.query (O := OpsF) (I := fsaeadMultiAtomicIface ℓ Pt qep qR B0) FSHdrTag.cr (.var .zero)
    | .dl => Comp.query (O := OpsF) (I := fsaeadMultiAtomicIface ℓ Pt qep qR B0) FSHdrTag.dl (.var .zero)
    | .ij => Comp.query (O := OpsF) (I := fsaeadMultiAtomicIface ℓ Pt qep qR B0) FSHdrTag.ij (.var .zero)

/-! ## 6. Exported Multi-Session to Single-Session Compilers (`compileFsMultiAtomic`, `compileFsMultiDFAtomic`) -/

/-- Compile a multi-session `fsaeadMultiHeaderAdIface` 4-oracle `SM.spec` reduction `R` to an atomic
single-session `fsaeadHeaderIface ℓ Pt` reduction at router `(stage, la, j)` with epoch bound `qep`,
cutoff parameter `qR`, and ratchet skip budget `B0`. -/
@[expose] def compileFsMultiAtomic (stage la : Bool) (j qep qR B0 : ℕ)
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
      .unit .unit .bool .bool) :
    CostedReduction OpsF (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  if ℓ < 10 ^ 6 ∧ j ≤ (qep + 2) * B0 + B0 * B0 ∧ qR ≤ B0 then
    (substQueryRed
      (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (I₂ := IfaceF)
      (initRouterStExpr ℓ Pt C Dh encPt encT lam)
      (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
      (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR)
      (compilePureAuxRed
        (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
        (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R))
  else
    { σ := .unit
      init := .ret (.pair .unit .unit)
      handle := .ret (.pair (.inl .none) .unit)
      finish := .ret (.bool false) }

/-- Compile a multi-session `fsaeadMultiHeaderAdIface` 6-oracle `SM.specDF` reduction `R` to an
atomic single-session `fsaeadHeaderIface ℓ Pt` reduction at router `(stage, la, j)` with epoch bound
`qep`, cutoff parameter `qR`, and ratchet skip budget `B0`. -/
@[expose] def compileFsMultiDFAtomic (stage la : Bool) (j qep qR B0 : ℕ)
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
      .unit .unit .bool .bool) :
    CostedReduction OpsF (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  if ℓ < 10 ^ 6 ∧ j ≤ (qep + 2) * B0 + B0 * B0 ∧ qR ≤ B0 then
    (substQueryRed
      (I₁ := fsaeadMultiAtomicIface ℓ Pt qep qR B0)
      (I₂ := IfaceF)
      (initRouterStExpr ℓ Pt C Dh encPt encT lam)
      (fun s {_} e => Comp.sample (O := OpsF) (I := IfaceF) s e)
      (routerQueryMacro ℓ Pt C Dh encPt encT (idOf := idOf) (lam := lam) stage la j qR)
      (compilePureAuxRed
        (fsMultiPureAuxBundle ℓ Pt C Dh encPt encT idOf lam qep qR B0 ($ᵗ (BitVec 256)))
        (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R))
  else
    { σ := .unit
      init := .ret (.pair .unit .unit)
      handle := .ret (.pair (.inl .none) .unit)
      finish := .ret (.bool false) }


end RouterDSL

end Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase
